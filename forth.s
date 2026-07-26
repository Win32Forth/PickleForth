// ============================================================================
// PickleForth - A Forth kernel for ARM64 (Apple Silicon)
// ============================================================================
// Registers:
//   x20 = TOS  (Top of Data Stack)
//   x19 = IP   (Instruction Pointer)
//   x21 = W    (Working - current dict entry pointer)
//   x22 = DSP  (Data Stack, grows down)
//   x23 = RSP  (Return Stack, grows down)
//   x24 = &latest (pointer to variable holding newest dict entry)
//
// Register discipline (important):
//   VM state lives in x19-x24, which are AAPCS64 callee-saved.
//   Helpers that use them MUST save/restore (see SAVE_VM / RESTORE_VM).
//
//   Darwin ARM64 unix syscalls (svc #0x80): the kernel preserves x1-x28
//   and only returns a result in x0 (and sets NZCV.C on error). So raw
//   syscalls do NOT corrupt the Forth VM registers. The real hazard is
//   assembly helpers that temporarily borrow x19-x24 without saving them.
//
// Dictionary entry format (each entry 8-byte aligned):
//   +0:  link (8 bytes, pointer to previous entry or 0)     >LINK
//   +8:  flags|len (8 bytes, low byte=name length, bit 8=immediate)  >FLAGS
//   +16: code_field (8 bytes, pointer to native code)      >CODE
//   +24: name (padded to 8-byte multiple)                  >NAME
//   after name: body / parameter field                     >BODY
//
// In this system an xt from ' / FIND is the entry address (not the CFA).
// >CODE converts xt to the code-field address;  >CODE @  fetches the code ptr.
//
// NEXT: load dict_entry from *IP, load code_field from entry, jump.
//
// ----------------------------------------------------------------------------
// ANS Forth 2012 compatibility
// ----------------------------------------------------------------------------
// Cell size: 64-bit (8 bytes). Flags: true = -1, false = 0.
//
// CORE (6.1) — word names: complete (all required Core names are present).
// This is NOT a claim of formal ANS System compliance: semantics, environmental
// restrictions, and the Hayes / forth2012-test-suite have not been certified.
// ENVIRONMENT? answers CORE true, CORE-EXT false, FLOORED false.
//
// Core coverage (by area; stack comments intended to match ANS):
//   Stack:    DUP DROP SWAP OVER ROT PICK ?DUP 2DUP 2DROP 2SWAP 2OVER DEPTH
//   Return:   >R R> R@
//   Arith:    + - * / MOD /MOD 1+ 1- NEGATE ABS MIN MAX LSHIFT RSHIFT
//             */ */MOD  (symmetric intermediate divide via SM/REM)
//   Double:   S>D 2* 2/ 2@ 2! UM* M* UM/MOD SM/REM FM/MOD
//   Logic:    AND OR XOR INVERT
//   Compare:  = <> < > U< 0= 0< 0<> 0> >= <= WITHIN TRUE FALSE
//   Memory:   @ ! C@ C! C, +! FILL ERASE MOVE CELL+ CELLS CHAR+ CHARS
//             ALIGN ALIGNED
//   Parse:    WORD PARSE CHAR [CHAR] BL >NUMBER
//   Comments: \  (
//   I/O:      EMIT KEY CR TYPE SPACE SPACES . U. ACCEPT
//   Strings:  S" ." COUNT
//   Numeric:  BASE DECIMAL HEX  pictured <# # #S #> HOLD SIGN
//   Compile:  : ; CREATE VARIABLE CONSTANT , ALLOT DP HERE
//             LITERAL ' ['] EXECUTE RECURSE IMMEDIATE [ ] POSTPONE
//   Control:  IF ELSE THEN BEGIN UNTIL AGAIN WHILE REPEAT EXIT
//             DO LOOP +LOOP I J LEAVE UNLOOP DOES>
//   Source:   SOURCE >IN EVALUATE REFILL SOURCE-ID
//   Search:   FIND ENVIRONMENT?
//   Outer:    QUIT ABORT ABORT"
//   Except:   CATCH THROW  (Exception word set; used by ABORT path)
//
// Implementation choices / differences (still ANS-legal where noted):
//   xt from ' / FIND / [']  = dictionary *entry* address (not CFA).
//     ANS xt is opaque; EXECUTE expects that entry. >CODE gives the CFA.
//   / MOD /MOD              = symmetric (toward zero), ARM sdiv; FLOORED false.
//   >BODY                   = after name for any xt (used by SEE on colon words);
//                             ANS text is oriented toward CREATE bodies.
//   FIND                    = case-insensitive names.
//   INCLUDE                 = loads whole file into one SOURCE (REFILL is false
//                             for file/EVALUATE sources; true only for terminal).
//   Header layout           = link | flags|len | code | name | body  (see above).
//
// ----------------------------------------------------------------------------
// CORE EXT (6.2) — word names: complete (all required Core Ext names present).
// ----------------------------------------------------------------------------
// ANS Core Extensions word set — implemented in PickleForth:
//   .(  :NONAME  ?DO
//   2>R  2R>  2R@
//   <>  0<>  0>  AGAIN
//   BUFFER:  C"  COMPILE,  [COMPILE]
//   CASE  OF  ENDOF  ENDCASE
//   DEFER  DEFER!  DEFER@  IS  ACTION-OF
//   ERASE  FALSE  TRUE  HEX
//   HOLDS  MARKER
//   NIP  TUCK  PICK  PAD  PARSE  PARSE-NAME
//   REFILL  SOURCE-ID  UNUSED  WITHIN
//   ROLL  U>  U.R
//   S\"   SAVE-INPUT  RESTORE-INPUT
//   VALUE  TO
//   \          (line comment; also used as Core Ext)
//
// Related non-Core-Ext but present (File / tools / common):
//   CMOVE  CMOVE>  INCLUDE  (FLOAD is an alias of INCLUDE)
//
// ENVIRONMENT? returns CORE-EXT true (names present; not a formal ANS certificate).
//
// ----------------------------------------------------------------------------
// PickleForth extensions (not ANS Core / Core Ext)
// ----------------------------------------------------------------------------
//   >CODE >NAME >FLAGS >LINK NAME>STRING DOCOL? DOCON-ADDR CELL
//   SP0 SP@ SP!           stack probes (DEPTH and ABORT use these)
//   LATEST                DP is ANS-style; LATEST is system
//   LIT BRANCH 0BRANCH and *-ADDR plumbing
//   ALIAS SEE WORDS .S DUMP FORGET ANEW USER-DICT REDEF-WARNING
//   FILE-ECHO ON OFF      echo INCLUDE/FLOAD source lines when FILE-ECHO is on
//   .FREE MS@ ELAPSED .ELAPSED CONTAINS
//   Line editor + history; "undefined:" and stack error reporting
//   SIGSEGV/SIGBUS recovery back to QUIT
//
// Implementation notes:
//   - Indirect threaded; colon cells hold dictionary entry addresses (xts)
//   - Prefer high-level Forth in forth_init_str; assembly when needed
//   - CREATE body: does_ip at +0, user PFA at +8 (DOVAR / DODOES / DOCON)
//   - No stack checks inside primitives (speed); outer interpreter checks
//     DSP between words; memory faults recover via signal handler
// ============================================================================

.text
.align 4

// ============================================================================
// Macros
// ============================================================================
.macro NEXT
    ldr x21, [x19], #8
    ldr x1, [x21, #16]
    br x1
.endm

// Debug version of NEXT
.macro DEBUG_NEXT
    ldr x21, [x19], #8
    ldr x1, [x21, #16]
    // Store crash diagnostics and write to stderr
    stp x0, x1, [sp, #-16]!
    adrp x0, next_diag@page
    add x0, x0, next_diag@pageoff
    str x19, [x0]
    str x21, [x0, #8]
    str x1, [x0, #16]
    // Write to stderr (fd=2)
    mov x0, #2
    adr next_diag@page
    add x1, x1, next_diag@pageoff
    mov x2, #24
    mov x16, #4
    svc #0x80
    ldp x0, x1, [sp], #16
    br x1
.endm

.macro DPUSH
    str x20, [x22, #-8]!
    mov x20, x0
.endm

.macro DPOP
    mov x0, x20
    ldr x20, [x22], #8
.endm

.macro RPUSH reg=x19
    str \reg, [x23, #-8]!
.endm

.macro RPOP reg=x19
    ldr \reg, [x23], #8
.endm

// Save/restore full VM register set across bl/svc that might borrow them.
// Call AFTER any intentional TOS/DSP updates so those changes survive.
.macro SAVE_VM
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
.endm

.macro RESTORE_VM
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
.endm

// ============================================================================
// Entry Point
// ============================================================================
.globl _main
_main:
    adrp x22, data_stack@page
    add  x22, x22, data_stack@pageoff
    add  x22, x22, #4096      // DSP starts at TOP of stack (grows down)
    adrp x23, return_stack@page
    add  x23, x23, return_stack@pageoff
    add  x23, x23, #2048      // RSP starts at TOP of stack (grows down)

    // x24 = address of latest_var (pointer to variable holding newest dict entry)
    adrp x24, latest_var@page
    add  x24, x24, latest_var@pageoff

    // Initialize TOS (empty stack)
    mov  x20, #0

    // Initialize latest_var to newest static word
    adrp x0, dict_restore_input@page
    add  x0, x0, dict_restore_input@pageoff
    str  x0, [x24]

    // HERE = user_dict_area
    adrp x0, here_ptr@page
    add  x0, x0, here_ptr@pageoff
    adrp x1, user_dict_area@page
    add  x1, x1, user_dict_area@pageoff
    str  x1, [x0]

    // Catch SIGSEGV/SIGBUS (e.g. @ on address 0) and return to QUIT
    bl _install_fault_handlers

    // Patch all dict entry code fields (Mach-O chained fixups broken for .quad cross-section refs)
    bl _patch_dict

    // Print welcome via raw SVC
    mov x0, #1
    adrp x1, str_hello@page
    add x1, x1, str_hello@pageoff
    mov x2, #19                    // "PickleForth v0.2.0\n"
    mov x16, #4
    svc #0x80

    // Initialize Forth from init string via SOURCE / >IN
    adrp x0, forth_init_str@page
    add x0, x0, forth_init_str@pageoff
    mov x1, x0
    mov x2, #0
1:
    ldrb w3, [x1, x2]
    cbz w3, 2f
    add x2, x2, #1
    b 1b
2:
    mov x1, x2                      // len
    bl _set_source
    b _interpret_loop

// ---------------------------------------------------------------------------
// Fault recovery: SIGSEGV / SIGBUS → message → QUIT (no process death)
// Does not slow primitives; only runs if a memory fault occurs.
// ---------------------------------------------------------------------------
_install_fault_handlers:
    stp x29, x30, [sp, #-16]!
    adrp x0, fault_handlers_on@page
    add x0, x0, fault_handlers_on@pageoff
    ldr x1, [x0]
    cbnz x1, 1f
    mov x1, #1
    str x1, [x0]
    mov x0, #11                    // SIGSEGV
    adrp x1, _fault_handler@page
    add x1, x1, _fault_handler@pageoff
    bl _signal
    mov x0, #10                    // SIGBUS
    adrp x1, _fault_handler@page
    add x1, x1, _fault_handler@pageoff
    bl _signal
1:
    ldp x29, x30, [sp], #16
    ret

// async-signal-safe: write(2) + siglongjmp only
.align 4
_fault_handler:
    mov x0, #2                     // stderr
    adrp x1, str_memfault@page
    add x1, x1, str_memfault@pageoff
    mov x2, #20                    // "memory access error\n"
    mov x16, #4
    svc #0x80
    adrp x0, quit_jmpbuf@page
    add x0, x0, quit_jmpbuf@pageoff
    mov x1, #1
    bl _siglongjmp                 // does not return

// ============================================================================
// DOCOL / DOEXIT / DOVAR
// ============================================================================
// Body of a colon/CREATE word starts after the 8-byte-aligned name field.
// name_len = flags|len & 0xFF; name_bytes = (name_len + 7) & ~7; body = entry+24+name_bytes
.macro DICT_BODY_ADDR dst, entry
    ldr \dst, [\entry, #8]
    and \dst, \dst, #0xFF
    add \dst, \dst, #7
    bic \dst, \dst, #7
    add \dst, \entry, \dst
    add \dst, \dst, #24
.endm

DOCOL:
    RPUSH
    DICT_BODY_ADDR x19, x21
    NEXT

DOEXIT:
    RPOP
    NEXT

DOVAR:
    // PFA = body+8 (body+0 reserved for does_ip)
    str x20, [x22, #-8]!
    DICT_BODY_ADDR x20, x21
    add x20, x20, #8
    NEXT

DOCON:
    str x20, [x22, #-8]!
    DICT_BODY_ADDR x0, x21
    ldr x20, [x0, #8]              // value at user PFA
    NEXT

// DODOES: push PFA (body+8), run high-level fragment at [body+0]
DODOES:
    RPUSH
    DICT_BODY_ADDR x0, x21
    ldr x19, [x0]                  // does_ip
    add x0, x0, #8                 // PFA
    str x20, [x22, #-8]!
    mov x20, x0
    NEXT

// ============================================================================
// _patch_dict - Patch all dict entry links and code fields at startup
// Uses ADR (PC-relative, ±1MB) instead of ADRP+ADD to avoid chained fixup issues.
// ============================================================================
_patch_dict:
    .macro PATCH_LINK dict_entry, prev_entry
    adrp x0, \dict_entry@page
    add  x0, x0, \dict_entry@pageoff
    adrp x1, \prev_entry@page
    add  x1, x1, \prev_entry@pageoff
    str  x1, [x0]
    .endm

    .macro PATCH_CODE dict_entry, native_code
    adrp x0, \dict_entry@page
    add  x0, x0, \dict_entry@pageoff
    adrp x1, \native_code@page
    add  x1, x1, \native_code@pageoff
    str  x1, [x0, #16]
    .endm

    // Patch link chain (dict_exit link=0 is already correct)
    PATCH_LINK dict_semi, dict_exit
    nop
    PATCH_LINK dict_lit, dict_semi
    nop
    PATCH_LINK dict_dup, dict_lit
    nop
    PATCH_LINK dict_drop, dict_dup
    nop
    PATCH_LINK dict_swap, dict_drop
    nop
    PATCH_LINK dict_over, dict_swap
    nop
    PATCH_LINK dict_rot, dict_over
    nop
    PATCH_LINK dict_nip, dict_rot
    nop
    PATCH_LINK dict_tuck, dict_nip
    nop
    PATCH_LINK dict_pick, dict_tuck
    nop
    PATCH_LINK dict_tor, dict_pick
    nop
    PATCH_LINK dict_rto, dict_tor
    nop
    PATCH_LINK dict_rfetch, dict_rto
    nop
    PATCH_LINK dict_plus, dict_rfetch
    nop
    PATCH_LINK dict_minus, dict_plus
    nop
    PATCH_LINK dict_star, dict_minus
    nop
    PATCH_LINK dict_slash, dict_star
    nop
    PATCH_LINK dict_mod, dict_slash
    nop
    PATCH_LINK dict_slmod, dict_mod
    nop
    PATCH_LINK dict_equal, dict_slmod
    nop
    PATCH_LINK dict_less, dict_equal
    nop
    PATCH_LINK dict_greater, dict_less
    nop
    PATCH_LINK dict_uless, dict_greater
    nop
    PATCH_LINK dict_and, dict_uless
    nop
    PATCH_LINK dict_or, dict_and
    nop
    PATCH_LINK dict_xor, dict_or
    nop
    PATCH_LINK dict_invert, dict_xor
    nop
    PATCH_LINK dict_zequal, dict_invert
    nop
    PATCH_LINK dict_zless, dict_zequal
    nop
    PATCH_LINK dict_true, dict_zless
    nop
    PATCH_LINK dict_false, dict_true
    nop
    PATCH_LINK dict_oneplus, dict_false
    nop
    PATCH_LINK dict_oneminus, dict_oneplus
    nop
    PATCH_LINK dict_cell, dict_oneminus
    nop
    PATCH_LINK dict_cells, dict_cell
    nop
    PATCH_LINK dict_fetch, dict_cells
    nop
    PATCH_LINK dict_store, dict_fetch
    nop
    PATCH_LINK dict_cfetch, dict_store
    nop
    PATCH_LINK dict_cstore, dict_cfetch
    nop
    PATCH_LINK dict_plusstore, dict_cstore
    nop
    PATCH_LINK dict_emit, dict_plusstore
    nop
    PATCH_LINK dict_key, dict_emit
    nop
    PATCH_LINK dict_cr, dict_key
    nop
    PATCH_LINK dict_dot, dict_cr
    nop
    PATCH_LINK dict_udot, dict_dot
    nop
    PATCH_LINK dict_dots, dict_udot
    nop
    PATCH_LINK dict_type, dict_dots
    nop
    PATCH_LINK dict_state, dict_type
    nop
    PATCH_LINK dict_base, dict_state
    nop
    PATCH_LINK dict_rbrack, dict_base
    nop
    PATCH_LINK dict_lbrack, dict_rbrack
    nop

    // Patch code fields
    PATCH_CODE dict_exit, DOEXIT
    nop
    PATCH_CODE dict_semi, XSEMI
    nop
    PATCH_CODE dict_lit, XLit
    nop
    PATCH_CODE dict_dup, XDUP
    nop
    PATCH_CODE dict_drop, XDROP
    nop
    PATCH_CODE dict_swap, XSWAP
    nop
    PATCH_CODE dict_over, XOVER
    nop
    PATCH_CODE dict_rot, XROT
    nop
    PATCH_CODE dict_nip, XNIP
    nop
    PATCH_CODE dict_tuck, XTUCK
    nop
    PATCH_CODE dict_pick, XPICK
    nop
    PATCH_CODE dict_tor, XTOR
    nop
    PATCH_CODE dict_rto, XRTO
    nop
    PATCH_CODE dict_rfetch, XRFETCH
    nop
    PATCH_CODE dict_plus, XPLUS
    nop
    PATCH_CODE dict_minus, XMINUS
    nop
    PATCH_CODE dict_star, XSTAR
    nop
    PATCH_CODE dict_slash, XSLASH
    nop
    PATCH_CODE dict_mod, XMOD
    nop
    PATCH_CODE dict_slmod, XSLMOD
    nop
    PATCH_CODE dict_equal, XEQUAL
    nop
    PATCH_CODE dict_less, XLESS
    nop
    PATCH_CODE dict_greater, XGREATER
    nop
    PATCH_CODE dict_uless, XULESS
    nop
    PATCH_CODE dict_and, XAND
    nop
    PATCH_CODE dict_or, XORR
    nop
    PATCH_CODE dict_xor, XXOR
    nop
    PATCH_CODE dict_invert, XINVERT
    nop
    PATCH_CODE dict_zequal, XZEQUAL
    nop
    PATCH_CODE dict_zless, XZLESS
    nop
    PATCH_CODE dict_true, XTRUE
    nop
    PATCH_CODE dict_false, XFALSE
    nop
    PATCH_CODE dict_oneplus, XONEPLUS
    nop
    PATCH_CODE dict_oneminus, XONEMINUS
    nop
    PATCH_CODE dict_cell, XCELL
    nop
    PATCH_CODE dict_cells, XCELLS
    nop
    PATCH_CODE dict_fetch, XFETCH
    nop
    PATCH_CODE dict_store, XSTORE
    nop
    PATCH_CODE dict_cfetch, XCFETCH
    nop
    PATCH_CODE dict_cstore, XCSTORE
    nop
    PATCH_CODE dict_plusstore, XPLUSSTORE
    nop
    PATCH_CODE dict_emit, XEMIT
    nop
    PATCH_CODE dict_key, XKEY
    nop
    PATCH_CODE dict_cr, XCR
    nop
    PATCH_CODE dict_dot, XDOT
    nop
    PATCH_CODE dict_udot, XUDOT
    nop
    PATCH_CODE dict_dots, XDOTS
    nop
    PATCH_CODE dict_type, XTYPE
    nop
    PATCH_CODE dict_state, XSTATE
    nop
    PATCH_CODE dict_base, XBASE
    nop
    PATCH_CODE dict_rbrack, XRBRA
    nop
    PATCH_CODE dict_lbrack, XLBRA
    nop
    PATCH_CODE dict_restart, XRESTART
    nop

    // Patch new compilation primitives
    PATCH_LINK dict_dp, dict_lbrack
    nop
    PATCH_LINK dict_here, dict_dp
    nop
    PATCH_LINK dict_alot, dict_here
    nop
    PATCH_LINK dict_comma, dict_alot
    nop
    PATCH_LINK dict_find, dict_comma
    nop
    PATCH_LINK dict_tick, dict_find
    nop
    PATCH_LINK dict_execute, dict_tick
    nop
    PATCH_LINK dict_literal, dict_execute
    nop
    PATCH_LINK dict_immediate, dict_literal
    nop
    PATCH_LINK dict_colon, dict_immediate
    nop
    PATCH_LINK dict_create, dict_colon
    nop
    PATCH_LINK dict_0branch, dict_create
    nop
    PATCH_LINK dict_branch, dict_0branch
    nop

    PATCH_CODE dict_dp, XDP
    nop
    PATCH_CODE dict_here, XHERE
    nop
    PATCH_CODE dict_alot, XALLOT
    nop
    PATCH_CODE dict_comma, XCOMMA
    nop
    PATCH_CODE dict_find, XFIND
    nop
    PATCH_CODE dict_tick, XTICK
    nop
    PATCH_CODE dict_execute, XEXECUTE
    nop
    PATCH_CODE dict_literal, XLITERAL
    nop
    PATCH_CODE dict_immediate, XIMMEDIATE
    nop
    PATCH_CODE dict_colon, XCOLON
    nop
    PATCH_CODE dict_create, XCREATE
    nop
    PATCH_CODE dict_0branch, X0Branch
    nop
    PATCH_CODE dict_branch, XBranch
    nop
    PATCH_LINK dict_bye, dict_branch
    nop
    PATCH_CODE dict_bye, XBYE
    nop
    PATCH_LINK dict_include, dict_bye
    nop
    PATCH_CODE dict_include, XINCLUDE
    nop
    PATCH_LINK dict_latest, dict_include
    nop
    PATCH_CODE dict_latest, XLATEST
    nop
    PATCH_LINK dict_qdup, dict_latest
    nop
    PATCH_CODE dict_qdup, XQDUP
    nop
    PATCH_LINK dict_bracket_tick, dict_qdup
    nop
    PATCH_CODE dict_bracket_tick, XBRACKET_TICK
    nop
    PATCH_LINK dict_lit_addr, dict_bracket_tick
    nop
    PATCH_CODE dict_lit_addr, XLIT_ADDR
    nop
    PATCH_LINK dict_0br_addr, dict_lit_addr
    nop
    PATCH_CODE dict_0br_addr, X0BRANCH_ADDR
    nop
    PATCH_LINK dict_br_addr, dict_0br_addr
    nop
    PATCH_CODE dict_br_addr, XBRANCH_ADDR
    nop
    PATCH_LINK dict_exit_addr, dict_br_addr
    nop
    PATCH_CODE dict_exit_addr, XEXIT_ADDR
    nop

    // ANS Core primitives (wired from existing code + new parse/comment)
    PATCH_LINK dict_negate, dict_exit_addr
    nop
    PATCH_CODE dict_negate, XNEGATE
    nop
    PATCH_LINK dict_abs, dict_negate
    nop
    PATCH_CODE dict_abs, XABS
    nop
    PATCH_LINK dict_min, dict_abs
    nop
    PATCH_CODE dict_min, XMIN
    nop
    PATCH_LINK dict_max, dict_min
    nop
    PATCH_CODE dict_max, XMAX
    nop
    PATCH_LINK dict_lshift, dict_max
    nop
    PATCH_CODE dict_lshift, XLSHIFT
    nop
    PATCH_LINK dict_rshift, dict_lshift
    nop
    PATCH_CODE dict_rshift, XRSHIFT
    nop
    PATCH_LINK dict_nequal, dict_rshift
    nop
    PATCH_CODE dict_nequal, XNEQUAL
    nop
    PATCH_LINK dict_parse, dict_nequal
    nop
    PATCH_CODE dict_parse, XPARSE
    nop
    PATCH_LINK dict_word, dict_parse
    nop
    PATCH_CODE dict_word, XWORD
    nop
    PATCH_LINK dict_backslash, dict_word
    nop
    PATCH_CODE dict_backslash, XBACKSLASH
    nop
    PATCH_LINK dict_paren, dict_backslash
    nop
    PATCH_CODE dict_paren, XPAREN
    nop
    PATCH_LINK dict_docon_addr, dict_paren
    nop
    PATCH_CODE dict_docon_addr, XDOCON_ADDR
    nop
    PATCH_LINK dict_source, dict_docon_addr
    nop
    PATCH_CODE dict_source, XSOURCE
    nop
    PATCH_LINK dict_to_in, dict_source
    nop
    PATCH_CODE dict_to_in, XTOIN
    nop
    PATCH_LINK dict_slit, dict_to_in
    nop
    PATCH_CODE dict_slit, XSLIT
    nop
    PATCH_LINK dict_squote, dict_slit
    nop
    PATCH_CODE dict_squote, XSQUOTE
    nop
    PATCH_LINK dict_dotquote, dict_squote
    nop
    PATCH_CODE dict_dotquote, XDOTQ
    nop
    // DO LOOP family + DOES>
    PATCH_LINK dict_do_rt, dict_dotquote
    nop
    PATCH_CODE dict_do_rt, XDO_RT
    nop
    PATCH_LINK dict_qdo_rt, dict_do_rt
    nop
    PATCH_CODE dict_qdo_rt, XQDO_RT
    nop
    PATCH_LINK dict_loop_rt, dict_qdo_rt
    nop
    PATCH_CODE dict_loop_rt, XLOOP_RT
    nop
    PATCH_LINK dict_ploop_rt, dict_loop_rt
    nop
    PATCH_CODE dict_ploop_rt, XPLUSLOOP_RT
    nop
    PATCH_LINK dict_i, dict_ploop_rt
    nop
    PATCH_CODE dict_i, XI
    nop
    PATCH_LINK dict_j, dict_i
    nop
    PATCH_CODE dict_j, XJ
    nop
    PATCH_LINK dict_unloop, dict_j
    nop
    PATCH_CODE dict_unloop, XUNLOOP
    nop
    PATCH_LINK dict_leave, dict_unloop
    nop
    PATCH_CODE dict_leave, XLEAVE
    nop
    PATCH_LINK dict_does_rt, dict_leave
    nop
    PATCH_CODE dict_does_rt, XDOES_RT
    nop
    PATCH_LINK dict_pad, dict_does_rt
    nop
    PATCH_CODE dict_pad, XPAD
    nop
    PATCH_LINK dict_does, dict_pad
    nop
    PATCH_CODE dict_does, XDOES
    nop
    PATCH_LINK dict_evaluate, dict_does
    nop
    PATCH_CODE dict_evaluate, XEVALUATE
    nop
    PATCH_LINK dict_catch, dict_evaluate
    nop
    PATCH_CODE dict_catch, XCATCH
    nop
    PATCH_LINK dict_throw, dict_catch
    nop
    PATCH_CODE dict_throw, XTHROW
    nop
    PATCH_LINK dict_catch_ok, dict_throw
    nop
    PATCH_CODE dict_catch_ok, XCATCH_OK
    nop
    PATCH_LINK dict_contains, dict_catch_ok
    nop
    PATCH_CODE dict_contains, XCONTAINS
    nop
    PATCH_LINK dict_msfetch, dict_contains
    nop
    PATCH_CODE dict_msfetch, XMSFETCH
    nop
    PATCH_LINK dict_unused, dict_msfetch
    nop
    PATCH_CODE dict_unused, XUNUSED
    nop
    PATCH_LINK dict_redef_warning, dict_unused
    nop
    PATCH_CODE dict_redef_warning, XREDEF_WARNING
    nop
    PATCH_LINK dict_user_dict, dict_redef_warning
    nop
    PATCH_CODE dict_user_dict, XUSER_DICT
    nop
    // SP0/SP@ for high-level DEPTH; SPACES C, S>D 2* 2/ 2@ 2!
    PATCH_LINK dict_sp0, dict_user_dict
    nop
    PATCH_CODE dict_sp0, XSP0
    nop
    PATCH_LINK dict_spfetch, dict_sp0
    nop
    PATCH_CODE dict_spfetch, XSPFETCH
    nop
    PATCH_LINK dict_spstore, dict_spfetch
    nop
    PATCH_CODE dict_spstore, XSPSTORE
    nop
    PATCH_LINK dict_spaces, dict_spstore
    nop
    PATCH_CODE dict_spaces, XSPACES
    nop
    PATCH_LINK dict_ccomma, dict_spaces
    nop
    PATCH_CODE dict_ccomma, XCCOMMA
    nop
    PATCH_LINK dict_stod, dict_ccomma
    nop
    PATCH_CODE dict_stod, XSTOD
    nop
    PATCH_LINK dict_twostar, dict_stod
    nop
    PATCH_CODE dict_twostar, XTWOSTAR
    nop
    PATCH_LINK dict_twoslash, dict_twostar
    nop
    PATCH_CODE dict_twoslash, XTWOSLASH
    nop
    PATCH_LINK dict_twofetch, dict_twoslash
    nop
    PATCH_CODE dict_twofetch, XTWOFETCH
    nop
    PATCH_LINK dict_twostore, dict_twofetch
    nop
    PATCH_CODE dict_twostore, XTWOSTORE
    nop
    // Double-cell suite
    PATCH_LINK dict_umstar, dict_twostore
    nop
    PATCH_CODE dict_umstar, XUMSTAR
    nop
    PATCH_LINK dict_mstar, dict_umstar
    nop
    PATCH_CODE dict_mstar, XMSTAR
    nop
    PATCH_LINK dict_ummod, dict_mstar
    nop
    PATCH_CODE dict_ummod, XUMMOD
    nop
    PATCH_LINK dict_smrem, dict_ummod
    nop
    PATCH_CODE dict_smrem, XSMREM
    nop
    PATCH_LINK dict_fmmod, dict_smrem
    nop
    PATCH_CODE dict_fmmod, XFMMOD
    nop
    PATCH_LINK dict_quit, dict_fmmod
    nop
    PATCH_CODE dict_quit, XQUIT
    nop
    // Group 3: SOURCE-ID REFILL ACCEPT >NUMBER ENVIRONMENT?
    PATCH_LINK dict_source_id, dict_quit
    nop
    PATCH_CODE dict_source_id, XSOURCE_ID
    nop
    PATCH_LINK dict_refill, dict_source_id
    nop
    PATCH_CODE dict_refill, XREFILL
    nop
    PATCH_LINK dict_accept, dict_refill
    nop
    PATCH_CODE dict_accept, XACCEPT
    nop
    PATCH_LINK dict_to_number, dict_accept
    nop
    PATCH_CODE dict_to_number, XTONUMBER
    nop
    PATCH_LINK dict_environment_q, dict_to_number
    nop
    PATCH_CODE dict_environment_q, XENVIRONMENT_Q
    nop
    // FILE-ECHO ( -- addr )
    PATCH_LINK dict_file_echo, dict_environment_q
    nop
    PATCH_CODE dict_file_echo, XFILE_ECHO
    nop
    // Core Ext CODE: 2>R 2R> 2R@ ROLL :NONAME (C") C" S\" SAVE/RESTORE-INPUT
    PATCH_LINK dict_parse_name, dict_file_echo
    nop
    PATCH_CODE dict_parse_name, XPARSE_NAME
    nop
    PATCH_LINK dict_2tor, dict_parse_name
    nop
    PATCH_CODE dict_2tor, X2TOR
    nop
    PATCH_LINK dict_2rto, dict_2tor
    nop
    PATCH_CODE dict_2rto, X2RTO
    nop
    PATCH_LINK dict_2rfetch, dict_2rto
    nop
    PATCH_CODE dict_2rfetch, X2RFETCH
    nop
    PATCH_LINK dict_roll, dict_2rfetch
    nop
    PATCH_CODE dict_roll, XROLL
    nop
    PATCH_LINK dict_noname, dict_roll
    nop
    PATCH_CODE dict_noname, XNONAME
    nop
    PATCH_LINK dict_cstr, dict_noname
    nop
    PATCH_CODE dict_cstr, XCSTR
    nop
    PATCH_LINK dict_cquote, dict_cstr
    nop
    PATCH_CODE dict_cquote, XCQUOTE
    nop
    PATCH_LINK dict_sescape, dict_cquote
    nop
    PATCH_CODE dict_sescape, XSESCAPE
    nop
    PATCH_LINK dict_save_input, dict_sescape
    nop
    PATCH_CODE dict_save_input, XSAVE_INPUT
    nop
    PATCH_LINK dict_restore_input, dict_save_input
    nop
    PATCH_CODE dict_restore_input, XRESTORE_INPUT
    nop

    .purgem PATCH_CODE
    .purgem PATCH_LINK
    ret

// ============================================================================
// Stack Primitives
// ============================================================================
// Note: no per-primitive stack checks (performance). The outer interpreter
// validates the data stack between words via _check_stack.
XDUP:
    str x20, [x22, #-8]!
    NEXT

XDROP:
    ldr x20, [x22], #8
    NEXT

XSWAP:
    ldr x0, [x22]
    str x20, [x22]
    mov x20, x0
    NEXT

XOVER:
    str x20, [x22, #-8]!
    ldr x20, [x22, #8]
    NEXT

XROT:
    ldr x0, [x22]
    ldr x1, [x22, #8]
    str x0, [x22, #8]
    str x20, [x22]
    mov x20, x1
    NEXT

XNIP:
    ldr x0, [x22], #8
    NEXT

XTUCK:
    ldr x0, [x22]
    str x20, [x22, #-8]!
    str x0, [x22]
    NEXT

XPICK:
    lsl x0, x20, #3
    ldr x0, [x22, x0]
    mov x20, x0
    NEXT

// ROLL ( xu xu-1 ... x0 u -- xu-1 ... x0 xu )
// u=0 no-op; u=1 SWAP; u=2 ROT.
XROLL:
    mov x1, x20                    // u
    ldr x20, [x22], #8             // pop u; TOS = x0
    cbz x1, _roll_done
    // Under TOS: [DSP+0]=x1 ... [DSP+(u-1)*8]=xu
    sub x2, x1, #1
    lsl x2, x2, #3                 // (u-1)*8
    ldr x3, [x22, x2]              // xu
    mov x0, x20                    // save old x0
    // shift slots [u-1]..[1] <- [u-2]..[0]
    mov x4, x2
1:
    cbz x4, 2f
    sub x5, x4, #8
    ldr x6, [x22, x5]
    str x6, [x22, x4]
    mov x4, x5
    b 1b
2:
    str x0, [x22]                  // [0] = old x0
    mov x20, x3                    // TOS = xu
_roll_done:
    NEXT

XTOR:
    str x20, [x23, #-8]!
    ldr x20, [x22], #8
    NEXT

XRTO:
    DPUSH
    ldr x0, [x23], #8
    mov x20, x0
    NEXT

XRFETCH:
    DPUSH
    ldr x0, [x23]
    mov x20, x0
    NEXT

// 2>R ( x1 x2 -- ) ( R: -- x1 x2 )  must be CODE (colon would clobber IP)
X2TOR:
    ldr x0, [x22], #8              // x1
    str x0, [x23, #-8]!            // R: x1
    str x20, [x23, #-8]!           // R: x1 x2
    ldr x20, [x22], #8
    NEXT

// 2R> ( -- x1 x2 ) ( R: x1 x2 -- )
X2RTO:
    str x20, [x22, #-8]!
    ldr x0, [x23], #8              // x2
    ldr x1, [x23], #8              // x1
    str x1, [x22, #-8]!
    mov x20, x0
    NEXT

// 2R@ ( -- x1 x2 ) ( R: x1 x2 -- x1 x2 )
X2RFETCH:
    str x20, [x22, #-8]!
    ldr x0, [x23]                  // x2
    ldr x1, [x23, #8]              // x1
    str x1, [x22, #-8]!
    mov x20, x0
    NEXT

// ============================================================================
// Arithmetic
// ============================================================================
XPLUS:
    ldr x0, [x22], #8
    add x20, x20, x0
    NEXT

XMINUS:
    ldr x0, [x22], #8
    sub x20, x0, x20
    NEXT

XSTAR:
    ldr x0, [x22], #8
    mul x20, x20, x0
    NEXT

XSLASH:
    ldr x0, [x22], #8
    sdiv x20, x0, x20
    NEXT

XMOD:
    ldr x0, [x22], #8
    sdiv x1, x0, x20
    msub x20, x1, x20, x0
    NEXT

XSLMOD:
    ldr x0, [x22], #8
    sdiv x1, x0, x20
    msub x2, x1, x20, x0
    str x2, [x22, #-8]!
    mov x20, x1
    NEXT

XONEPLUS:
    add x20, x20, #1
    NEXT

XONEMINUS:
    sub x20, x20, #1
    NEXT

XNEGATE:
    neg x20, x20
    NEXT

XABS:
    cmp x20, #0
    csneg x20, x20, x20, ge
    NEXT

XMIN:
    ldr x0, [x22], #8
    cmp x0, x20
    csel x20, x0, x20, lt
    NEXT

XMAX:
    ldr x0, [x22], #8
    cmp x0, x20
    csel x20, x0, x20, gt
    NEXT

// ============================================================================
// Logic / Bitwise
// ============================================================================
XAND:
    ldr x0, [x22], #8
    and x20, x20, x0
    NEXT

XORR:
    ldr x0, [x22], #8
    orr x20, x20, x0
    NEXT

XXOR:
    ldr x0, [x22], #8
    eor x20, x20, x0
    NEXT

XINVERT:
    mvn x20, x20
    NEXT

XLSHIFT:
    ldr x0, [x22], #8
    lsl x20, x0, x20
    NEXT

XRSHIFT:
    ldr x0, [x22], #8
    lsr x20, x0, x20
    NEXT

// ============================================================================
// Comparison
// ============================================================================
// Comparisons return standard Forth flags: 0 (false) or -1 (true)
XEQUAL:
    ldr x0, [x22], #8
    cmp x0, x20
    csetm x20, eq
    NEXT

XNEQUAL:
    ldr x0, [x22], #8
    cmp x0, x20
    csetm x20, ne
    NEXT

XLESS:
    ldr x0, [x22], #8
    cmp x0, x20
    csetm x20, lt
    NEXT

XGREATER:
    ldr x0, [x22], #8
    cmp x0, x20
    csetm x20, gt
    NEXT

XULESS:
    ldr x0, [x22], #8
    cmp x0, x20
    csetm x20, lo
    NEXT

XZEQUAL:
    cmp x20, #0
    csetm x20, eq
    NEXT

XZLESS:
    cmp x20, #0
    csetm x20, lt
    NEXT

// TRUE is all-bits-set (-1) per standard Forth
XTRUE:
    DPUSH
    mov x20, #-1
    NEXT

XFALSE:
    DPUSH
    mov x20, #0
    NEXT

// ============================================================================
// Memory
// ============================================================================
XFETCH:
    ldr x20, [x20]
    NEXT

// ! ( x addr -- ) store x at addr  [TOS=addr, second=x]
XSTORE:
    ldr x0, [x22], #8      // x0 = value
    str x0, [x20]          // *addr = value
    ldr x20, [x22], #8
    NEXT

XCFETCH:
    ldrb w20, [x20]
    NEXT

// C! ( char addr -- ) store char at addr
XCSTORE:
    ldr x0, [x22], #8      // x0 = char
    strb w0, [x20]         // *addr = char
    ldr x20, [x22], #8
    NEXT

XPLUSSTORE:
    ldr x0, [x22], #8
    ldr x1, [x20]
    add x1, x1, x0
    str x1, [x20]
    ldr x20, [x22], #8
    NEXT

XCELL:
    DPUSH
    mov x20, #8
    NEXT

XCELLS:
    lsl x20, x20, #3
    NEXT

XBL:
    DPUSH
    mov x20, #32
    NEXT

// ============================================================================
// I/O
// ============================================================================
// Helpers (_putchar etc.) only touch x0-x18/x29/x30; Darwin svc preserves
// x19-x28. We still SAVE_VM around bl so a future helper cannot clobber the VM.
XEMIT:
    mov x0, x20
    ldr x20, [x22], #8
    SAVE_VM
    bl _putchar
    RESTORE_VM
    NEXT

XKEY:
    SAVE_VM
    bl _getchar
    // char in x0; restore VM then push
    RESTORE_VM
    DPUSH               // also does mov x20, x0
    NEXT

XCR:
    SAVE_VM
    mov x0, #10
    bl _putchar
    RESTORE_VM
    NEXT

XDOT:
    mov x0, x20
    ldr x20, [x22], #8
    SAVE_VM
    bl _print_signed
    mov x0, #32
    bl _putchar
    RESTORE_VM
    NEXT

XUDOT:
    mov x0, x20
    ldr x20, [x22], #8
    SAVE_VM
    bl _print_unsigned
    RESTORE_VM
    NEXT

XDOTS:
    SAVE_VM
    bl _print_dots
    RESTORE_VM
    NEXT

// TYPE ( addr u -- ) write u bytes at addr to stdout
XTYPE:
    mov x2, x20            // x2 = u (length)
    ldr x1, [x22], #8      // x1 = addr
    ldr x20, [x22], #8
    cbz x2, _type_done
    mov x0, #1             // fd = stdout
    mov x16, #4            // write
    svc #0x80
_type_done:
    NEXT

// ============================================================================
// Control Flow
// ============================================================================
XBranch:
    ldr x0, [x19]
    add x19, x19, x0
    NEXT

X0Branch:
    cbz x20, _0br_true
    ldr x20, [x22], #8
    add x19, x19, #8
    NEXT
_0br_true:
    ldr x20, [x22], #8
    ldr x0, [x19]
    add x19, x19, x0
    NEXT

XLit:
    str x20, [x22, #-8]!
    ldr x20, [x19], #8
    NEXT

// ============================================================================
// Compilation Primitives
// ============================================================================

// DP ( -- a-addr )  address of the dictionary pointer cell (ANS-style)
XDP:
    str x20, [x22, #-8]!
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    mov x20, x0
    NEXT

// HERE ( -- addr ) push current dictionary pointer (also : HERE DP @ ;)
XHERE:
    DPUSH
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x20, [x0]
    NEXT

// ALLOT ( n -- ) advance HERE by n bytes
XALLOT:
    mov x0, x20
    ldr x20, [x22], #8
    // Use _compile_cell's approach to access here_ptr
    adrp x1, here_ptr@page
    add x1, x1, here_ptr@pageoff
    ldr x2, [x1]
    add x2, x2, x0
    str x2, [x1]
    NEXT

// , ( x -- ) compile cell at HERE
XCOMMA:
    mov x0, x20
    ldr x20, [x22], #8
    bl _compile_cell
    NEXT

// FIND ( c-addr -- c-addr 0 | xt 1 | xt -1 )  ANS Core
// c-addr is a counted string. 1 = immediate, -1 = non-immediate.
XFIND:
    mov x2, x20                 // c-addr (counted)
    ldrb w1, [x2]               // u = count
    add x0, x2, #1              // address of name chars
    bl _find_word
    cbz x0, _xfind_not
    // x0 = entry; reload flags (x1 may be ok from _find_word)
    ldr x1, [x0, #8]
    tst x1, #0x100
    mov x4, #1
    mov x5, #-1
    csel x4, x4, x5, ne         // immediate -> 1, else -1
    mov x20, x0                 // xt
    str x20, [x22, #-8]!
    mov x20, x4                 // flag
    NEXT
_xfind_not:
    str x20, [x22, #-8]!        // c-addr under 0
    mov x20, #0
    NEXT

// ' ( "name" -- xt ) tick: find word and push dictionary entry (XT)
// XT is the dict entry address; DOCOL/native words all expect x21 = entry.
XTICK:
    bl _next_word
    cbz x1, _tick_fail
    bl _find_word
    cbz x0, _tick_fail
    DPUSH
    mov x20, x0         // push entry address (XT)
    NEXT
_tick_fail:
    // Print "?" and abort
    mov x0, #1
    adrp x1, str_quest@page
    add x1, x1, str_quest@pageoff
    mov x2, #2
    mov x16, #4
    svc #0x80
    b _do_quit

// EXECUTE ( xt -- ) execute a dictionary entry and return to caller.
// Must NOT force the interpret trampoline: when EXECUTE is used inside a
// colon definition (e.g. ELAPSED), IP already points at the next cell and
// DOCOL/NEXT/EXIT nest correctly. Interpret-time EXECUTE still returns via
// the existing restart_cell IP set up by _exec_found.
XEXECUTE:
    mov x21, x20                   // W = xt (dict entry)
    ldr x20, [x22], #8             // pop xt → prior TOS
    ldr x1, [x21, #16]             // code field
    br x1

// LITERAL ( x -- ) immediate: compile LIT + value
XLITERAL:
    // Save TOS value (bl will clobber x0-x3)
    str x20, [x23, #-8]!
    // Compile LIT entry address
    adrp x0, dict_lit@page
    add x0, x0, dict_lit@pageoff
    bl _compile_cell
    // Compile the literal value
    ldr x0, [x23], #8
    bl _compile_cell
    NEXT

// IMMEDIATE ( -- ) mark last defined word as immediate
XIMMEDIATE:
    ldr x0, [x24]       // x0 = address of last defined word
    ldr x1, [x0, #8]    // load flags|len
    orr x1, x1, #0x100  // set immediate bit
    str x1, [x0, #8]
    NEXT

// : ( "name" -- ) start colon definition
XCOLON:
    // Not a :NONAME definition
    adrp x0, noname_xt@page
    add x0, x0, noname_xt@pageoff
    str xzr, [x0]
    // Save VM state and frame
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    bl _next_word
    cbz x1, _colon_fail
    // x0 = word addr, x1 = word len
    mov x19, x0          // save word addr
    mov x20, x1          // save word len
    // Warn if this name already exists in the dictionary
    mov x0, x19
    mov x1, x20
    bl _warn_redef

    // Get current HERE = new entry address
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x0, [x0]
    mov x21, x0          // x21 = new entry

    // Write link = *x24 (previous latest)
    ldr x1, [x24]
    str x1, [x0], #8

    // Write flags|len = len
    str x20, [x0], #8

    // Write code_field = DOCOL
    adrp x1, DOCOL@page
    add x1, x1, DOCOL@pageoff
    str x1, [x0], #8

    // Copy name (x19) with length x20, pad to 8 bytes
    mov x2, #0
_colon_name_loop:
    cmp x2, x20
    b.ge _colon_name_pad
    ldrb w3, [x19, x2]
    strb w3, [x0, x2]
    add x2, x2, #1
    b _colon_name_loop
_colon_name_pad:
    mov w3, #0
_colon_pad_loop:
    tst x2, #7
    b.eq _colon_name_done
    strb w3, [x0, x2]
    add x2, x2, #1
    b _colon_pad_loop
_colon_name_done:
    add x0, x0, x2

    // Update HERE
    adrp x1, here_ptr@page
    add x1, x1, here_ptr@pageoff
    str x0, [x1]

    // Update latest (x24) to new entry
    str x21, [x24]

    // Set state to compile mode
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    mov x1, #1
    str x1, [x0]
    // Restore VM state
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    NEXT
_colon_fail:
    mov x0, #1
    adrp x1, str_quest@page
    add x1, x1, str_quest@pageoff
    mov x2, #2
    mov x16, #4
    svc #0x80
    // Restore VM state and bail to QUIT
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    b _do_quit

// :NONAME ( -- ) start nameless colon definition; ; leaves xt
XNONAME:
    // Create DOCOL entry with empty name at HERE
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x0, [x0]
    mov x1, x0                     // new entry
    // link
    ldr x2, [x24]
    str x2, [x0], #8
    // flags|len = 0
    str xzr, [x0], #8
    // code = DOCOL
    adrp x2, DOCOL@page
    add x2, x2, DOCOL@pageoff
    str x2, [x0], #8
    // name length 0 — body begins here (already 8-aligned after code field)
    adrp x2, here_ptr@page
    add x2, x2, here_ptr@pageoff
    str x0, [x2]
    str x1, [x24]                  // LATEST = new entry
    // remember for ; to push xt
    adrp x2, noname_xt@page
    add x2, x2, noname_xt@pageoff
    str x1, [x2]
    // compile mode
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    mov x1, #1
    str x1, [x0]
    NEXT

// ; ( -- ) immediate: end colon definition; after :NONAME leaves xt
XSEMI:
    // Compile EXIT entry address
    adrp x0, dict_exit@page
    add x0, x0, dict_exit@pageoff
    bl _compile_cell
    // Set state to interpret mode
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    str xzr, [x0]
    // :NONAME → leave xt
    adrp x0, noname_xt@page
    add x0, x0, noname_xt@pageoff
    ldr x1, [x0]
    cbz x1, _semi_done
    str xzr, [x0]
    str x20, [x22, #-8]!
    mov x20, x1
_semi_done:
    NEXT

// CREATE ( "name" -- ) create dictionary entry with DOVAR code field
XCREATE:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    bl _next_word
    cbz x1, _create_fail
    mov x19, x0
    mov x20, x1
    // Warn if this name already exists
    mov x0, x19
    mov x1, x20
    bl _warn_redef
    // Get current HERE = new entry address
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x0, [x0]
    mov x21, x0
    // Write link
    ldr x1, [x24]
    str x1, [x0], #8
    // Write flags|len
    str x20, [x0], #8
    // Write code_field = DOVAR
    adrp x1, DOVAR@page
    add x1, x1, DOVAR@pageoff
    str x1, [x0], #8
    // Copy name
    mov x2, #0
_create_name_loop:
    cmp x2, x20
    b.ge _create_name_pad
    ldrb w3, [x19, x2]
    strb w3, [x0, x2]
    add x2, x2, #1
    b _create_name_loop
_create_name_pad:
    mov w3, #0
_create_pad_loop:
    tst x2, #7
    b.eq _create_name_done
    strb w3, [x0, x2]
    add x2, x2, #1
    b _create_pad_loop
_create_name_done:
    add x0, x0, x2
    // Reserve does_ip cell at body+0; user PFA starts at body+8
    str xzr, [x0], #8
    // Update HERE
    adrp x1, here_ptr@page
    add x1, x1, here_ptr@pageoff
    str x0, [x1]
    // Update latest
    str x21, [x24]
    // Restore VM state
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    NEXT
_create_fail:
    mov x0, #1
    adrp x1, str_quest@page
    add x1, x1, str_quest@pageoff
    mov x2, #2
    mov x16, #4
    svc #0x80
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    b _do_quit

// ============================================================================
// Interpreter Words
// ============================================================================
XSTATE:
    DPUSH
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    mov x20, x0
    NEXT

XBASE:
    DPUSH
    adrp x0, base_var@page
    add x0, x0, base_var@pageoff
    mov x20, x0
    NEXT

XRBRA:
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    mov x1, #1
    str x1, [x0]
    NEXT

XLBRA:
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    str xzr, [x0]
    NEXT

XBYE:
    b _quit_exit

// INCLUDE ( "filename" -- ) read and interpret a .fth file
XINCLUDE:
    // Parse filename (_next_word saves/restores x19-x20)
    bl _next_word
    cbz x1, _include_fail
    // word_scratch is already null-terminated by _next_word

    // Keep VM stable across open/read/close (temps in x25/x26, callee-saved)
    SAVE_VM
    stp x25, x26, [sp, #-16]!

    adrp x0, word_scratch@page
    add x0, x0, word_scratch@pageoff
    mov x1, #0          // O_RDONLY
    mov x2, #0          // mode
    mov x16, #5         // syscall: open
    svc #0x80
    b.cs _include_fail_restore
    mov x25, x0         // save fd

    mov x0, x25
    adrp x1, file_buffer@page
    add x1, x1, file_buffer@pageoff
    mov x2, #65536      // max bytes
    mov x16, #3         // syscall: read
    svc #0x80
    mov x26, x0         // save bytes read

    mov x0, x25
    mov x16, #6         // syscall: close
    svc #0x80

    cmp x26, #0
    b.le _include_done_restore
    adrp x0, file_buffer@page
    add x0, x0, file_buffer@pageoff
    add x0, x0, x26
    strb wzr, [x0]

_include_done_restore:
    // Nest SOURCE: push current, then switch to file (x26 = length)
    bl _push_source
    adrp x0, file_buffer@page
    add x0, x0, file_buffer@pageoff
    mov x1, x26
    cmp x1, #0
    b.ge 1f
    mov x1, #0
1:
    // x0/x1 still set — _push_source clobbers them! reload:
    adrp x0, file_buffer@page
    add x0, x0, file_buffer@pageoff
    mov x1, x26
    cmp x1, #0
    b.ge 2f
    mov x1, #0
2:
    bl _set_source
    // SOURCE-ID = 1 (text file / INCLUDE buffer; fd already closed)
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    mov x1, #1
    str x1, [x0]
    ldp x25, x26, [sp], #16
    RESTORE_VM
    NEXT

_include_fail_restore:
    ldp x25, x26, [sp], #16
    RESTORE_VM
_include_fail:
    // "can't open: <path>\n"  (word_scratch still holds the filename)
    mov x0, #1
    adrp x1, str_cant_open@page
    add x1, x1, str_cant_open@pageoff
    mov x2, #12                    // "can't open: "
    mov x16, #4
    svc #0x80
    adrp x0, word_scratch@page
    add x0, x0, word_scratch@pageoff
    bl _print_string_svc
    mov x0, #10
    bl _putchar
    b _do_quit

// ============================================================================
// High-Level Forth Support Primitives
// ============================================================================

// LATEST ( -- addr ) push address of latest_var
XLATEST:
    DPUSH
    mov x0, x24
    mov x20, x0
    NEXT

// ?DUP ( x -- x x | 0 ) dup if nonzero
XQDUP:
    cbz x20, _qdup_done
    str x20, [x22, #-8]!
_qdup_done:
    NEXT

// ['] ( "name" -- entry ) compile-only: find word and push entry address
XBRACKET_TICK:
    // Check if in compile mode
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    ldr x0, [x0]
    cbz x0, _bracket_tick_interpret
    
    // Compile mode: compile LIT + entry address
    stp x19, x20, [sp, #-16]!
    bl _next_word
    cbz x1, _bracket_tick_fail
    bl _find_word
    cbz x0, _bracket_tick_fail
    // x0 = entry address
    mov x19, x0
    // Compile LIT entry address
    adrp x0, dict_lit@page
    add x0, x0, dict_lit@pageoff
    bl _compile_cell
    // Compile the entry address
    mov x0, x19
    bl _compile_cell
    ldp x19, x20, [sp], #16
    NEXT

_bracket_tick_interpret:
    // Interpret mode: parse word and push entry address
    bl _next_word
    cbz x1, _bracket_tick_fail
    bl _find_word
    cbz x0, _bracket_tick_fail
    // x0 = entry address
    DPUSH
    mov x20, x0
    NEXT

_bracket_tick_fail:
    // Print "?" and abort
    mov x0, #1
    adrp x1, str_quest@page
    add x1, x1, str_quest@pageoff
    mov x2, #2
    mov x16, #4
    svc #0x80
    b _do_quit

// LIT-ADDR ( -- addr ) push dict_lit entry address
XLIT_ADDR:
    DPUSH
    adrp x0, dict_lit@page
    add x0, x0, dict_lit@pageoff
    mov x20, x0
    NEXT

// 0BRANCH-ADDR ( -- addr ) push dict_0branch entry address
X0BRANCH_ADDR:
    DPUSH
    adrp x0, dict_0branch@page
    add x0, x0, dict_0branch@pageoff
    mov x20, x0
    NEXT

// BRANCH-ADDR ( -- addr ) push dict_branch entry address
XBRANCH_ADDR:
    DPUSH
    adrp x0, dict_branch@page
    add x0, x0, dict_branch@pageoff
    mov x20, x0
    NEXT

// EXIT-ADDR ( -- addr ) push dict_exit entry address
XEXIT_ADDR:
    DPUSH
    adrp x0, dict_exit@page
    add x0, x0, dict_exit@pageoff
    mov x20, x0
    NEXT

// DOCON-ADDR ( -- addr ) address of DOCON code (for CONSTANT)
XDOCON_ADDR:
    DPUSH
    adrp x0, DOCON@page
    add x0, x0, DOCON@pageoff
    mov x20, x0
    NEXT

// ============================================================================
// DO / LOOP family  (R: limit index  with index on top)
// ============================================================================

// (DO) ( limit index -- )  R: -- limit index
XDO_RT:
    ldr x0, [x22], #8              // limit
    str x0, [x23, #-8]!            // R: limit
    str x20, [x23, #-8]!           // R: limit index
    ldr x20, [x22], #8
    NEXT

// (?DO) ( limit index -- )  R: -- limit index | skip loop if equal
// Inline after xt: forward branch offset (like BRANCH) used when index==limit.
XQDO_RT:
    ldr x0, [x22], #8              // limit
    cmp x20, x0
    b.eq _qdo_skip
    str x0, [x23, #-8]!            // R: limit
    str x20, [x23, #-8]!           // R: index
    ldr x20, [x22], #8
    add x19, x19, #8               // skip forward-offset cell
    NEXT
_qdo_skip:
    ldr x20, [x22], #8             // drop index
    ldr x0, [x19]
    add x19, x19, x0               // branch past LOOP/+LOOP
    NEXT

// (LOOP) ( -- )  increment index; branch by offset if not done
// LEAVE sets index=limit so first cmp exits.
XLOOP_RT:
    ldr x0, [x23], #8              // index
    ldr x1, [x23], #8              // limit
    cmp x0, x1
    b.ge _loop_done                // LEAVE or finished
    add x0, x0, #1
    cmp x0, x1
    b.eq _loop_done
    str x1, [x23, #-8]!
    str x0, [x23, #-8]!
    ldr x2, [x19]
    add x19, x19, x2
    NEXT
_loop_done:
    add x19, x19, #8               // skip offset
    NEXT

// (+LOOP) ( n -- )
XPLUSLOOP_RT:
    ldr x0, [x23], #8              // index
    ldr x1, [x23], #8              // limit
    mov x2, x20                    // step n
    ldr x20, [x22], #8
    cmp x0, x1
    b.eq _pl_done                  // LEAVE: index == limit
    mov x3, x0                     // old index
    add x0, x0, x2                 // new index
    cmp x2, #0
    b.lt _pl_neg
    // n >= 0: done if old < limit && new >= limit
    cmp x3, x1
    b.ge _pl_cont
    cmp x0, x1
    b.ge _pl_done
    b _pl_cont
_pl_neg:
    cmp x3, x1
    b.lt _pl_cont
    cmp x0, x1
    b.lt _pl_done
_pl_cont:
    str x1, [x23, #-8]!
    str x0, [x23, #-8]!
    ldr x2, [x19]
    add x19, x19, x2
    NEXT
_pl_done:
    add x19, x19, #8
    NEXT

// I ( -- n )  current loop index
XI:
    str x20, [x22, #-8]!
    ldr x20, [x23]
    NEXT

// J ( -- n )  outer loop index
XJ:
    str x20, [x22, #-8]!
    ldr x20, [x23, #16]            // skip inner index+limit
    NEXT

// UNLOOP ( -- )  R: limit index --
XUNLOOP:
    add x23, x23, #16
    NEXT

// LEAVE ( -- )  set index=limit so LOOP/+LOOP exit
XLEAVE:
    ldr x0, [x23, #8]              // limit
    str x0, [x23]                  // index = limit
    NEXT

// (DOES>) ( -- ) runtime of DOES>: patch LATEST, then EXIT defining word
XDOES_RT:
    ldr x0, [x24]                  // latest entry
    adrp x1, DODOES@page
    add x1, x1, DODOES@pageoff
    str x1, [x0, #16]              // code field = DODOES
    // body[0] = does_ip (x19 points at first word of does-clause)
    DICT_BODY_ADDR x1, x0
    str x19, [x1]
    // EXIT defining word
    RPOP
    NEXT

// DOES> ( -- ) IMMEDIATE  compile (DOES>)
XDOES:
    adrp x0, dict_does_rt@page
    add x0, x0, dict_does_rt@pageoff
    bl _compile_cell
    NEXT

// ============================================================================
// Pictured numeric output support
// ============================================================================
// PAD ( -- c-addr )
XPAD:
    str x20, [x22, #-8]!
    adrp x0, pad_buffer@page
    add x0, x0, pad_buffer@pageoff
    mov x20, x0
    NEXT

// MS@ ( -- u )  wall-clock milliseconds since Unix epoch
// Uses libc gettimeofday (stable on Darwin); not ANS MS (which is a delay).
XMSFETCH:
    SAVE_VM
    sub sp, sp, #16                // struct timeval { tv_sec, tv_usec }
    mov x0, sp
    mov x1, xzr
    bl _gettimeofday
    ldr x0, [sp]                   // tv_sec
    ldr x1, [sp, #8]               // tv_usec
    add sp, sp, #16
    RESTORE_VM
    mov x2, #1000
    mul x0, x0, x2                 // sec * 1000
    udiv x1, x1, x2                // usec / 1000
    add x0, x0, x1
    str x20, [x22, #-8]!
    mov x20, x0
    NEXT

// UNUSED ( -- u )  free bytes remaining in user_dict_area (128 KiB)
.equ USER_DICT_SIZE, 131072
XUNUSED:
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x1, [x0]                   // HERE
    adrp x0, user_dict_area@page
    add x0, x0, user_dict_area@pageoff
    mov x2, #USER_DICT_SIZE
    add x0, x0, x2                 // end of user dictionary
    subs x0, x0, x1                // free = end - HERE
    b.hs 1f
    mov x0, xzr                    // clamp if overrun
1:
    str x20, [x22, #-8]!
    mov x20, x0
    NEXT

// REDEF-WARNING ( -- addr )  VARIABLE-like; non-zero = warn on redefine
// Defaults to 0 at cold start; set TRUE (-1) when entering the user REPL.
XREDEF_WARNING:
    str x20, [x22, #-8]!
    adrp x0, redef_warn@page
    add x0, x0, redef_warn@pageoff
    mov x20, x0
    NEXT

// FILE-ECHO ( -- addr )  VARIABLE-like; non-zero = echo INCLUDE/FLOAD lines
// Defaults to 0 (OFF). Use: FILE-ECHO ON   or   FILE-ECHO OFF
XFILE_ECHO:
    str x20, [x22, #-8]!
    adrp x0, file_echo@page
    add x0, x0, file_echo@pageoff
    mov x20, x0
    NEXT

// USER-DICT ( -- addr )  start of growable user dictionary (FORGET fence)
XUSER_DICT:
    str x20, [x22, #-8]!
    adrp x0, user_dict_area@page
    add x0, x0, user_dict_area@pageoff
    mov x20, x0
    NEXT

// ============================================================================
// Stack pointer probes (for high-level DEPTH) + SPACES C, S>D 2* 2/ 2@ 2!
// ============================================================================
// Data stack grows down. Empty DSP = data_stack + 4096 (SP0).
// TOS is kept in x20; SP@ is DSP (x22). Depth cells = (SP0 - SP@) / 8.

// SP0 ( -- addr )  DSP value when the data stack is empty
XSP0:
    str x20, [x22, #-8]!
    adrp x0, data_stack@page
    add x0, x0, data_stack@pageoff
    add x0, x0, #4096
    mov x20, x0
    NEXT

// SP@ ( -- addr )  current data-stack pointer (under-TOS cells)
// Capture DSP before pushing the result (push would lower x22 by one cell).
XSPFETCH:
    mov x0, x22
    str x20, [x22, #-8]!
    mov x20, x0
    NEXT

// SP! ( addr -- )  set data-stack pointer (DSP). TOS becomes 0 (empty cache).
// Classic empty: SP0 SP!   (same as clearing the data stack)
XSPSTORE:
    mov x22, x20
    mov x20, #0
    NEXT

// SPACES ( n -- )  emit n spaces (n<=0: no-op)
XSPACES:
    mov x1, x20
    ldr x20, [x22], #8
    cmp x1, #0
    b.le _spaces_done
_spaces_loop:
    stp x1, x20, [sp, #-16]!
    str x22, [sp, #-16]!
    mov x0, #32
    bl _putchar
    ldr x22, [sp], #16
    ldp x1, x20, [sp], #16
    subs x1, x1, #1
    b.ne _spaces_loop
_spaces_done:
    NEXT

// C, ( char -- )  store char at HERE, advance HERE by 1
XCCOMMA:
    mov w0, w20
    ldr x20, [x22], #8
    adrp x1, here_ptr@page
    add x1, x1, here_ptr@pageoff
    ldr x2, [x1]
    strb w0, [x2], #1
    str x2, [x1]
    NEXT

// S>D ( n -- d )  sign-extend single to double; hi cell is TOS
XSTOD:
    str x20, [x22, #-8]!           // lo = n under
    asr x20, x20, #63              // hi = 0 or -1
    NEXT

// 2* ( x1 -- x2 )  x2 = x1 shifted left 1 (×2)
XTWOSTAR:
    lsl x20, x20, #1
    NEXT

// 2/ ( x1 -- x2 )  arithmetic shift right 1
XTWOSLASH:
    asr x20, x20, #1
    NEXT

// 2@ ( a-addr -- x1 x2 )  x1 at a-addr (lo), x2 at a-addr+cell (hi/TOS)
XTWOFETCH:
    mov x0, x20
    ldr x1, [x0]                   // lo
    ldr x20, [x0, #8]              // hi
    str x1, [x22, #-8]!
    NEXT

// 2! ( x1 x2 a-addr -- )  store x1 at a-addr, x2 at a-addr+cell
XTWOSTORE:
    mov x0, x20                    // a-addr
    ldr x2, [x22], #8              // x2 (more significant)
    ldr x1, [x22], #8              // x1 (less significant)
    ldr x20, [x22], #8
    str x1, [x0]
    str x2, [x0, #8]
    NEXT

// ============================================================================
// Double-cell arithmetic (ANS Core)
// Doubles on stack: lo under, hi in TOS (same as S>D).
// ============================================================================

// UM* ( u1 u2 -- ud )  unsigned multiply → double
XUMSTAR:
    mov x1, x20                    // u2
    ldr x0, [x22], #8              // u1
    mul x2, x0, x1                 // lo
    umulh x20, x0, x1              // hi
    str x2, [x22, #-8]!            // lo under
    NEXT

// M* ( n1 n2 -- d )  signed multiply → double
XMSTAR:
    mov x1, x20
    ldr x0, [x22], #8
    mul x2, x0, x1
    smulh x20, x0, x1
    str x2, [x22, #-8]!
    NEXT

// _udivmod128: unsigned (x1:x0) / x2 → quot x3, rem x4
// Pre: x2 != 0. If x1 >= x2 (quotient won't fit 64 bits), returns quot=-1, rem=x0.
// Invariant long division: remainder always restored to < divisor (at most one sub
// after 2*r+bit, with overflow handling when r's top bit was set).
_udivmod128:
    cbz x2, _udm_div0
    cmp x1, x2
    b.hs _udm_ovf
    mov x3, xzr                    // quot
    mov x4, xzr                    // rem
    mov x5, #128                   // bit index 127..0
_udm_bit:
    sub x5, x5, #1
    // bit = bit x5 of (x1:x0)
    cmp x5, #64
    b.hs 1f
    lsr x6, x0, x5
    b 2f
1:
    sub x7, x5, #64
    lsr x6, x1, x7
2:
    and x6, x6, #1
    // ov = rem top bit before shift
    lsr x7, x4, #63
    lsl x4, x4, #1
    orr x4, x4, x6
    lsl x3, x3, #1
    // if ov || rem >= div: rem -= div, quot |= 1
    cbnz x7, 3f
    cmp x4, x2
    b.lo 4f
3:
    sub x4, x4, x2
    orr x3, x3, #1
4:
    cbnz x5, _udm_bit
    ret
_udm_div0:
_udm_ovf:
    mov x3, #-1
    mov x4, x0
    ret

// UM/MOD ( ud u1 -- u2 u3 )  urem uquot ; ud = ulo under, uhi TOS before u1
XUMMOD:
    mov x2, x20                    // u1 divisor
    ldr x1, [x22], #8              // uhi
    ldr x0, [x22], #8              // ulo
    // prior TOS now at [x22]; compute
    stp x0, x1, [sp, #-16]!        // save dividend for clarity
    // x0,x1,x2 already set
    bl _udivmod128
    add sp, sp, #16
    // stack: push rem, TOS=quot. Prior stack item still at [x22].
    str x4, [x22, #-8]!            // rem under
    mov x20, x3                    // quot
    NEXT

// SM/REM ( d1 n1 -- n2 n3 )  symmetric (toward 0) rem, quot
// d1 = dlo under, dhi TOS before n1
XSMREM:
    mov x5, x20                    // n1 (signed divisor)
    ldr x4, [x22], #8              // dhi
    ldr x3, [x22], #8              // dlo
    // signs on stack (x6/x7 clobbered by _udivmod128)
    cmp x4, #0
    cset x6, lt                    // sign dividend
    cmp x5, #0
    cset x7, lt                    // sign divisor
    stp x6, x7, [sp, #-16]!
    str x5, [sp, #-16]!            // keep signed divisor (unused here)
    // abs dividend → x1:x0
    mov x0, x3
    mov x1, x4
    cbz x6, 1f
    mvn x0, x0
    mvn x1, x1
    adds x0, x0, #1
    adc x1, x1, xzr
1:
    mov x2, x5
    cbz x7, 2f
    neg x2, x2
2:
    cbz x2, 3f
    bl _udivmod128
    ldp x5, xzr, [sp], #16         // drop saved divisor slot
    ldp x6, x7, [sp], #16          // restore signs
    // rem sign = dividend; quot sign = xor
    cbz x6, 4f
    neg x4, x4
4:
    eor x8, x6, x7
    cbz x8, 5f
    neg x3, x3
5:
    str x4, [x22, #-8]!
    mov x20, x3
    NEXT
3:
    add sp, sp, #32
    mov x3, #-1
    mov x4, xzr
    str x4, [x22, #-8]!
    mov x20, x3
    NEXT

// FM/MOD ( d1 n1 -- n2 n3 )  floored rem, quot
// Like SM/REM then if rem!=0 and rem/divisor different signs: q--, r+=divisor
XFMMOD:
    mov x5, x20
    ldr x4, [x22], #8
    ldr x3, [x22], #8
    cmp x4, #0
    cset x6, lt
    cmp x5, #0
    cset x7, lt
    stp x6, x7, [sp, #-16]!
    str x5, [sp, #-16]!            // signed divisor for floor adjust
    mov x0, x3
    mov x1, x4
    cbz x6, 1f
    mvn x0, x0
    mvn x1, x1
    adds x0, x0, #1
    adc x1, x1, xzr
1:
    mov x2, x5
    cbz x7, 2f
    neg x2, x2
2:
    cbz x2, 9f
    bl _udivmod128
    ldr x5, [sp], #16              // divisor
    ldp x6, x7, [sp], #16          // signs
    cbz x6, 3f
    neg x4, x4
3:
    eor x8, x6, x7
    cbz x8, 4f
    neg x3, x3
4:
    cbz x4, 5f
    eor x8, x4, x5
    tbz x8, #63, 5f                // same sign → done
    sub x3, x3, #1
    add x4, x4, x5
5:
    str x4, [x22, #-8]!
    mov x20, x3
    NEXT
9:
    add sp, sp, #32
    mov x3, #-1
    mov x4, xzr
    str x4, [x22, #-8]!
    mov x20, x3
    NEXT

// CONTAINS ( hay-a hay-u ned-a ned-u -- flag )
// True if needle appears in haystack (ASCII case-insensitive).
// Empty needle => true.
// Stack: x20=ned-u, [DSP]=ned-a, [DSP+8]=hay-u, [DSP+16]=hay-a
XCONTAINS:
    mov x4, x20                    // ned-u
    ldr x3, [x22], #8              // ned-a
    ldr x2, [x22], #8              // hay-u
    ldr x1, [x22], #8              // hay-a
    // now [x22] = previous TOS; x20 still stale
    cbz x4, _cont_yes
    cmp x2, x4
    b.lo _cont_no
    sub x5, x2, x4
    add x5, x5, #1                 // positions to try
    mov x6, #0                     // i
_cont_i:
    cmp x6, x5
    b.hs _cont_no
    mov x7, #0                     // j
_cont_j:
    cmp x7, x4
    b.hs _cont_yes
    add x8, x1, x6
    add x8, x8, x7
    ldrb w9, [x8]
    ldrb w10, [x3, x7]
    cmp w9, #'a'
    b.lo 1f
    cmp w9, #'z'
    b.hi 1f
    sub w9, w9, #32
1:
    cmp w10, #'a'
    b.lo 2f
    cmp w10, #'z'
    b.hi 2f
    sub w10, w10, #32
2:
    cmp w9, w10
    b.ne _cont_next_i
    add x7, x7, #1
    b _cont_j
_cont_next_i:
    add x6, x6, #1
    b _cont_i
_cont_yes:
    // prior TOS already at [x22]; replace ned-u with flag
    mov x20, #-1
    NEXT
_cont_no:
    mov x20, #0
    NEXT

// EVALUATE ( c-addr u -- )  nest SOURCE and interpret the string
XEVALUATE:
    mov x1, x20                    // u
    ldr x0, [x22], #8              // c-addr
    ldr x20, [x22], #8
    stp x0, x1, [sp, #-16]!        // preserve across _push_source
    bl _push_source
    ldp x0, x1, [sp], #16
    bl _set_source
    // SOURCE-ID = -1 (string)
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    mov x1, #-1
    str x1, [x0]
    b _interpret_loop

// CATCH ( i*x xt -- j*x 0 | i*x n )
// R-stack frame (top first): saved_IP, saved_DSP, saved_TOS, prev_handler
// handler points at saved_IP.
XCATCH:
    mov x5, x20                    // xt
    ldr x20, [x22], #8             // pop xt → prior TOS
    adrp x7, throw_handler@page
    add x7, x7, throw_handler@pageoff
    ldr x2, [x7]
    str x2, [x23, #-8]!            // prev_handler
    str x20, [x23, #-8]!           // saved_TOS
    str x22, [x23, #-8]!           // saved_DSP
    str x19, [x23, #-8]!           // saved_IP (resume after CATCH)
    str x23, [x7]                  // handler = &saved_IP
    // Return trampoline: NEXT after xt → catch_ok entry
    adrp x0, dict_catch_ok@page
    add x0, x0, dict_catch_ok@pageoff
    adrp x1, catch_ok_cell@page
    add x1, x1, catch_ok_cell@pageoff
    str x0, [x1]
    mov x19, x1
    mov x21, x5
    ldr x1, [x5, #16]
    br x1

// Normal completion of CATCH'd xt
XCATCH_OK:
    adrp x7, throw_handler@page
    add x7, x7, throw_handler@pageoff
    ldr x1, [x7]
    cbz x1, _cok_push0
    mov x23, x1
    ldr x19, [x23], #8             // resume IP
    add x23, x23, #16              // skip DSP + TOS (keep xt results)
    ldr x0, [x23], #8              // prev_handler
    str x0, [x7]
_cok_push0:
    str x20, [x22, #-8]!
    mov x20, #0
    NEXT

// THROW ( k -- )  0 THROW is a no-op drop; nonzero restores CATCH frame
XTHROW:
    cbz x20, _throw_zero
    mov x5, x20                    // k
    adrp x7, throw_handler@page
    add x7, x7, throw_handler@pageoff
    ldr x1, [x7]
    cbz x1, _throw_abort
    mov x23, x1
    ldr x19, [x23], #8             // IP
    ldr x22, [x23], #8             // DSP
    ldr x20, [x23], #8             // TOS
    ldr x0, [x23], #8              // prev_handler
    str x0, [x7]
    str x20, [x22, #-8]!
    mov x20, x5                    // throw code
    NEXT
_throw_zero:
    ldr x20, [x22], #8
    NEXT
_throw_abort:
    // Uncaught THROW: empty data stack, then QUIT (no message here).
    adrp x22, data_stack@page
    add x22, x22, data_stack@pageoff
    add x22, x22, #4096
    mov x20, #0
    b _do_quit

// QUIT ( -- )  ANS outer interpreter entry (CODE — not a colon trampoline).
// Empty return stack, interpret state, existing prompt/line/interpret loop.
// Does not empty the data stack (ANS); ABORT clears the data stack first.
XQUIT:
    b _do_quit

// PARSE-NAME ( -- c-addr u )  ANS Core Ext
// Skip leading spaces/tabs; parse to next space/tab/newline/end.
// Result points into SOURCE (transient across next parse).
XPARSE_NAME:
    bl _cursor_load
    mov x2, x0
    bl _source_end
    mov x9, x0
_pn_skip:
    cmp x2, x9
    b.hs _pn_empty
    ldrb w4, [x2]
    cbz w4, _pn_empty
    cmp w4, #32
    b.eq _pn_sk
    cmp w4, #9
    b.eq _pn_sk
    cmp w4, #10
    b.eq _pn_sk
    cmp w4, #13
    b.eq _pn_sk
    b _pn_start
_pn_sk:
    add x2, x2, #1
    b _pn_skip
_pn_start:
    mov x3, x2
_pn_scan:
    cmp x2, x9
    b.hs _pn_end
    ldrb w4, [x2]
    cbz w4, _pn_end
    cmp w4, #32
    b.eq _pn_end
    cmp w4, #9
    b.eq _pn_end
    cmp w4, #10
    b.eq _pn_end
    cmp w4, #13
    b.eq _pn_end
    add x2, x2, #1
    b _pn_scan
_pn_end:
    sub x5, x2, x3                 // u
    // consume trailing delimiter if space-class
    cmp x2, x9
    b.hs _pn_store
    ldrb w4, [x2]
    cbz w4, _pn_store
    cmp w4, #32
    b.eq _pn_cons
    cmp w4, #9
    b.eq _pn_cons
    cmp w4, #10
    b.eq _pn_cons
    cmp w4, #13
    b.ne _pn_store
_pn_cons:
    add x2, x2, #1
_pn_store:
    mov x0, x2
    // save c-addr/u across _cursor_store
    str x3, [x23, #-8]!
    str x5, [x23, #-8]!
    bl _cursor_store
    ldr x5, [x23], #8
    ldr x3, [x23], #8
    str x20, [x22, #-8]!
    mov x20, x3
    str x20, [x22, #-8]!
    mov x20, x5
    NEXT
_pn_empty:
    mov x0, x2
    mov x3, x2                     // c-addr = end
    bl _cursor_store
    str x20, [x22, #-8]!
    mov x20, x3
    str x20, [x22, #-8]!
    mov x20, #0
    NEXT

// PARSE ( char "ccc<char>" -- c-addr u )
// From >IN to delimiter or end of SOURCE; consumes delimiter if found.
// Does not skip leading delimiters (ANS PARSE).
XPARSE:
    mov w7, w20                     // delimiter
    bl _cursor_load
    mov x9, x0                      // c-addr = start (x9 not clobbered by helpers)
    mov x3, x9
    bl _source_end
    mov x6, x0                      // end
_parse_scan:
    cmp x3, x6
    b.hs _parse_eos
    ldrb w4, [x3]
    cbz w4, _parse_eos
    cmp w4, w7
    b.eq _parse_found
    add x3, x3, #1
    b _parse_scan
_parse_found:
    sub x5, x3, x9                  // u
    add x3, x3, #1                  // skip delimiter
    mov x0, x3
    bl _cursor_store
    b _parse_push
_parse_eos:
    sub x5, x3, x9
    mov x0, x3
    bl _cursor_store
_parse_push:
    mov x20, x9
    str x20, [x22, #-8]!
    mov x20, x5
    NEXT

// WORD ( char "<chars>ccc<char>" -- c-addr )
// Skip leading delimiters, parse until delimiter, store counted string
// in word_scratch (transient). Space delimiter also skips TAB/CR/LF.
XWORD:
    mov w7, w20                     // delimiter
    bl _cursor_load
    mov x2, x0
    bl _source_end
    mov x9, x0                      // end of SOURCE
_word_skip:
    cmp x2, x9
    b.hs _word_empty
    ldrb w4, [x2]
    cbz w4, _word_empty
    cmp w7, #32
    b.ne _word_skip_exact
    cmp w4, #32
    b.eq _word_skip_adv
    cmp w4, #9
    b.eq _word_skip_adv
    cmp w4, #10
    b.eq _word_skip_adv
    cmp w4, #13
    b.eq _word_skip_adv
    b _word_start
_word_skip_exact:
    cmp w4, w7
    b.ne _word_start
_word_skip_adv:
    add x2, x2, #1
    b _word_skip
_word_start:
    mov x3, x2                      // start of token
_word_scan:
    cmp x2, x9
    b.hs _word_end
    ldrb w4, [x2]
    cbz w4, _word_end
    cmp w7, #32
    b.ne _word_scan_exact
    cmp w4, #32
    b.eq _word_end
    cmp w4, #9
    b.eq _word_end
    cmp w4, #10
    b.eq _word_end
    cmp w4, #13
    b.eq _word_end
    add x2, x2, #1
    b _word_scan
_word_scan_exact:
    cmp w4, w7
    b.eq _word_end
    add x2, x2, #1
    b _word_scan
_word_end:
    sub x5, x2, x3                  // length
    cmp x2, x9
    b.hs _word_store
    ldrb w4, [x2]
    cbz w4, _word_store
    add x2, x2, #1                  // consume delimiter
_word_store:
    // Save token start/len across _cursor_store (clobbers x0-x3)
    mov x6, x3                      // token start
    mov x7, x5                      // len
    mov x0, x2
    bl _cursor_store
    mov x3, x6
    mov x5, x7
    cmp x5, #63
    b.ls _word_len_ok
    mov x5, #63
_word_len_ok:
    adrp x6, word_scratch@page
    add x6, x6, word_scratch@pageoff
    strb w5, [x6]
    mov x1, #0
_word_copy:
    cmp x1, x5
    b.ge _word_done
    ldrb w4, [x3, x1]
    add x8, x6, #1
    strb w4, [x8, x1]
    add x1, x1, #1
    b _word_copy
_word_done:
    mov x20, x6
    NEXT
_word_empty:
    mov x0, x2
    bl _cursor_store
    adrp x6, word_scratch@page
    add x6, x6, word_scratch@pageoff
    strb wzr, [x6]
    mov x20, x6
    NEXT

// \ ( -- ) IMMEDIATE  discard rest of parse area (to end of line)
// Note: _source_end clobbers x0/x1 — keep cursor in x10.
XBACKSLASH:
    bl _cursor_load
    mov x10, x0                     // cursor
    bl _source_end
    mov x9, x0                      // end
_bs_loop:
    cmp x10, x9
    b.hs _bs_done
    ldrb w2, [x10]
    cbz w2, _bs_done
    cmp w2, #10
    b.eq _bs_done
    add x10, x10, #1
    b _bs_loop
_bs_done:
    mov x0, x10
    bl _cursor_store
    NEXT

// ( ( -- ) IMMEDIATE  paren comment; discard until ')'
XPAREN:
    bl _cursor_load
    mov x10, x0                     // cursor
    bl _source_end
    mov x9, x0                      // end
_par_loop:
    cmp x10, x9
    b.hs _par_done
    ldrb w2, [x10]
    cbz w2, _par_done
    cmp w2, #41
    b.eq _par_found
    add x10, x10, #1
    b _par_loop
_par_found:
    add x10, x10, #1
_par_done:
    mov x0, x10
    bl _cursor_store
    NEXT

// SOURCE ( -- c-addr u )  ANS
XSOURCE:
    str x20, [x22, #-8]!
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x20, [x0]
    str x20, [x22, #-8]!
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    ldr x20, [x0]
    NEXT

// SOURCE-ID ( -- 0 | -1 | fileid )  ANS
// 0 = user input device, -1 = EVALUATE string, >0 = file-ish INCLUDE buffer
XSOURCE_ID:
    str x20, [x22, #-8]!
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    ldr x20, [x0]
    NEXT

// REFILL ( -- flag )  ANS
// Terminal: read a line into input_buffer, make it SOURCE, true (false on EOF).
// EVALUATE (SOURCE-ID = -1): always false.
// INCLUDE buffer (SOURCE-ID > 0): false (whole file already in SOURCE).
XREFILL:
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    ldr x0, [x0]
    cmp x0, #0
    b.ne _refill_false
    adrp x0, input_buffer@page
    add x0, x0, input_buffer@pageoff
    mov x1, #1023
    SAVE_VM
    bl _read_line
    RESTORE_VM
    cbz x0, _refill_eof
    adrp x0, input_buffer@page
    add x0, x0, input_buffer@pageoff
    mov x1, #0
1:
    ldrb w2, [x0, x1]
    cbz w2, 2f
    add x1, x1, #1
    b 1b
2:
    bl _set_source
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    str xzr, [x0]
    str x20, [x22, #-8]!
    mov x20, #-1
    NEXT
_refill_eof:
_refill_false:
    str x20, [x22, #-8]!
    mov x20, #0
    NEXT

// ACCEPT ( c-addr +n1 -- +n2 )  ANS
// Receive a string of at most +n1 characters into c-addr; return count.
// Uses the line editor when stdin is a TTY.
XACCEPT:
    // ( c-addr +n1 )  TOS=+n1
    mov x1, x20                    // +n1
    ldr x0, [x22], #8              // c-addr; x22 -> prior TOS cell
    cmp x1, #0
    b.gt 1f
    mov x20, #0                    // +n2 = 0
    NEXT
1:
    // Save VM + args; _read_line uses x19-x26
    stp x29, x30, [sp, #-16]!
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    stp x0, x1, [sp, #-16]!        // c-addr, +n1
    mov x19, x0
    add x1, x1, #1                 // room for NUL
    mov x0, x19
    bl _read_line
    mov x2, x0                     // buf or 0
    ldp x0, x1, [sp], #16          // c-addr, +n1
    mov x3, #0                     // len
    cbz x2, 3f
2:
    cmp x3, x1
    b.hs 3f
    ldrb w4, [x2, x3]
    cbz w4, 3f
    add x3, x3, #1
    b 2b
3:
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    // x22 restored to post-c-addr-pop (prior under); TOS = n2
    mov x20, x3
    NEXT

// >NUMBER ( ud1 c-addr1 u1 -- ud2 c-addr2 u2 )  ANS
// Convert digits from string in BASE into double ud1; leave rest of string.
// ud is lo under, hi TOS (same as S>D). Character set: 0-9A-Z (case-insensitive).
XTONUMBER:
    // stack: ( udlo udhi c-addr u )  TOS=u
    mov x4, x20                    // u
    ldr x3, [x22], #8              // c-addr
    ldr x2, [x22], #8              // udhi
    ldr x1, [x22], #8              // udlo
    // BASE
    adrp x5, base_var@page
    add x5, x5, base_var@pageoff
    ldr x5, [x5]
    cmp x5, #2
    b.lo 8f
    cmp x5, #36
    b.ls 9f
8:
    mov x5, #10
9:
_tn_loop:
    cbz x4, _tn_done
    ldrb w6, [x3]
    // digit value
    sub w7, w6, #48
    cmp w7, #9
    b.ls _tn_dig
    mov w7, w6
    cmp w7, #'a'
    b.lo _tn_up
    cmp w7, #'z'
    b.hi _tn_stop
    sub w7, w7, #32
_tn_up:
    sub w7, w7, #'A'
    cmp w7, #25
    b.hi _tn_stop
    add w7, w7, #10
_tn_dig:
    cmp x7, x5
    b.hs _tn_stop
    // ud = ud * base + digit  (128-bit)
    // (x2:x1) * x5 + x7
    mul x8, x1, x5                 // lo*base low
    umulh x9, x1, x5               // lo*base high
    mul x10, x2, x5                // hi*base low (ignore hi*base high overflow)
    add x9, x9, x10
    adds x1, x8, x7
    adc x2, x9, xzr
    add x3, x3, #1
    sub x4, x4, #1
    b _tn_loop
_tn_stop:
_tn_done:
    // push udlo udhi c-addr u
    str x1, [x22, #-8]!
    str x2, [x22, #-8]!
    str x3, [x22, #-8]!
    mov x20, x4
    NEXT

// ENVIRONMENT? ( c-addr u -- false | i*x true )  ANS
// Recognized queries (minimal Core set + a few useful ones):
//   /COUNTED-STRING  ADDRESS-UNIT-BITS  CORE  CORE-EXT  FLOORED
//   MAX-CHAR  MAX-N  MAX-U  RETURN-STACK-CELLS  STACK-CELLS
XENVIRONMENT_Q:
    mov x1, x20                    // u
    ldr x0, [x22], #8              // c-addr
    // x0/x1 = query string; scan env_name_ptrs table
    mov x4, #0                     // index
_env_next:
    // load name pointer and length from table: each entry is .quad ptr, .quad len, then next
    // Simpler: fixed table of asciz names, parallel values
    cmp x4, #10                    // ENV_COUNT
    b.hs _env_no
    // name at env_name_ptrs[x4]
    adrp x5, env_name_ptrs@page
    add x5, x5, env_name_ptrs@pageoff
    ldr x5, [x5, x4, lsl #3]
    // strlen name
    mov x6, #0
1:
    ldrb w7, [x5, x6]
    cbz w7, 2f
    add x6, x6, #1
    b 1b
2:
    cmp x6, x1
    b.ne _env_cont
    // compare bytes case-sensitive (ANS names are uppercase)
    mov x7, #0
3:
    cmp x7, x6
    b.eq _env_yes
    ldrb w8, [x5, x7]
    ldrb w9, [x0, x7]
    cmp w8, w9
    b.ne _env_cont
    add x7, x7, #1
    b 3b
_env_cont:
    add x4, x4, #1
    b _env_next
_env_yes:
    // value kind in env_kinds[x4]: 0 = flag true only, 1 = single cell then true
    adrp x5, env_kinds@page
    add x5, x5, env_kinds@pageoff
    ldrb w5, [x5, x4]
    adrp x6, env_values@page
    add x6, x6, env_values@pageoff
    ldr x6, [x6, x4, lsl #3]
    cbz w5, _env_flag_only
    // push value, then true
    str x6, [x22, #-8]!
    mov x20, #-1
    NEXT
_env_flag_only:
    // boolean query: value is the flag (-1 present / 0 absent)
    mov x20, x6
    NEXT
_env_no:
    mov x20, #0
    NEXT

// >IN ( -- a-addr )  ANS variable
XTOIN:
    str x20, [x22, #-8]!
    adrp x0, to_in_var@page
    add x0, x0, to_in_var@pageoff
    mov x20, x0
    NEXT

// (S") ( -- c-addr u )  runtime for compiled S" / ."
// In-line layout at IP:  cell len, then len bytes, then pad to 8.
XSLIT:
    ldr x0, [x19], #8               // length
    str x20, [x22, #-8]!
    mov x20, x19                    // c-addr of string bytes
    str x20, [x22, #-8]!
    mov x20, x0                     // u
    add x19, x19, x0
    add x19, x19, #7
    bic x19, x19, #7
    NEXT

// S" ( -- c-addr u | compile-time ) IMMEDIATE
// Parse is fully inlined so we never clobber VM regs via nested helpers.
XSQUOTE:
    // --- skip blanks; parse to " ---
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x9, [x0]                    // SOURCE base
    adrp x0, to_in_var@page
    add x0, x0, to_in_var@pageoff
    mov x10, x0                     // & >IN
    ldr x11, [x10]                  // >IN
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    ldr x12, [x0]                   // SOURCE len
    add x1, x9, x11                 // cursor
    add x6, x9, x12                 // end
_sq_skip:
    cmp x1, x6
    b.hs _sq_body0
    ldrb w2, [x1]
    cmp w2, #32
    b.eq _sq_sk1
    cmp w2, #9
    b.ne _sq_body0
_sq_sk1:
    add x1, x1, #1
    b _sq_skip
_sq_body0:
    mov x2, x1                      // c-addr
_sq_scan:
    cmp x1, x6
    b.hs _sq_eos
    ldrb w3, [x1]
    cbz w3, _sq_eos
    cmp w3, #34
    b.eq _sq_found
    add x1, x1, #1
    b _sq_scan
_sq_found:
    sub x5, x1, x2                  // u
    add x1, x1, #1
    b _sq_commit
_sq_eos:
    sub x5, x1, x2
_sq_commit:
    sub x11, x1, x9
    str x11, [x10]                  // >IN
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    str x1, [x0]
    // x2=c-addr, x5=u  (x9-x12 free again except we keep x2,x5)
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    ldr x0, [x0]
    cbnz x0, _sq_comp
    // interpret: ( c-addr u )
    str x20, [x22, #-8]!
    mov x20, x2
    str x20, [x22, #-8]!
    mov x20, x5
    NEXT
_sq_comp:
    // Compile (S") , len , bytes , align.  x2=c-addr x5=u; save IP on R stack.
    str x19, [x23, #-8]!            // RPUSH IP
    str x2, [x23, #-8]!             // save c-addr
    str x5, [x23, #-8]!             // save u
    adrp x0, dict_slit@page
    add x0, x0, dict_slit@pageoff
    bl _compile_cell
    ldr x0, [x23]                   // peek u
    bl _compile_cell
    // copy u bytes from c-addr to HERE
    ldr x5, [x23], #8               // pop u
    ldr x2, [x23], #8               // pop c-addr
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x1, [x0]                    // dest
    mov x3, #0
_sq_cpy:
    cmp x3, x5
    b.ge _sq_al
    ldrb w4, [x2, x3]
    strb w4, [x1, x3]
    add x3, x3, #1
    b _sq_cpy
_sq_al:
    add x1, x1, x5
    add x1, x1, #7
    bic x1, x1, #7
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    str x1, [x0]
    ldr x19, [x23], #8              // RPOP IP
    NEXT

// (C") ( -- c-addr )  runtime: counted string inline at IP
// Layout: len byte, chars, pad to 8-byte boundary.
XCSTR:
    str x20, [x22, #-8]!
    mov x20, x19                   // c-addr of counted string
    ldrb w0, [x19]
    add x19, x19, x0
    add x19, x19, #1
    add x19, x19, #7
    bic x19, x19, #7
    NEXT

// C" ( -- c-addr ) IMMEDIATE  ANS counted string
// Interpret: counted copy in PAD. Compile: (C") + counted bytes + align.
XCQUOTE:
    // Parse to " (same style as S")
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x9, [x0]
    adrp x0, to_in_var@page
    add x0, x0, to_in_var@pageoff
    mov x10, x0
    ldr x11, [x10]
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    ldr x12, [x0]
    add x1, x9, x11
    add x6, x9, x12
_cq_skip:
    cmp x1, x6
    b.hs _cq_body
    ldrb w2, [x1]
    cmp w2, #32
    b.eq _cq_sk1
    cmp w2, #9
    b.ne _cq_body
_cq_sk1:
    add x1, x1, #1
    b _cq_skip
_cq_body:
    mov x2, x1
_cq_scan:
    cmp x1, x6
    b.hs _cq_eos
    ldrb w3, [x1]
    cbz w3, _cq_eos
    cmp w3, #34
    b.eq _cq_found
    add x1, x1, #1
    b _cq_scan
_cq_found:
    sub x5, x1, x2
    add x1, x1, #1
    b _cq_commit
_cq_eos:
    sub x5, x1, x2
_cq_commit:
    sub x11, x1, x9
    str x11, [x10]
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    str x1, [x0]
    cmp x5, #255
    b.ls _cq_lenok
    mov x5, #255
_cq_lenok:
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    ldr x0, [x0]
    cbnz x0, _cq_comp
    // interpret → PAD counted string
    adrp x0, pad_buffer@page
    add x0, x0, pad_buffer@pageoff
    strb w5, [x0]
    mov x3, #0
1:
    cmp x3, x5
    b.ge 2f
    ldrb w4, [x2, x3]
    add x6, x0, #1
    strb w4, [x6, x3]
    add x3, x3, #1
    b 1b
2:
    str x20, [x22, #-8]!
    mov x20, x0
    NEXT
_cq_comp:
    str x19, [x23, #-8]!
    str x2, [x23, #-8]!
    str x5, [x23, #-8]!
    adrp x0, dict_cstr@page
    add x0, x0, dict_cstr@pageoff
    bl _compile_cell
    ldr x5, [x23], #8
    ldr x2, [x23], #8
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x1, [x0]
    strb w5, [x1], #1
    mov x3, #0
3:
    cmp x3, x5
    b.ge 4f
    ldrb w4, [x2, x3]
    strb w4, [x1, x3]
    add x3, x3, #1
    b 3b
4:
    add x1, x1, x5
    add x1, x1, #7
    bic x1, x1, #7
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    str x1, [x0]
    ldr x19, [x23], #8
    NEXT

// S\" ( -- c-addr u ) IMMEDIATE  ANS escaped string
// Escapes: \a \b \e \f \l \m \n \q \r \t \v \z \" \\ \xHH
// Interpret: expand into slit_esc_buf. Compile: (S") + expanded bytes.
XSESCAPE:
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x9, [x0]
    adrp x0, to_in_var@page
    add x0, x0, to_in_var@pageoff
    mov x10, x0
    ldr x11, [x10]
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    ldr x12, [x0]
    add x1, x9, x11                // cursor
    add x6, x9, x12                // end
_se_skip:
    cmp x1, x6
    b.hs _se_body
    ldrb w2, [x1]
    cmp w2, #32
    b.eq _se_sk1
    cmp w2, #9
    b.ne _se_body
_se_sk1:
    add x1, x1, #1
    b _se_skip
_se_body:
    // Expand into slit_esc_buf (max 255)
    adrp x7, slit_esc_buf@page
    add x7, x7, slit_esc_buf@pageoff
    mov x5, #0                     // out len
_se_loop:
    cmp x1, x6
    b.hs _se_done
    ldrb w2, [x1]
    cbz w2, _se_done
    cmp w2, #34                    // "
    b.eq _se_endq
    cmp w2, #92                    // backslash
    b.eq _se_esc
    // ordinary char
    cmp x5, #255
    b.hs _se_adv
    strb w2, [x7, x5]
    add x5, x5, #1
_se_adv:
    add x1, x1, #1
    b _se_loop
_se_endq:
    add x1, x1, #1
    b _se_done
_se_esc:
    add x1, x1, #1
    cmp x1, x6
    b.hs _se_done
    ldrb w2, [x1]
    add x1, x1, #1
    // decode escape in w2 → w3 (char), or multi for \m \x
    cmp w2, #'a'
    b.eq _se_a
    cmp w2, #'b'
    b.eq _se_b
    cmp w2, #'e'
    b.eq _se_e
    cmp w2, #'f'
    b.eq _se_f
    cmp w2, #'l'
    b.eq _se_l
    cmp w2, #'m'
    b.eq _se_m
    cmp w2, #'n'
    b.eq _se_n
    cmp w2, #'q'
    b.eq _se_q
    cmp w2, #'r'
    b.eq _se_r
    cmp w2, #'t'
    b.eq _se_t
    cmp w2, #'v'
    b.eq _se_v
    cmp w2, #'z'
    b.eq _se_z
    cmp w2, #'"'
    b.eq _se_qq
    cmp w2, #'\\'
    b.eq _se_bs
    cmp w2, #'x'
    b.eq _se_hex
    // unknown: emit the char after backslash
    mov w3, w2
    b _se_put1
_se_a:  mov w3, #7
    b _se_put1
_se_b:  mov w3, #8
    b _se_put1
_se_e:  mov w3, #27
    b _se_put1
_se_f:  mov w3, #12
    b _se_put1
_se_l:  mov w3, #10
    b _se_put1
_se_n:  mov w3, #10
    b _se_put1
_se_q:  mov w3, #34
    b _se_put1
_se_r:  mov w3, #13
    b _se_put1
_se_t:  mov w3, #9
    b _se_put1
_se_v:  mov w3, #11
    b _se_put1
_se_z:  mov w3, #0
    b _se_put1
_se_qq: mov w3, #34
    b _se_put1
_se_bs: mov w3, #92
    b _se_put1
_se_m:
    // CR LF
    cmp x5, #254
    b.hs _se_loop
    mov w3, #13
    strb w3, [x7, x5]
    add x5, x5, #1
    mov w3, #10
    strb w3, [x7, x5]
    add x5, x5, #1
    b _se_loop
_se_hex:
    // \xHH — two hex digits
    mov w3, #0
    mov x4, #2
_se_hx:
    cbz x4, _se_put1
    cmp x1, x6
    b.hs _se_put1
    ldrb w2, [x1]
    // hex value
    sub w8, w2, #48
    cmp w8, #9
    b.ls _se_hd
    sub w8, w2, #'A'
    cmp w8, #5
    b.ls _se_hu
    sub w8, w2, #'a'
    cmp w8, #5
    b.hi _se_put1
    add w8, w8, #10
    b _se_hok
_se_hu:
    add w8, w8, #10
    b _se_hok
_se_hd:
_se_hok:
    add x1, x1, #1
    lsl w3, w3, #4
    orr w3, w3, w8
    sub x4, x4, #1
    b _se_hx
_se_put1:
    cmp x5, #255
    b.hs _se_loop
    strb w3, [x7, x5]
    add x5, x5, #1
    b _se_loop
_se_done:
    sub x11, x1, x9
    str x11, [x10]
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    str x1, [x0]
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    ldr x0, [x0]
    cbnz x0, _se_comp
    // interpret: ( c-addr u ) pointing at slit_esc_buf
    str x20, [x22, #-8]!
    mov x20, x7
    str x20, [x22, #-8]!
    mov x20, x5
    NEXT
_se_comp:
    str x19, [x23, #-8]!
    str x7, [x23, #-8]!            // buf
    str x5, [x23, #-8]!            // u
    adrp x0, dict_slit@page
    add x0, x0, dict_slit@pageoff
    bl _compile_cell
    ldr x0, [x23]                  // peek u
    bl _compile_cell
    ldr x5, [x23], #8
    ldr x2, [x23], #8
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x1, [x0]
    mov x3, #0
1:
    cmp x3, x5
    b.ge 2f
    ldrb w4, [x2, x3]
    strb w4, [x1, x3]
    add x3, x3, #1
    b 1b
2:
    add x1, x1, x5
    add x1, x1, #7
    bic x1, x1, #7
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    str x1, [x0]
    ldr x19, [x23], #8
    NEXT

// SAVE-INPUT ( -- xn ... x1 n )
// Saves SOURCE addr, len, >IN, SOURCE-ID; n=4.
XSAVE_INPUT:
    str x20, [x22, #-8]!
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x20, [x0]
    str x20, [x22, #-8]!
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    ldr x20, [x0]
    str x20, [x22, #-8]!
    adrp x0, to_in_var@page
    add x0, x0, to_in_var@pageoff
    ldr x20, [x0]
    str x20, [x22, #-8]!
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    ldr x20, [x0]
    str x20, [x22, #-8]!
    mov x20, #4
    NEXT

// RESTORE-INPUT ( xn ... x1 n -- flag )
// flag true (-1) = cannot restore; false (0) = ok.
// Expects n=4 and (addr len >in id 4).
XRESTORE_INPUT:
    // TOS = n
    cmp x20, #4
    b.ne _ri_fail
    ldr x0, [x22], #8              // source_id
    ldr x1, [x22], #8              // >IN
    ldr x2, [x22], #8              // len
    ldr x3, [x22], #8              // addr
    ldr x20, [x22], #8             // prior under
    adrp x4, source_addr@page
    add x4, x4, source_addr@pageoff
    str x3, [x4]
    adrp x4, source_len@page
    add x4, x4, source_len@pageoff
    str x2, [x4]
    adrp x4, to_in_var@page
    add x4, x4, to_in_var@pageoff
    str x1, [x4]
    adrp x4, source_id_var@page
    add x4, x4, source_id_var@pageoff
    str x0, [x4]
    // word_cursor = source + >IN
    add x3, x3, x1
    adrp x4, word_cursor@page
    add x4, x4, word_cursor@pageoff
    str x3, [x4]
    // success flag 0
    str x20, [x22, #-8]!
    mov x20, #0
    NEXT
_ri_fail:
    // drop n cells under n? We only know n from TOS; drop n items + replace with true
    mov x1, x20                    // n
    ldr x20, [x22], #8
1:
    cbz x1, 2f
    ldr x20, [x22], #8
    sub x1, x1, #1
    b 1b
2:
    str x20, [x22, #-8]!
    mov x20, #-1
    NEXT

// ." ( -- ) IMMEDIATE
XDOTQ:
    // Reuse S" logic by calling the same parse, then TYPE or compile TYPE
    // Implement by branching into shared structure via stack trick:
    // For simplicity, duplicate parse (same as S") then diverge.
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x9, [x0]
    adrp x0, to_in_var@page
    add x0, x0, to_in_var@pageoff
    mov x10, x0
    ldr x11, [x10]
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    ldr x12, [x0]
    add x1, x9, x11
    add x6, x9, x12
_dq_skip:
    cmp x1, x6
    b.hs _dq_body0
    ldrb w2, [x1]
    cmp w2, #32
    b.eq _dq_sk1
    cmp w2, #9
    b.ne _dq_body0
_dq_sk1:
    add x1, x1, #1
    b _dq_skip
_dq_body0:
    mov x2, x1
_dq_scan:
    cmp x1, x6
    b.hs _dq_eos
    ldrb w3, [x1]
    cbz w3, _dq_eos
    cmp w3, #34
    b.eq _dq_found
    add x1, x1, #1
    b _dq_scan
_dq_found:
    sub x5, x1, x2
    add x1, x1, #1
    b _dq_commit
_dq_eos:
    sub x5, x1, x2
_dq_commit:
    sub x11, x1, x9
    str x11, [x10]
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    str x1, [x0]
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    ldr x0, [x0]
    cbnz x0, _dq_comp
    // interpret: write string to stdout
    mov x1, x2
    mov x2, x5
    cbz x2, _dq_out
    mov x0, #1
    mov x16, #4
    svc #0x80
_dq_out:
    NEXT
_dq_comp:
    str x19, [x23, #-8]!
    str x2, [x23, #-8]!
    str x5, [x23, #-8]!
    adrp x0, dict_slit@page
    add x0, x0, dict_slit@pageoff
    bl _compile_cell
    ldr x0, [x23]
    bl _compile_cell
    ldr x5, [x23], #8
    ldr x2, [x23], #8
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    ldr x1, [x0]
    mov x3, #0
_dq_cpy:
    cmp x3, x5
    b.ge _dq_al
    ldrb w4, [x2, x3]
    strb w4, [x1, x3]
    add x3, x3, #1
    b _dq_cpy
_dq_al:
    add x1, x1, x5
    add x1, x1, #7
    bic x1, x1, #7
    adrp x0, here_ptr@page
    add x0, x0, here_ptr@pageoff
    str x1, [x0]
    adrp x0, dict_type@page
    add x0, x0, dict_type@pageoff
    bl _compile_cell
    ldr x19, [x23], #8
    NEXT

// _skip_blanks: advance >IN over spaces/tabs (not newlines)
_skip_blanks:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    bl _cursor_load
    mov x1, x0
    bl _source_end
    mov x9, x0
_sb_loop:
    cmp x1, x9
    b.hs _sb_done
    ldrb w2, [x1]
    cmp w2, #32
    b.eq _sb_adv
    cmp w2, #9
    b.eq _sb_adv
    b _sb_done
_sb_adv:
    add x1, x1, #1
    b _sb_loop
_sb_done:
    mov x0, x1
    bl _cursor_store
    ldp x29, x30, [sp], #16
    ret

// _parse_quote: w7=delim -> x2=c-addr, x5=u, advances >IN
_parse_quote:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    bl _cursor_load
    mov x21, x0                     // start (callee-saved)
    mov x3, x0
    bl _source_end
    mov x6, x0
_pq_scan:
    cmp x3, x6
    b.hs _pq_eos
    ldrb w4, [x3]
    cbz w4, _pq_eos
    cmp w4, w7
    b.eq _pq_found
    add x3, x3, #1
    b _pq_scan
_pq_found:
    sub x22, x3, x21                // u
    add x3, x3, #1
    mov x0, x3
    bl _cursor_store
    b _pq_out
_pq_eos:
    sub x22, x3, x21
    mov x0, x3
    bl _cursor_store
_pq_out:
    mov x2, x21                     // c-addr
    mov x5, x22                     // u
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _compile_slit: x2=c-addr, x5=u — compile (S") + len + bytes + align
_compile_slit:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    mov x19, x2                     // src
    mov x20, x5                     // len
    adrp x0, dict_slit@page
    add x0, x0, dict_slit@pageoff
    bl _compile_cell
    mov x0, x20
    bl _compile_cell
    // copy bytes to HERE
    adrp x1, here_ptr@page
    add x1, x1, here_ptr@pageoff
    ldr x21, [x1]                   // dest
    mov x2, #0
_cs_copy:
    cmp x2, x20
    b.ge _cs_pad
    ldrb w3, [x19, x2]
    strb w3, [x21, x2]
    add x2, x2, #1
    b _cs_copy
_cs_pad:
    add x21, x21, x20
    // align HERE to 8
    add x21, x21, #7
    bic x21, x21, #7
    adrp x1, here_ptr@page
    add x1, x1, here_ptr@pageoff
    str x21, [x1]
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// ============================================================================
// QUIT - Outer Interpreter
// ============================================================================
.align 4
_do_quit:
    // Empty return stack; clear CATCH nesting
    adrp x23, return_stack@page
    add  x23, x23, return_stack@pageoff
    add  x23, x23, #2048
    adrp x0, throw_handler@page
    add  x0, x0, throw_handler@pageoff
    str  xzr, [x0]
    // Interpret state
    adrp x0, state_var@page
    add  x0, x0, state_var@pageoff
    str  xzr, [x0]
    // Pop any nested SOURCE (EVALUATE / INCLUDE) back to base
    adrp x0, source_sp@page
    add  x0, x0, source_sp@pageoff
    str  xzr, [x0]
    // Terminal is the input source
    adrp x0, source_id_var@page
    add  x0, x0, source_id_var@pageoff
    str  xzr, [x0]

_quit_loop:
    // Once after bootstrap: REDEF-WARNING ON, and clear data stack (init
    // may leave residual cells). Do not clear on later prompts — stack persists.
    adrp x0, redef_boot_done@page
    add x0, x0, redef_boot_done@pageoff
    ldr x1, [x0]
    cbnz x1, 1f
    mov x1, #1
    str x1, [x0]
    adrp x0, redef_warn@page
    add x0, x0, redef_warn@pageoff
    mov x1, #-1
    str x1, [x0]
    adrp x22, data_stack@page
    add x22, x22, data_stack@pageoff
    add x22, x22, #4096
    mov x20, #0
1:
    // Refresh fault recovery point (siglongjmp lands here after SIGSEGV/SIGBUS)
    adrp x0, quit_jmpbuf@page
    add x0, x0, quit_jmpbuf@pageoff
    mov x1, #1                     // save signal mask
    bl _sigsetjmp
    cbz x0, 2f
    // Returned from fault handler: rebuild a clean outer-interpreter state
    adrp x22, data_stack@page
    add x22, x22, data_stack@pageoff
    add x22, x22, #4096
    mov x20, #0
    adrp x23, return_stack@page
    add x23, x23, return_stack@pageoff
    add x23, x23, #2048
    adrp x0, throw_handler@page
    add x0, x0, throw_handler@pageoff
    str xzr, [x0]
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    str xzr, [x0]
    adrp x0, source_sp@page
    add x0, x0, source_sp@pageoff
    str xzr, [x0]
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    str xzr, [x0]
    adrp x24, latest_var@page
    add x24, x24, latest_var@pageoff
2:
    // Print prompt via raw SVC
    mov x0, #1
    adrp x1, str_prompt@page
    add x1, x1, str_prompt@pageoff
    mov x2, #5
    mov x16, #4
    svc #0x80

    // Read line (line editor; maxlen leaves room for NUL)
    adrp x0, input_buffer@page
    add  x0, x0, input_buffer@pageoff
    mov  x1, #1023
    bl   _read_line
    cbz  x0, _quit_exit

    // SOURCE = input_buffer, length = strlen, >IN = 0
    adrp x0, input_buffer@page
    add  x0, x0, input_buffer@pageoff
    mov x1, #0
1:
    ldrb w2, [x0, x1]
    cbz w2, 2f
    add x1, x1, #1
    b 1b
2:
    bl _set_source
    // User input device
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    str xzr, [x0]

_interpret_loop:
    // Between words: catch underflow/overflow from the previous word
    bl _check_stack

    // When FILE-ECHO is on and SOURCE is an INCLUDE buffer, echo source
    // lines up through the current parse position before the next word.
    bl _file_echo_upto_cursor

    bl _next_word
    cbz x1, _interpret_empty

    // Save word addr and len on return stack (caller-saved x2/x3 will be clobbered)
    str x0, [x23, #-8]!    // push word addr
    str x1, [x23, #-8]!    // push word len

    // Try number
    bl _parse_number
    cbz x0, _try_find

    // Pop saved values from return stack (not needed, just clean up)
    add x23, x23, #16

    // x1 = value. Compile mode?
    adrp x2, state_var@page
    add x2, x2, state_var@pageoff
    ldr x2, [x2]
    cbnz x2, _compile_lit

    DPUSH
    mov x20, x1
    b _interpret_loop

_compile_lit:
    // x1 = literal value, compile LIT entry address then value
    // Save value on return stack (bl will clobber x0-x3)
    str x1, [x23, #-8]!
    // Compile LIT entry address
    adrp x0, dict_lit@page
    add x0, x0, dict_lit@pageoff
    bl _compile_cell
    // Compile the literal value
    ldr x0, [x23], #8
    bl _compile_cell
    b _interpret_loop

_try_find:
    // Restore word addr and len from return stack
    ldr x1, [x23], #8      // pop len
    ldr x0, [x23], #8      // pop addr
    bl _find_word
    cbz x0, _word_not_found

    mov x2, x0
    mov x3, x1

    ldr x5, [x2, #16]

    // Immediate?
    tst x3, #0x100
    b.ne _exec_found

    // Compile mode?
    adrp x6, state_var@page
    add x6, x6, state_var@pageoff
    ldr x6, [x6]
    cbnz x6, _compile_entry

_exec_found:
    // Compute dict_restart address at runtime (avoids broken .quad relocation)
    adrp x19, dict_restart@page
    add  x19, x19, dict_restart@pageoff
    // Compute XRESTART address and store in dict_restart+16 (code field)
    adrp x1, XRESTART@page
    add  x1, x1, XRESTART@pageoff
    str  x1, [x19, #16]
    // Store dict_restart address in restart_cell
    adrp x1, restart_cell@page
    add  x1, x1, restart_cell@pageoff
    str  x19, [x1]
    // Set x19 to point to restart_cell (IP register for NEXT)
    mov  x19, x1
    mov x21, x2
    // Crash diagnostic: save x5 (code field ptr), dict_restart addr, XRESTART addr to next_diag
    adrp x1, next_diag@page
    add  x1, x1, next_diag@pageoff
    str  x5, [x1]             // next_diag+0 = code field value
    str  x19, [x1, #8]        // next_diag+8 = restart_cell ptr (x19 after mov)
    str  x22, [x1, #16]       // next_diag+16 = DSP (x22)
    str  x20, [x1, #24]       // next_diag+24 = TOS (x20)
    br x5

_compile_entry:
    mov x0, x2
    bl _compile_cell
    b _interpret_loop

_word_not_found:
    // "undefined: <word>\n"
    mov x0, #1
    adrp x1, str_undefined@page
    add x1, x1, str_undefined@pageoff
    mov x2, #11                    // "undefined: "
    mov x16, #4
    svc #0x80
    adrp x0, word_scratch@page
    add x0, x0, word_scratch@pageoff
    bl _print_string_svc
    mov x0, #10
    bl _putchar
    b _error_abandon

// Data-stack check between outer-interpreter words (not inside primitives).
// Stack grows down; empty DSP = data_stack+4096. Underflow if DSP > SP0.
// Also reject DSP below data_stack (overflow into other BSS).
_check_stack:
    adrp x0, data_stack@page
    add x0, x0, data_stack@pageoff
    add x1, x0, #4096              // SP0
    cmp x22, x1
    b.hi _stack_underflow          // DSP above empty → underflowed
    cmp x22, x0
    b.lo _stack_overflow           // DSP below buffer → overflow
    ret

_stack_underflow:
    mov x0, #1
    adrp x1, str_underflow@page
    add x1, x1, str_underflow@pageoff
    mov x2, #16                    // "stack underflow\n"
    mov x16, #4
    svc #0x80
    b _stack_reset_abandon

_stack_overflow:
    mov x0, #1
    adrp x1, str_overflow@page
    add x1, x1, str_overflow@pageoff
    mov x2, #15                    // "stack overflow\n"
    mov x16, #4
    svc #0x80
_stack_reset_abandon:
    adrp x22, data_stack@page
    add x22, x22, data_stack@pageoff
    add x22, x22, #4096
    mov x20, #0
    b _error_abandon

// Shared: leave interpret, abandon rest of SOURCE, finish line
_error_abandon:
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    str xzr, [x0]
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    ldr x0, [x0]
    adrp x1, to_in_var@page
    add x1, x1, to_in_var@pageoff
    str x0, [x1]
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x0, [x0]
    adrp x1, source_len@page
    add x1, x1, source_len@pageoff
    ldr x1, [x1]
    add x0, x0, x1
    adrp x1, word_cursor@page
    add x1, x1, word_cursor@pageoff
    str x0, [x1]
    b _interpret_empty

// End of current SOURCE: pop nested source (INCLUDE/EVALUATE) or finish line
_interpret_empty:
    bl _pop_source
    cbnz x0, _interpret_loop       // restored outer SOURCE — keep going
_interpret_done:
    // Print " ok" via SVC
    mov x0, #1
    adrp x1, str_ok@page
    add x1, x1, str_ok@pageoff
    mov x2, #4
    mov x16, #4
    svc #0x80
    b _quit_loop

_quit_exit:
    // Print "Bye!" via SVC
    mov x0, #1
    adrp x1, str_bye@page
    add x1, x1, str_bye@pageoff
    mov x2, #5
    mov x16, #4
    svc #0x80
    mov x0, #0
    mov x16, #1
    svc #0x80

// ============================================================================
// C Helper Functions (assembly)
// ============================================================================

// _set_source: x0=c-addr, x1=u  — establish SOURCE / >IN=0
_set_source:
    adrp x2, source_addr@page
    add x2, x2, source_addr@pageoff
    str x0, [x2]
    adrp x2, source_len@page
    add x2, x2, source_len@pageoff
    str x1, [x2]
    adrp x2, to_in_var@page
    add x2, x2, to_in_var@pageoff
    str xzr, [x2]
    adrp x2, word_cursor@page
    add x2, x2, word_cursor@pageoff
    str x0, [x2]
    // Reset FILE-ECHO scan so the new SOURCE echoes from its start
    adrp x2, file_echo_pos@page
    add x2, x2, file_echo_pos@pageoff
    str x0, [x2]
    ret

// _file_echo_upto_cursor: if FILE-ECHO nonzero and SOURCE-ID > 0 (INCLUDE),
// write any not-yet-echoed source text through the end of the line that
// contains the next non-whitespace character (lookahead from word_cursor).
// That way blank lines skipped by the parser are still echoed.
// Tracks progress in file_echo_pos (absolute address).
// Safe to call with any VM regs live; uses only x0-x4/x16 (+ frame).
_file_echo_upto_cursor:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    // FILE-ECHO off?
    adrp x0, file_echo@page
    add x0, x0, file_echo@pageoff
    ldr x0, [x0]
    cbz x0, _fe_done
    // Only for INCLUDE / file-ish buffers (SOURCE-ID > 0)
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    ldr x0, [x0]
    cmp x0, #0
    b.le _fe_done
    // source base / end
    adrp x1, source_addr@page
    add x1, x1, source_addr@pageoff
    ldr x1, [x1]                   // x1 = source base
    adrp x2, source_len@page
    add x2, x2, source_len@pageoff
    ldr x2, [x2]
    add x2, x1, x2                 // x2 = source end
    // cursor = word_cursor, clamped
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    ldr x0, [x0]
    cmp x0, x1
    csel x0, x1, x0, lo
    cmp x0, x2
    csel x0, x2, x0, hi
    // Lookahead: skip whitespace to next token (or end)
1:
    cmp x0, x2
    b.hs 2f
    ldrb w3, [x0]
    cbz w3, 2f
    cmp w3, #32
    b.eq 3f
    cmp w3, #10
    b.eq 3f
    cmp w3, #9
    b.eq 3f
    b 2f                           // non-ws: target found
3:
    add x0, x0, #1
    b 1b
2:
    // x0 = target (next token or end). Find end of that line.
    mov x3, x0                     // x3 = line_end scan
4:
    cmp x3, x2
    b.hs 5f
    ldrb w4, [x3]
    cbz w4, 5f
    cmp w4, #10
    b.eq 5f
    add x3, x3, #1
    b 4b
5:
    // x1 = pos (file_echo_pos), clamp into SOURCE
    adrp x4, file_echo_pos@page
    add x4, x4, file_echo_pos@pageoff
    ldr x0, [x4]                   // x0 = pos (reuse x0; target no longer needed)
    adrp x1, source_addr@page
    add x1, x1, source_addr@pageoff
    ldr x1, [x1]
    cmp x0, x1
    csel x0, x1, x0, lo
    cmp x0, x2
    csel x0, x2, x0, hi
    // if pos > line_end, already echoed through this line
    cmp x0, x3
    b.hi _fe_done
    // write [pos, line_end): x0=pos, x3=line_end
    mov x1, x0                     // buf = pos
    subs x2, x3, x1                // len = line_end - pos
    b.eq 6f
    mov x0, #1                     // stdout
    mov x16, #4
    svc #0x80
6:
    // If line ends with \n, print it and advance past; else add \n for display
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x0, [x0]
    adrp x1, source_len@page
    add x1, x1, source_len@pageoff
    ldr x1, [x1]
    add x0, x0, x1                 // source end
    cmp x3, x0
    b.hs 7f
    ldrb w1, [x3]
    cmp w1, #10
    b.ne 7f
    mov x0, #10
    bl _putchar
    add x3, x3, #1
    adrp x4, file_echo_pos@page
    add x4, x4, file_echo_pos@pageoff
    str x3, [x4]
    b _fe_done
7:
    // No trailing newline in source (last line): print one for the console
    mov x0, #10
    bl _putchar
    adrp x4, file_echo_pos@page
    add x4, x4, file_echo_pos@pageoff
    str x3, [x4]
_fe_done:
    ldp x29, x30, [sp], #16
    ret

// _push_source: save current SOURCE/>IN/SOURCE-ID/file_echo_pos on source_stack.
// Frame = 5 quads (addr, len, >IN, source-id, file_echo_pos). Clobbers x0-x3.
// Returns x0=1 ok, x0=0 overflow.
_push_source:
    adrp x0, source_sp@page
    add x0, x0, source_sp@pageoff
    ldr x1, [x0]
    cmp x1, #8
    b.hs 1f
    mov x2, #40                    // 5*8 per frame
    mul x3, x1, x2
    adrp x2, source_stack@page
    add x2, x2, source_stack@pageoff
    add x2, x2, x3
    // store addr, len, to_in, source_id, file_echo_pos
    adrp x3, source_addr@page
    add x3, x3, source_addr@pageoff
    ldr x3, [x3]
    str x3, [x2], #8
    adrp x3, source_len@page
    add x3, x3, source_len@pageoff
    ldr x3, [x3]
    str x3, [x2], #8
    adrp x3, to_in_var@page
    add x3, x3, to_in_var@pageoff
    ldr x3, [x3]
    str x3, [x2], #8
    adrp x3, source_id_var@page
    add x3, x3, source_id_var@pageoff
    ldr x3, [x3]
    str x3, [x2], #8
    adrp x3, file_echo_pos@page
    add x3, x3, file_echo_pos@pageoff
    ldr x3, [x3]
    str x3, [x2]
    add x1, x1, #1
    str x1, [x0]
    mov x0, #1
    ret
1:
    mov x0, #0
    ret

// _pop_source: restore SOURCE/>IN/SOURCE-ID/file_echo_pos. x0=1 ok, x0=0 underflow.
_pop_source:
    adrp x0, source_sp@page
    add x0, x0, source_sp@pageoff
    ldr x1, [x0]
    cbz x1, 1f
    sub x1, x1, #1
    str x1, [x0]
    mov x2, #40
    mul x3, x1, x2
    adrp x2, source_stack@page
    add x2, x2, source_stack@pageoff
    add x2, x2, x3
    ldr x3, [x2], #8
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    str x3, [x0]
    mov x4, x3                     // base for cursor
    ldr x3, [x2], #8
    adrp x0, source_len@page
    add x0, x0, source_len@pageoff
    str x3, [x0]
    ldr x3, [x2], #8
    adrp x0, to_in_var@page
    add x0, x0, to_in_var@pageoff
    str x3, [x0]
    add x4, x4, x3
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    str x4, [x0]
    ldr x3, [x2], #8
    adrp x0, source_id_var@page
    add x0, x0, source_id_var@pageoff
    str x3, [x0]
    ldr x3, [x2]
    adrp x0, file_echo_pos@page
    add x0, x0, file_echo_pos@pageoff
    str x3, [x0]
    mov x0, #1
    ret
1:
    mov x0, #0
    ret

// _cursor_load: -> x0 = absolute parse pointer (SOURCE + >IN)
_cursor_load:
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x0, [x0]
    adrp x1, to_in_var@page
    add x1, x1, to_in_var@pageoff
    ldr x1, [x1]
    add x0, x0, x1
    ret

// _cursor_store: x0 = absolute parse pointer; updates >IN and word_cursor
_cursor_store:
    adrp x1, source_addr@page
    add x1, x1, source_addr@pageoff
    ldr x1, [x1]
    sub x2, x0, x1                 // offset
    cmp x2, #0
    b.ge 1f
    mov x2, #0
1:
    adrp x3, source_len@page
    add x3, x3, source_len@pageoff
    ldr x3, [x3]
    cmp x2, x3
    b.ls 2f
    mov x2, x3
2:
    adrp x1, to_in_var@page
    add x1, x1, to_in_var@pageoff
    str x2, [x1]
    adrp x1, source_addr@page
    add x1, x1, source_addr@pageoff
    ldr x1, [x1]
    add x1, x1, x2
    adrp x3, word_cursor@page
    add x3, x3, word_cursor@pageoff
    str x1, [x3]
    ret

// _source_end: -> x0 = SOURCE+u (one past last char)
_source_end:
    adrp x0, source_addr@page
    add x0, x0, source_addr@pageoff
    ldr x0, [x0]
    adrp x1, source_len@page
    add x1, x1, source_len@pageoff
    ldr x1, [x1]
    add x0, x0, x1
    ret

// _putchar: x0 = char
// Uses only x0-x2/x16 (+ frame). Does not touch x19-x28 (VM-safe).
.globl _putchar
_putchar:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    sub sp, sp, #16
    strb w0, [sp]
    mov x0, #1              // fd = stdout
    mov x1, sp              // buf
    mov x2, #1              // len
    mov x16, #4             // write
    svc #0x80               // Darwin: preserves x19-x28; result in x0
    add sp, sp, #16
    ldp x29, x30, [sp], #16
    ret

// _rl_echo: like _putchar but only when line-editor owns the TTY (raw mode).
// Avoids double-echo when still in cooked mode or when stdin is a pipe.
_rl_echo:
    stp x29, x30, [sp, #-16]!
    adrp x1, tty_raw_active@page
    add x1, x1, tty_raw_active@pageoff
    ldr x1, [x1]
    cbz x1, 1f
    bl _putchar
1:
    ldp x29, x30, [sp], #16
    ret

// _getchar: returns char or -1 on EOF
// Uses only x0-x2/x16 (+ frame). Does not touch x19-x28 (VM-safe).
.globl _getchar
_getchar:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    sub sp, sp, #16
    mov x0, #0              // fd = stdin
    mov x1, sp
    mov x2, #1
    mov x16, #3             // read
    svc #0x80
    cbz x0, _gc_eof
    ldrb w0, [sp]
    add sp, sp, #16
    ldp x29, x30, [sp], #16
    ret
_gc_eof:
    mov w0, #-1
    add sp, sp, #16
    ldp x29, x30, [sp], #16
    ret

// _print_string_svc: x0 = null-terminated string, print via SVC
_print_string_svc:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    mov x1, x0
    mov x2, #0
_pss_len:
    ldrb w3, [x1, x2]
    cbz w3, _pss_print
    add x2, x2, #1
    b _pss_len
_pss_print:
    cbz x2, _pss_done
    mov x0, #1
    mov x16, #4
    svc #0x80
_pss_done:
    ldp x29, x30, [sp], #16
    ret

// ============================================================================
// Line editor (_read_line)
// Raw-ish TTY (no ICANON/ECHO) + local echo, so left/right/backspace work
// when pasting or editing a long definition before Enter.
// Up/Down arrows walk a ring of recent lines (history).
// x0=buf, x1=maxlen (incl. room for NUL) -> x0=buf or 0 on EOF
// Preserves VM regs x19-x24 (and more).
// ============================================================================

// History: 32 lines x 512 bytes (NUL-terminated). Ring buffer.
.equ HIST_MAX, 32
.equ HIST_LINE, 512

// _tty_raw_enter / _tty_raw_leave: libc tcgetattr/tcsetattr
// termios layout (Darwin arm64): c_lflag @24, c_cc @32, VMIN=16, VTIME=17
// ICANON=0x100, ECHO=0x8, ECHOE=0x2
_tty_raw_enter:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    adrp x1, tty_termios_save@page
    add x1, x1, tty_termios_save@pageoff
    mov x0, #0                      // stdin
    bl _tcgetattr
    cbnz x0, _tty_re_fail
    // copy save -> raw (72 bytes)
    adrp x0, tty_termios_save@page
    add x0, x0, tty_termios_save@pageoff
    adrp x1, tty_termios_raw@page
    add x1, x1, tty_termios_raw@pageoff
    mov x2, #72
1:
    cbz x2, 2f
    ldrb w3, [x0], #1
    strb w3, [x1], #1
    sub x2, x2, #1
    b 1b
2:
    adrp x1, tty_termios_raw@page
    add x1, x1, tty_termios_raw@pageoff
    ldr x0, [x1, #24]               // c_lflag
    mov x2, #0x108                  // ICANON|ECHO
    bic x0, x0, x2
    mov x2, #0x2                    // ECHOE
    bic x0, x0, x2
    str x0, [x1, #24]
    mov w0, #1
    strb w0, [x1, #32+16]           // c_cc[VMIN]=1
    strb wzr, [x1, #32+17]          // c_cc[VTIME]=0
    mov x0, #0
    mov x2, x1
    mov x1, #0                      // TCSANOW
    bl _tcsetattr
    cbnz x0, _tty_re_fail
    adrp x0, tty_raw_active@page
    add x0, x0, tty_raw_active@pageoff
    mov x1, #1
    str x1, [x0]
    ldp x29, x30, [sp], #16
    ret
_tty_re_fail:
    adrp x0, tty_raw_active@page
    add x0, x0, tty_raw_active@pageoff
    str xzr, [x0]
    ldp x29, x30, [sp], #16
    ret

_tty_raw_leave:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    adrp x0, tty_raw_active@page
    add x0, x0, tty_raw_active@pageoff
    ldr x1, [x0]
    cbz x1, 1f
    str xzr, [x0]
    mov x0, #0
    mov x1, #0                      // TCSANOW
    adrp x2, tty_termios_save@page
    add x2, x2, tty_termios_save@pageoff
    bl _tcsetattr
1:
    ldp x29, x30, [sp], #16
    ret

// _rl_emit_bs: emit n backspaces (x0=n)
_rl_emit_bs:
    stp x29, x30, [sp, #-16]!
    stp x19, x20, [sp, #-16]!
    mov x19, x0
1:
    cbz x19, 2f
    mov x0, #8
    bl _rl_echo
    sub x19, x19, #1
    b 1b
2:
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _rl_redraw_tail: from cursor pos to end, then pad space, then back up.
// x19=buf x21=len x22=pos  (does not clobber those permanently beyond needs)
// After delete/insert-at-middle: show buf[pos..len), space, BS*(len-pos+1)
_rl_redraw_tail:
    stp x29, x30, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    mov x23, x22                    // i = pos
1:
    cmp x23, x21
    b.ge 2f
    ldrb w0, [x19, x23]
    bl _rl_echo
    add x23, x23, #1
    b 1b
2:
    mov x0, #32                     // trailing space clears leftover char
    bl _rl_echo
    // backspaces: (len - pos + 1)
    sub x0, x21, x22
    add x0, x0, #1
    bl _rl_emit_bs
    ldp x23, x24, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _rl_clear_display: erase current line on screen (cursor -> col0, wipe)
// uses x19/x21/x22
_rl_clear_display:
    stp x29, x30, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    mov x0, x22
    bl _rl_emit_bs                  // cursor to start
    mov x23, x21
1:
    cbz x23, 2f
    mov x0, #32
    bl _rl_echo
    sub x23, x23, #1
    b 1b
2:
    mov x0, x21
    bl _rl_emit_bs
    ldp x23, x24, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _rl_load_str: replace edit buffer with C-string at x0 (NUL-term), redraw
// respects maxlen in x20; updates x21/x22
_rl_load_str:
    stp x29, x30, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    stp x25, x26, [sp, #-16]!
    mov x25, x0                     // src
    bl _rl_clear_display
    mov x21, #0
    mov x23, #0
1:
    ldrb w0, [x25, x23]
    cbz w0, 2f
    cmp x23, x20
    b.ge 2f
    strb w0, [x19, x23]
    add x23, x23, #1
    b 1b
2:
    mov x21, x23
    mov x22, x23
    strb wzr, [x19, x21]
    // echo new line
    mov x23, #0
3:
    cmp x23, x21
    b.ge 4f
    ldrb w0, [x19, x23]
    bl _rl_echo
    add x23, x23, #1
    b 3b
4:
    ldp x25, x26, [sp], #16
    ldp x23, x24, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _hist_push: save current line (x19, x21=len) into history ring
_hist_push:
    stp x29, x30, [sp, #-16]!
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    cbz x21, _hp_done               // skip empty
    // cap copy length
    mov x22, x21
    cmp x22, #HIST_LINE-1
    b.ls 1f
    mov x22, #HIST_LINE-1
1:
    // skip if identical to most recent entry
    adrp x0, hist_count@page
    add x0, x0, hist_count@pageoff
    ldr x1, [x0]
    cbz x1, _hp_store
    adrp x0, hist_head@page
    add x0, x0, hist_head@pageoff
    ldr x2, [x0]                    // head = next write
    // newest slot = (head - 1) mod HIST_MAX
    subs x2, x2, #1
    b.ge 2f
    mov x2, #HIST_MAX-1
2:
    // compare
    mov x3, #HIST_LINE
    mul x3, x2, x3
    adrp x4, hist_data@page
    add x4, x4, hist_data@pageoff
    add x4, x4, x3                  // &hist[newest]
    mov x5, #0
3:
    cmp x5, x22
    b.ge 4f
    ldrb w6, [x19, x5]
    ldrb w7, [x4, x5]
    cmp w6, w7
    b.ne _hp_store
    add x5, x5, #1
    b 3b
4:
    ldrb w7, [x4, x5]               // must be NUL at end for equal
    cbnz w7, _hp_store
    // equal — skip push
    b _hp_done
_hp_store:
    adrp x0, hist_head@page
    add x0, x0, hist_head@pageoff
    ldr x2, [x0]
    mov x3, #HIST_LINE
    mul x3, x2, x3
    adrp x4, hist_data@page
    add x4, x4, hist_data@pageoff
    add x4, x4, x3
    mov x5, #0
5:
    cmp x5, x22
    b.ge 6f
    ldrb w6, [x19, x5]
    strb w6, [x4, x5]
    add x5, x5, #1
    b 5b
6:
    strb wzr, [x4, x5]
    // head = (head+1) % HIST_MAX
    add x2, x2, #1
    cmp x2, #HIST_MAX
    b.lo 7f
    mov x2, #0
7:
    str x2, [x0]
    adrp x0, hist_count@page
    add x0, x0, hist_count@pageoff
    ldr x1, [x0]
    cmp x1, #HIST_MAX
    b.hs _hp_done
    add x1, x1, #1
    str x1, [x0]
_hp_done:
    adrp x0, hist_nav@page
    add x0, x0, hist_nav@pageoff
    mov x1, #-1
    str x1, [x0]
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _rl_hist_up: older line (ESC [ A)
_rl_hist_up:
    stp x29, x30, [sp, #-16]!
    adrp x0, hist_count@page
    add x0, x0, hist_count@pageoff
    ldr x1, [x0]
    cbz x1, _hu_done
    adrp x0, hist_nav@page
    add x0, x0, hist_nav@pageoff
    ldr x2, [x0]                    // current nav (-1 = draft)
    // first up: save draft
    cmp x2, #-1
    b.ne 1f
    // copy buf -> hist_draft
    adrp x3, hist_draft@page
    add x3, x3, hist_draft@pageoff
    mov x4, #0
2:
    cmp x4, x21
    b.ge 3f
    cmp x4, #HIST_LINE-1
    b.ge 3f
    ldrb w5, [x19, x4]
    strb w5, [x3, x4]
    add x4, x4, #1
    b 2b
3:
    strb wzr, [x3, x4]
    adrp x3, hist_draft_len@page
    add x3, x3, hist_draft_len@pageoff
    str x21, [x3]
    mov x2, #0                      // nav = newest
    b 4f
1:
    // older
    add x3, x2, #1
    cmp x3, x1
    b.hs _hu_done                   // already oldest
    mov x2, x3
4:
    str x2, [x0]
    // slot = (hist_head - 1 - nav) mod HIST_MAX
    adrp x3, hist_head@page
    add x3, x3, hist_head@pageoff
    ldr x3, [x3]
    sub x3, x3, #1
    sub x3, x3, x2
5:
    cmp x3, #0
    b.ge 6f
    add x3, x3, #HIST_MAX
    b 5b
6:
    mov x4, #HIST_LINE
    mul x4, x3, x4
    adrp x0, hist_data@page
    add x0, x0, hist_data@pageoff
    add x0, x0, x4
    bl _rl_load_str
_hu_done:
    ldp x29, x30, [sp], #16
    ret

// _rl_hist_down: newer line / draft (ESC [ B)
_rl_hist_down:
    stp x29, x30, [sp, #-16]!
    adrp x0, hist_nav@page
    add x0, x0, hist_nav@pageoff
    ldr x2, [x0]
    cmp x2, #-1
    b.eq _hd_done                   // already on draft
    cbz x2, 1f                      // nav 0 -> restore draft
    // newer
    sub x2, x2, #1
    str x2, [x0]
    adrp x3, hist_head@page
    add x3, x3, hist_head@pageoff
    ldr x3, [x3]
    sub x3, x3, #1
    sub x3, x3, x2
2:
    cmp x3, #0
    b.ge 3f
    add x3, x3, #HIST_MAX
    b 2b
3:
    mov x4, #HIST_LINE
    mul x4, x3, x4
    adrp x1, hist_data@page
    add x1, x1, hist_data@pageoff
    add x0, x1, x4
    bl _rl_load_str
    b _hd_done
1:
    mov x1, #-1
    str x1, [x0]
    adrp x0, hist_draft@page
    add x0, x0, hist_draft@pageoff
    bl _rl_load_str
_hd_done:
    ldp x29, x30, [sp], #16
    ret

// _read_line: x0=buf, x1=maxlen -> x0=buf ptr on success, 0 on EOF
_read_line:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    stp x23, x24, [sp, #-16]!
    stp x25, x26, [sp, #-16]!
    mov x19, x0                     // buf
    // leave 1 byte for NUL
    subs x20, x1, #1
    b.gt 1f
    mov x20, #0
1:
    mov x21, #0                     // len
    mov x22, #0                     // pos
    // reset history navigation for this prompt
    adrp x0, hist_nav@page
    add x0, x0, hist_nav@pageoff
    mov x1, #-1
    str x1, [x0]
    bl _tty_raw_enter
_rl_loop:
    bl _getchar
    cmp w0, #-1
    b.le _rl_eof
    and w0, w0, #0xff
    // Enter
    cmp w0, #10
    b.eq _rl_nl
    cmp w0, #13
    b.eq _rl_nl
    // Backspace / DEL
    cmp w0, #8
    b.eq _rl_backspace
    cmp w0, #127
    b.eq _rl_backspace
    // Ctrl-A home
    cmp w0, #1
    b.eq _rl_home
    // Ctrl-E end
    cmp w0, #5
    b.eq _rl_end
    // Ctrl-U kill whole line
    cmp w0, #21
    b.eq _rl_kill_all
    // Ctrl-K kill to end
    cmp w0, #11
    b.eq _rl_kill_eol
    // Ctrl-D: EOF if empty, else delete forward
    cmp w0, #4
    b.eq _rl_ctrl_d
    // ESC sequences (arrows, etc.)
    cmp w0, #27
    b.eq _rl_esc
    // Printable ASCII
    cmp w0, #32
    b.lo _rl_loop
    cmp w0, #126
    b.hi _rl_loop
    // insert w0 at pos
    cmp x21, x20
    b.ge _rl_loop                   // full
    mov w25, w0                     // save char
    // shift right: from len-1 down to pos
    mov x23, x21
_rl_ins_shift:
    cmp x23, x22
    b.le _rl_ins_store
    sub x24, x23, #1
    ldrb w0, [x19, x24]
    strb w0, [x19, x23]
    sub x23, x23, #1
    b _rl_ins_shift
_rl_ins_store:
    strb w25, [x19, x22]
    add x21, x21, #1
    // echo inserted char + tail
    mov w0, w25
    bl _rl_echo
    add x22, x22, #1
    // print rest of line after new cursor, then BS back
    mov x23, x22
_rl_ins_echo:
    cmp x23, x21
    b.ge _rl_ins_back
    ldrb w0, [x19, x23]
    bl _rl_echo
    add x23, x23, #1
    b _rl_ins_echo
_rl_ins_back:
    sub x0, x21, x22
    bl _rl_emit_bs
    b _rl_loop

_rl_backspace:
    cbz x22, _rl_loop
    sub x22, x22, #1
    // shift left from pos
    mov x23, x22
_rl_bs_shift:
    add x24, x23, #1
    cmp x24, x21
    b.ge _rl_bs_done_shift
    ldrb w0, [x19, x24]
    strb w0, [x19, x23]
    add x23, x23, #1
    b _rl_bs_shift
_rl_bs_done_shift:
    sub x21, x21, #1
    mov x0, #8
    bl _rl_echo
    bl _rl_redraw_tail
    b _rl_loop

_rl_home:
    mov x0, x22
    bl _rl_emit_bs
    mov x22, #0
    b _rl_loop

_rl_end:
1:
    cmp x22, x21
    b.ge _rl_loop
    ldrb w0, [x19, x22]
    bl _rl_echo
    add x22, x22, #1
    b 1b

_rl_kill_all:
    mov x0, x22
    bl _rl_emit_bs
    // erase visible: spaces for old len, then BS
    mov x23, x21
1:
    cbz x23, 2f
    mov x0, #32
    bl _rl_echo
    sub x23, x23, #1
    b 1b
2:
    mov x0, x21
    bl _rl_emit_bs
    mov x21, #0
    mov x22, #0
    b _rl_loop

_rl_kill_eol:
    // clear on screen from pos
    sub x23, x21, x22
1:
    cbz x23, 2f
    mov x0, #32
    bl _rl_echo
    sub x23, x23, #1
    b 1b
2:
    sub x0, x21, x22
    bl _rl_emit_bs
    mov x21, x22
    b _rl_loop

_rl_ctrl_d:
    cbz x21, _rl_eof                // empty -> EOF
    // delete forward if not at end
    cmp x22, x21
    b.ge _rl_loop
    mov x23, x22
_rl_del_shift:
    add x24, x23, #1
    cmp x24, x21
    b.ge _rl_del_done
    ldrb w0, [x19, x24]
    strb w0, [x19, x23]
    add x23, x23, #1
    b _rl_del_shift
_rl_del_done:
    sub x21, x21, #1
    bl _rl_redraw_tail
    b _rl_loop

// ESC [ ... final   (CSI).  w26 holds last parameter digit (for ~ keys).
_rl_esc:
    bl _getchar
    cmp w0, #-1
    b.le _rl_eof
    cmp w0, #'['
    b.ne _rl_loop                   // drop lone ESC / Alt- keys
    mov w26, #0                     // last CSI digit
    // collect CSI until final byte 0x40-0x7E
_rl_csi:
    bl _getchar
    cmp w0, #-1
    b.le _rl_eof
    cmp w0, #'0'
    b.lo 1f
    cmp w0, #'9'
    b.hi 1f
    mov w26, w0                     // remember digit
    b _rl_csi
1:
    cmp w0, #0x40
    b.lo _rl_csi                    // other parameter/intermediate
    // final
    cmp w0, #'A'                    // up — history older
    b.eq _rl_up
    cmp w0, #'B'                    // down — history newer
    b.eq _rl_down
    cmp w0, #'C'                    // right
    b.eq _rl_right
    cmp w0, #'D'                    // left
    b.eq _rl_left
    cmp w0, #'H'                    // home
    b.eq _rl_home
    cmp w0, #'F'                    // end
    b.eq _rl_end
    cmp w0, #'~'
    b.ne _rl_loop
    // ESC [ n ~  : 1/7=home 3=delete 4/8=end
    cmp w26, #'3'
    b.eq _rl_ctrl_d
    cmp w26, #'1'
    b.eq _rl_home
    cmp w26, #'7'
    b.eq _rl_home
    cmp w26, #'4'
    b.eq _rl_end
    cmp w26, #'8'
    b.eq _rl_end
    b _rl_loop

_rl_up:
    bl _rl_hist_up
    b _rl_loop

_rl_down:
    bl _rl_hist_down
    b _rl_loop

_rl_left:
    cbz x22, _rl_loop
    sub x22, x22, #1
    mov x0, #8
    bl _rl_echo
    b _rl_loop

_rl_right:
    cmp x22, x21
    b.ge _rl_loop
    ldrb w0, [x19, x22]
    bl _rl_echo
    add x22, x22, #1
    b _rl_loop

_rl_nl:
    // move visually to end then newline
1:
    cmp x22, x21
    b.ge 2f
    ldrb w0, [x19, x22]
    bl _rl_echo
    add x22, x22, #1
    b 1b
2:
    mov x0, #10
    bl _rl_echo
    strb wzr, [x19, x21]
    bl _hist_push                   // remember non-empty lines
    // _tty_raw_leave clobbers x0 (tcsetattr status); keep buffer ptr in x25
    mov x25, x19
    bl _tty_raw_leave
    mov x0, x25                     // success: return buf (non-zero)
    ldp x25, x26, [sp], #16
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

_rl_eof:
    // Preserve len across leave; x0 must be buf or 0 after restore
    mov x25, x21
    bl _tty_raw_leave
    cbz x25, _rl_null
    strb wzr, [x19, x25]
    mov x0, x19
    ldp x25, x26, [sp], #16
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_rl_null:
    mov x0, #0
    ldp x25, x26, [sp], #16
    ldp x23, x24, [sp], #16
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _next_word: parse next word -> x0=addr of word_scratch, x1=length (0=done)
// Stops at SOURCE end (not only NUL) so EVALUATE substrings work.
_next_word:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!

    bl _cursor_load
    mov x19, x0
    bl _source_end
    mov x21, x0                    // end of SOURCE

_nw_skip:
    cmp x19, x21
    b.hs _nw_eof
    ldrb w0, [x19]
    cbz w0, _nw_eof
    cmp w0, #32
    b.eq _nw_adv
    cmp w0, #10
    b.eq _nw_adv
    cmp w0, #9
    b.eq _nw_adv
    b _nw_start
_nw_adv:
    add x19, x19, #1
    b _nw_skip

_nw_start:
    mov x20, x19
_nw_scan:
    cmp x19, x21
    b.hs _nw_got
    ldrb w0, [x19]
    cbz w0, _nw_got
    cmp w0, #32
    b.eq _nw_got
    cmp w0, #10
    b.eq _nw_got
    cmp w0, #9
    b.eq _nw_got
    add x19, x19, #1
    b _nw_scan

_nw_got:
    sub x1, x19, x20
    cbz x1, _nw_eof

    // Copy to word_scratch
    adrp x2, word_scratch@page
    add x2, x2, word_scratch@pageoff
    mov x3, #0
_nw_copy:
    cmp x3, x1
    b.ge _nw_copied
    ldrb w4, [x20, x3]
    strb w4, [x2, x3]
    add x3, x3, #1
    b _nw_copy
_nw_copied:
    strb wzr, [x2, x3]

    // update >IN (preserve len x1 and scratch x2)
    stp x1, x2, [sp, #-16]!
    mov x0, x19
    bl _cursor_store
    ldp x1, x2, [sp], #16

    mov x0, x2
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

_nw_eof:
    mov x0, #0
    mov x1, #0
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _parse_number: x0=addr, x1=len -> x0=1 (val in x1) or 0
// Honors BASE (2..36). Digits: 0-9, A-Z / a-z.
_parse_number:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    mov x19, x0                 // addr
    mov x20, x1                 // len
    mov x2, #0                  // accumulator
    mov x3, #0                  // digit count
    mov x4, #0                  // negative flag
    // base
    adrp x21, base_var@page
    add x21, x21, base_var@pageoff
    ldr x21, [x21]
    cmp x21, #2
    b.lo _pn_base10
    cmp x21, #36
    b.ls _pn_base_ok
_pn_base10:
    mov x21, #10
_pn_base_ok:
    cbz x20, _pn_fail
    ldrb w5, [x19]
    cmp w5, #45                 // '-'
    b.ne _pn_loop
    mov x4, #1
    add x19, x19, #1
    sub x20, x20, #1
_pn_loop:
    cbz x20, _pn_done
    ldrb w5, [x19], #1
    // digit value in w22
    sub w22, w5, #48            // '0'
    cmp w22, #9
    b.ls _pn_have_digit
    // A-Z / a-z -> 10..35
    mov w22, w5
    cmp w22, #97                // 'a'
    b.lo _pn_upper
    cmp w22, #122               // 'z'
    b.hi _pn_fail
    sub w22, w22, #32           // tolower -> toupper
_pn_upper:
    sub w22, w22, #65           // 'A'
    cmp w22, #25
    b.hi _pn_fail
    add w22, w22, #10
_pn_have_digit:
    cmp x22, x21                // digit must be < base
    b.hs _pn_fail
    mul x2, x2, x21
    add x2, x2, x22
    add x3, x3, #1
    sub x20, x20, #1
    b _pn_loop
_pn_done:
    cbz x3, _pn_fail
    cbz x4, _pn_pos
    neg x2, x2
_pn_pos:
    mov x0, #1
    mov x1, x2
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_pn_fail:
    mov x0, #0
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _find_word: x0=addr, x1=len -> x0=entry or 0, x1=flags
_find_word:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!
    mov x19, x0
    mov x20, x1
    ldr x21, [x24]          // start at latest dict entry (*latest_var)
_fw_loop:
    cbz x21, _fw_fail
    ldr x2, [x21, #8]
    and x3, x2, #0xFF
    cmp x3, x20
    b.ne _fw_next
    add x4, x21, #24
    mov x5, #0
_fw_cmp:
    cmp x5, x20
    b.ge _fw_match
    ldrb w6, [x4, x5]
    ldrb w7, [x19, x5]
    cmp w6, #97
    b.lo _fw_ch
    sub w6, w6, #32
_fw_ch:
    cmp w7, #97
    b.lo _fw_eq
    sub w7, w7, #32
_fw_eq:
    cmp w6, w7
    b.ne _fw_next
    add x5, x5, #1
    b _fw_cmp
_fw_match:
    mov x0, x21
    ldr x1, [x21, #8]
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_fw_next:
    ldr x21, [x21]
    b _fw_loop
_fw_fail:
    mov x0, #0
    mov x1, #0
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _warn_redef: x0=name addr, x1=len
// If name is already in the dictionary, print:  <name> is redefined\n
// Gated by REDEF-WARNING (redef_warn cell): 0 = quiet, nonzero = warn.
// Cell is 0 during bootstrap; set to TRUE (-1) when entering QUIT.
_warn_redef:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    adrp x2, redef_warn@page
    add x2, x2, redef_warn@pageoff
    ldr x2, [x2]
    cbz x2, _wr_done
    mov x19, x0                     // name
    mov x20, x1                     // len
    bl _find_word
    cbz x0, _wr_done
    // write name
    cbz x20, 1f
    mov x0, #1                      // stdout
    mov x1, x19
    mov x2, x20
    mov x16, #4                     // write
    svc #0x80
1:
    mov x0, #1
    adrp x1, str_redef@page
    add x1, x1, str_redef@pageoff
    mov x2, #15                     // " is redefined\n"
    mov x16, #4
    svc #0x80
_wr_done:
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _compile_cell: x0 = value, compile at HERE
_compile_cell:
    adrp x1, here_ptr@page
    add x1, x1, here_ptr@pageoff
    ldr x1, [x1]
    str x0, [x1], #8
    adrp x2, here_ptr@page
    add x2, x2, here_ptr@pageoff
    str x1, [x2]
    ret

// _print_signed: x0=value  (uses BASE; leading '-' if negative)
_print_signed:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    sub sp, sp, #80             // 16-byte aligned; room for digits + sign + NUL
    mov x1, sp
    bl _i64_to_str
    mov x0, sp
    bl _print_string_svc
    add sp, sp, #80
    ldp x29, x30, [sp], #16
    ret

// _print_unsigned: x0=value  (uses BASE; always unsigned)
_print_unsigned:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    sub sp, sp, #80
    mov x1, sp
    bl _u64_to_str
    mov x0, sp
    bl _print_string_svc
    add sp, sp, #80
    ldp x29, x30, [sp], #16
    ret

// _load_base: -> x6 = BASE clamped to 2..36
_load_base:
    adrp x6, base_var@page
    add x6, x6, base_var@pageoff
    ldr x6, [x6]
    cmp x6, #2
    b.lo _lb_def
    cmp x6, #36
    b.ls _lb_ok
_lb_def:
    mov x6, #10
_lb_ok:
    ret

// _digit_char: w8 = digit value 0..35 -> ASCII in w8
_digit_char:
    cmp w8, #9
    b.hi _dc_alpha
    add w8, w8, #48             // '0'
    ret
_dc_alpha:
    add w8, w8, #55             // 'A' - 10
    ret

// _i64_to_str: x0=val, x1=buf — signed, current BASE
_i64_to_str:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    mov x2, x1                  // write ptr
    add x3, x1, #64             // temp digit area near end of 72-byte buf
    mov x4, x0                  // value
    mov x5, #0                  // digit count
    bl _load_base               // x6 = base
    mov x19, x6
    cmp x4, #0
    b.ge _i2s_pos
    mov w6, #45
    strb w6, [x2], #1           // '-'
    neg x4, x4
_i2s_pos:
    cbnz x4, _i2s_div
    mov w6, #48
    strb w6, [x2], #1
    strb wzr, [x2]
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_i2s_div:
    udiv x7, x4, x19
    msub x8, x7, x19, x4        // remainder
    bl _digit_char
    strb w8, [x3, #-1]!
    add x5, x5, #1
    mov x4, x7
    cbnz x4, _i2s_div
_i2s_cpy:
    cbz x5, _i2s_done
    ldrb w8, [x3], #1
    strb w8, [x2], #1
    sub x5, x5, #1
    b _i2s_cpy
_i2s_done:
    strb wzr, [x2]
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _u64_to_str: x0=val, x1=buf — unsigned, current BASE
_u64_to_str:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    mov x2, x1
    add x3, x1, #64
    mov x4, x0
    mov x5, #0
    bl _load_base
    mov x19, x6
    cbnz x4, _u2s_div
    mov w6, #48
    strb w6, [x2], #1
    strb wzr, [x2]
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_u2s_div:
    udiv x7, x4, x19
    msub x8, x7, x19, x4
    bl _digit_char
    strb w8, [x3, #-1]!
    add x5, x5, #1
    mov x4, x7
    cbnz x4, _u2s_div
_u2s_cpy:
    cbz x5, _u2s_done
    ldrb w8, [x3], #1
    strb w8, [x2], #1
    sub x5, x5, #1
    b _u2s_cpy
_u2s_done:
    strb wzr, [x2]
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _print_dots: print stack without destroying DSP/TOS.
// Empty: DSP==base, TOS=0. Each DPUSH stores previous TOS; after n pushes
// from empty, mem is [v_{n-1},...,v1,0_sentinel] and x20=v_n. Skip sentinel.
// Callee-saved x19-x22 only — do not rely on x0-x18 across bl.
_print_dots:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!

    adrp x19, data_stack@page
    add x19, x19, data_stack@pageoff
    add x19, x19, #4096            // stack base

    cmp x22, x19
    b.ge _pd_empty

    sub x21, x19, x22
    lsr x21, x21, #3               // mem_cells >= 1; depth == mem_cells

    mov x0, x21
    bl _print_unsigned
    mov x0, #58                    // ':'
    bl _putchar
    mov x0, #32
    bl _putchar

    // under-TOS items at indices mem_cells-2 .. 0 (skip sentinel at mem_cells-1)
    // x19 = loop index (callee-saved)
    cmp x21, #1
    b.eq _pd_print_tos
    sub x19, x21, #1               // x19 = mem_cells - 1
_pd_mem_loop:
    sub x19, x19, #1
    lsl x0, x19, #3
    ldr x0, [x22, x0]
    bl _print_signed
    mov x0, #32
    bl _putchar
    cbnz x19, _pd_mem_loop

_pd_print_tos:
    mov x0, x20
    bl _print_signed
    mov x0, #32
    bl _putchar
    b _pd_done

_pd_empty:
    mov x0, #48                    // '0'
    bl _putchar
    mov x0, #58                    // ':'
    bl _putchar

_pd_done:
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// XRESTART: trampoline code that returns to the interpreter loop.
// Must be in __text (executable) section, NOT in .data.
.align 8
XRESTART:
    b _interpret_loop

// ============================================================================
// Data Section
// ============================================================================
.data
.align 8

data_stack:     .skip 4096
return_stack:   .skip 2048
input_buffer:   .skip 1024
file_buffer:    .skip 65536
word_scratch:   .skip 64
tty_termios_save: .skip 80
tty_termios_raw:  .skip 80
tty_raw_active:   .quad 0
redef_warn:       .quad 0           // REDEF-WARNING body; 0=off, nonzero=on (TRUE after boot)
redef_boot_done:  .quad 0           // set after first QUIT so default TRUE applied once
file_echo:        .quad 0           // FILE-ECHO body; 0=off, nonzero=on
file_echo_pos:    .quad 0           // absolute addr: next source byte not yet echoed
noname_xt:        .quad 0           // :NONAME entry; ; pushes then clears
slit_esc_buf:     .skip 256         // S\" interpret expansion buffer
// Line history (see HIST_MAX / HIST_LINE)
hist_data:        .skip HIST_MAX * HIST_LINE
hist_draft:       .skip HIST_LINE
hist_count:       .quad 0
hist_head:        .quad 0
hist_nav:         .quad -1
hist_draft_len:   .quad 0

state_var:      .quad 0
base_var:       .quad 10
here_ptr:       .quad 0
latest_var:     .quad 0
word_cursor:    .quad 0
source_addr:    .quad 0
source_len:     .quad 0
to_in_var:      .quad 0
pad_buffer:     .skip 256
hold_ptr:       .quad 0
// Nested SOURCE stack: 8 frames * 5 quads (addr, len, >IN, source-id, file_echo_pos)
source_stack:   .skip 320
source_sp:      .quad 0
source_id_var:  .quad 0
throw_handler:  .quad 0

// ENVIRONMENT? tables (name ptrs, value cells, kinds: 0=flag only, 1=value+true)
.equ ENV_COUNT, 10
.align 8
env_name_ptrs:
    .quad env_n_counted
    .quad env_n_aub
    .quad env_n_core
    .quad env_n_core_ext
    .quad env_n_floored
    .quad env_n_maxchar
    .quad env_n_maxn
    .quad env_n_maxu
    .quad env_n_rstack
    .quad env_n_stack
env_values:
    .quad 255                      // /COUNTED-STRING
    .quad 8                        // ADDRESS-UNIT-BITS
    .quad -1                       // CORE (flag)
    .quad -1                       // CORE-EXT (true — names present)
    .quad 0                        // FLOORED (false — we use symmetric /)
    .quad 255                      // MAX-CHAR
    .quad 0x7FFFFFFFFFFFFFFF       // MAX-N
    .quad 0xFFFFFFFFFFFFFFFF       // MAX-U
    .quad 256                      // RETURN-STACK-CELLS (2048/8)
    .quad 512                      // STACK-CELLS (4096/8)
env_kinds:
    .byte 1, 1, 0, 0, 0, 1, 1, 1, 1, 1
    .space 6
env_n_counted:  .asciz "/COUNTED-STRING"
env_n_aub:      .asciz "ADDRESS-UNIT-BITS"
env_n_core:     .asciz "CORE"
env_n_core_ext: .asciz "CORE-EXT"
env_n_floored:  .asciz "FLOORED"
env_n_maxchar:  .asciz "MAX-CHAR"
env_n_maxn:     .asciz "MAX-N"
env_n_maxu:     .asciz "MAX-U"
env_n_rstack:   .asciz "RETURN-STACK-CELLS"
env_n_stack:    .asciz "STACK-CELLS"

str_hello:  .asciz "PickleForth v0.2.0\n"
str_prompt: .asciz "\nok> "
str_ok:     .asciz " ok\n"
str_bye:    .asciz "Bye!\n"
str_quest:  .asciz "? "
str_cant_open:  .ascii "can't open: "
                .byte 0
str_undefined:  .ascii "undefined: "
                .byte 0
str_underflow:  .asciz "stack underflow\n"
str_overflow:   .asciz "stack overflow\n"
str_memfault:   .asciz "memory access error\n"
str_redef:  .asciz " is redefined\n"
.align 8
quit_jmpbuf:        .skip 256      // sigjmp_buf for fault recovery
fault_handlers_on:  .quad 0
str_x:      .asciz "X"

// ============================================================================
// High-level Forth bootstrap (interpreted once at startup)
// Prefer new user-facing words here; assembly only for needed primitives.
//
// Dictionary field helpers (xt = entry address from ' or FIND):
//   >LINK  ( xt -- a-addr )  link field (previous word); offset 0
//   >FLAGS ( xt -- a-addr )  flags|length cell; offset 8
//   >CODE  ( xt -- a-addr )  code field address; offset 16  (was bare "16 +")
//   >NAME  ( xt -- a-addr )  first name byte; offset 24
//   >BODY  ( xt -- a-addr )  body/parameter field after aligned name
//
// Control-flow compilers (immediate):
//   BEGIN  ( -- dest )              mark begin for AGAIN/UNTIL/WHILE
//   UNTIL  ( dest -- )              compile 0BRANCH back to dest
//   AGAIN  ( dest -- )              compile BRANCH back to dest
//   IF     ( -- orig )              compile 0BRANCH + placeholder
//   THEN   ( orig -- )              resolve forward branch
//   ELSE   ( orig1 -- orig2 )       branch around false part, resolve IF
//   WHILE  ( dest -- orig dest )    0BRANCH out of BEGIN loop
//   REPEAT ( orig dest -- )         BRANCH to dest, resolve WHILE
// ============================================================================
forth_init_str:
    // Order matters: define dependencies before users.

    // HERE as DP @ (shadows CODE HERE so SEE shows the classic definition)
    .ascii ": HERE DP @ ; "

    // --- 1. Simple ANS helpers (no control flow, no >CODE) ---
    .ascii ": BL 32 ; "
    .ascii ": SPACE BL EMIT ; "
    .ascii ": CHAR+ 1+ ; "
    .ascii ": CHARS ; "
    .ascii ": CELL+ 8 + ; "
    .ascii ": CELLS 8 * ; "
    .ascii ": ALIGNED 7 + 7 INVERT AND ; "
    .ascii ": ALIGN HERE ALIGNED HERE - ALLOT ; "
    .ascii ": 2DUP OVER OVER ; "
    .ascii ": 2DROP DROP DROP ; "
    .ascii ": 2SWAP ROT >R ROT R> ; "
    .ascii ": 2OVER >R >R 2DUP R> R> 2SWAP ; "
    .ascii ": COUNT DUP C@ SWAP CHAR+ SWAP ; "
    .ascii ": /STRING DUP >R - SWAP R> + SWAP ; "
    .ascii ": DECIMAL 10 BASE ! ; "
    .ascii ": HEX 16 BASE ! ; "
    .ascii ": 0<> 0= 0= ; "
    .ascii ": 0> 0 > ; "
    .ascii ": >= < 0= ; "
    .ascii ": <= > 0= ; "
    .ascii ": WITHIN OVER - >R - R> U< ; "

    // --- 2. Dictionary field accessors (needed by CONSTANT, ALIAS, SEE) ---
    .ascii ": >LINK ; "
    .ascii ": >FLAGS 8 + ; "
    .ascii ": >CODE 16 + ; "
    .ascii ": >NAME 24 + ; "
    .ascii ": NAME>STRING DUP >NAME SWAP >FLAGS @ 255 AND ; "
    .ascii ": >BODY NAME>STRING ALIGNED + ; "

    // --- 3. Control flow (immediate) ---
    .ascii ": BEGIN HERE ; IMMEDIATE "
    .ascii ": UNTIL 0BRANCH-ADDR , HERE - , ; IMMEDIATE "
    .ascii ": AGAIN BRANCH-ADDR , HERE - , ; IMMEDIATE "
    .ascii ": IF 0BRANCH-ADDR , HERE 0 , ; IMMEDIATE "
    .ascii ": THEN HERE OVER - SWAP ! ; IMMEDIATE "
    .ascii ": ELSE BRANCH-ADDR , HERE 0 , SWAP HERE OVER - SWAP ! ; IMMEDIATE "
    .ascii ": WHILE 0BRANCH-ADDR , HERE 0 , ; IMMEDIATE "
    .ascii ": REPEAT BRANCH-ADDR , SWAP HERE - , HERE OVER - SWAP ! ; IMMEDIATE "
    // ?COMP ( -- )  error if not compiling (ANS throw -14)
    .ascii ": ?COMP STATE @ 0= IF S\" compile only\" TYPE CR -14 THROW THEN ; "

    // DO/LOOP: ( limit start -- ) ... LOOP    classic Forth order: limit first
    // DO leaves ( 0 dest ); ?DO leaves ( orig dest ) so LOOP/+LOOP can resolve
    // the empty-range forward branch after (?DO).
    .ascii ": DO ?COMP ['] (DO) , 0 HERE ; IMMEDIATE "
    .ascii ": ?DO ?COMP ['] (?DO) , HERE 0 , HERE ; IMMEDIATE "
    .ascii ": LOOP ?COMP ['] (LOOP) , HERE - , ?DUP IF HERE OVER - SWAP ! THEN ; IMMEDIATE "
    .ascii ": +LOOP ?COMP ['] (+LOOP) , HERE - , ?DUP IF HERE OVER - SWAP ! THEN ; IMMEDIATE "

    // --- 4. Defining words / parse helpers using the above ---
    .ascii ": CHAR BL WORD COUNT DROP C@ ; "
    .ascii ": [CHAR] ?COMP CHAR LIT-ADDR , , ; IMMEDIATE "
    .ascii ": VARIABLE CREATE 0 , ; "
    // CONSTANT via DOES> (body+0=does_ip, body+8=value; DOES> action @ )
    .ascii ": CONSTANT CREATE , DOES> @ ; "
    .ascii ": RECURSE ?COMP LATEST @ , ; IMMEDIATE "

    // --- 4b. Pictured numeric output (single-cell); . and U. stay native (BASE-aware) ---
    .ascii "VARIABLE HLD "
    .ascii ": <# PAD 256 + HLD ! ; "
    .ascii ": HOLD -1 HLD +! HLD @ C! ; "
    .ascii ": #> DROP HLD @ PAD 256 + OVER - ; "
    .ascii ": # BASE @ /MOD SWAP DUP 9 > IF 7 + THEN 48 + HOLD ; "
    .ascii ": #S BEGIN # DUP 0= UNTIL ; "
    .ascii ": SIGN 0< IF 45 HOLD THEN ; "
    // Formatted print using pictured output (native . / U. remain)
    .ascii ": UD. <# #S #> TYPE SPACE ; "
    .ascii ": D. DUP 0< IF NEGATE <# #S 45 HOLD #> ELSE <# #S #> THEN TYPE SPACE ; "
    // FILL ( c-addr u char -- ); stack top is u, so bump addr via SWAP 1+ SWAP
    .ascii ": FILL >R BEGIN DUP WHILE OVER R@ SWAP C! SWAP 1+ SWAP 1- REPEAT R> DROP 2DROP ; "
    .ascii ": ERASE 0 FILL ; "
    // MOVE / CMOVE (ANS character/cell move; MOVE handles overlap)
    .ascii ": CMOVE BEGIN DUP WHILE >R OVER C@ OVER C! CHAR+ SWAP CHAR+ SWAP R> 1- REPEAT DROP 2DROP ; "
    .ascii ": CMOVE> DUP >R + 1- SWAP R@ + 1- SWAP R> BEGIN DUP WHILE >R OVER C@ OVER C! 1- SWAP 1- SWAP R> 1- REPEAT DROP 2DROP ; "
    .ascii ": MOVE DUP 0= IF DROP 2DROP EXIT THEN >R 2DUP U< IF R> CMOVE> ELSE R> CMOVE THEN ; "

    // POSTPONE (ANS, compilation only):
    //   immediate:     compile xt (runs when outer word runs)
    //   non-immediate: compile LIT xt (COMP,)  so runtime compiles xt via ,
    .ascii ": (COMP,) , ; "
    .ascii ": POSTPONE ?COMP BL WORD FIND DUP 0= IF 2DROP EXIT THEN 1 = IF , ELSE LIT-ADDR , , ['] (COMP,) , THEN ; IMMEDIATE "

    // CASE OF ENDOF ENDCASE (ANS-style; compilation only)
    .ascii ": CASE ?COMP 0 ; IMMEDIATE "
    .ascii ": OF ?COMP 1+ >R POSTPONE OVER POSTPONE = POSTPONE IF POSTPONE DROP R> ; IMMEDIATE "
    .ascii ": ENDOF ?COMP >R POSTPONE ELSE R> ; IMMEDIATE "
    .ascii ": ENDCASE ?COMP POSTPONE DROP BEGIN DUP WHILE 1- >R POSTPONE THEN R> REPEAT DROP ; IMMEDIATE "

    // --- 5. Tools / extensions ---
    // WORDS [string]  list all names, or only those containing string (case-insensitive).
    // Keep filter (fa fu) under the walk: >R / 2DUP / R@ NAME>STRING / 2SWAP so CONTAINS
    // does not consume the filter (previous ROT >R 2SWAP path ate fa fu on first match check).
    .ascii ": WORDS BL WORD COUNT LATEST @ BEGIN DUP WHILE >R 2DUP R@ NAME>STRING 2SWAP CONTAINS IF R@ NAME>STRING TYPE SPACE THEN R> @ REPEAT DROP 2DROP CR ; "
    .ascii ": DOCOL? >CODE @ ['] WORDS >CODE @ = ; "
    // SEE: walk colon body; skip inline data after LIT, (S"), BRANCH, 0BRANCH,
    // (LOOP), and (+LOOP). Ordinary xts (including (DO), (DOES>), EXIT) are 1 cell.
    .ascii ": SEE ' DUP DOCOL? IF 58 EMIT SPACE ELSE 67 EMIT 79 EMIT 68 EMIT 69 EMIT SPACE THEN DUP NAME>STRING TYPE SPACE DUP DOCOL? 0= IF DROP 40 EMIT 112 EMIT 114 EMIT 105 EMIT 109 EMIT 105 EMIT 116 EMIT 105 EMIT 118 EMIT 101 EMIT 41 EMIT CR EXIT THEN >BODY BEGIN DUP @ DUP EXIT-ADDR = IF 2DROP 59 EMIT CR EXIT THEN DUP LIT-ADDR = IF DROP 8 + DUP @ . 8 + ELSE DUP ['] (S\") = IF DROP 8 + DUP @ >R 8 + 83 EMIT 34 EMIT SPACE DUP R@ TYPE 34 EMIT SPACE R> + ALIGNED ELSE DUP NAME>STRING TYPE SPACE DUP BRANCH-ADDR = OVER 0BRANCH-ADDR = OR OVER ['] (LOOP) = OR OVER ['] (+LOOP) = OR IF DROP 8 + DUP @ . SPACE 8 + ELSE DROP 8 + THEN THEN THEN AGAIN ; "
    .ascii ": ALIAS CREATE LATEST @ >CODE SWAP >CODE @ SWAP ! ; "
    .ascii "' INCLUDE ALIAS FLOAD "
    // .FREE ( -- )  print free user-dictionary bytes (UNUSED is the cell value)
    .ascii ": .FREE UNUSED U. SPACE S\" bytes free\" TYPE CR ; "
    // Digit helpers for .ELAPSED (zero-padded; BASE forced to DECIMAL)
    .ascii ": .2DIG 10 /MOD 48 + EMIT 48 + EMIT ; "
    .ascii ": .3DIG 100 /MOD 48 + EMIT .2DIG ; "
    // .ELAPSED ( ms -- )  print milliseconds as HH:MM:SS.mmm (HH at least 2 digits)
    .ascii ": .ELAPSED BASE @ >R DECIMAL 1000 /MOD SWAP >R 60 /MOD SWAP >R 60 /MOD SWAP >R DUP 10 < IF 48 EMIT THEN <# #S #> TYPE 58 EMIT R> .2DIG 58 EMIT R> .2DIG 46 EMIT R> .3DIG R> BASE ! ; "
    // ELAPSED <name>  run name once; print wall time as HH:MM:SS.mmm
    .ascii ": ELAPSED ' >R MS@ R@ EXECUTE MS@ SWAP - .ELAPSED CR R> DROP ; "
    // DUMP ( addr u -- )  classic hex+ASCII dump, 16 bytes/line
    // .H2 byte as 2 hex digits; .HA address as 16 hex digits (BASE=HEX)
    .ascii ": .H2 255 AND <# # # #> TYPE ; "
    .ascii ": .HA <# # # # # # # # # # # # # # # # # #> TYPE ; "
    .ascii "VARIABLE DUMP-END "
    .ascii ": DUMP-LINE DUP .HA SPACE SPACE DUP 16 0 DO DUP I + DUMP-END @ U< IF DUP I + C@ .H2 SPACE ELSE SPACE SPACE SPACE THEN LOOP SPACE SPACE 16 0 DO DUP I + DUMP-END @ U< IF DUP I + C@ DUP BL 127 WITHIN 0= IF DROP BL THEN EMIT ELSE BL EMIT THEN LOOP DROP 16 + ; "
    .ascii ": DUMP BASE @ >R HEX OVER + DUMP-END ! BEGIN DUP DUMP-END @ U< WHILE CR DUMP-LINE REPEAT DROP CR R> BASE ! ; "
    // DEPTH — high-level so SEE shows TOS-cached layout (stack grows down):
    //   SP@ first (sample DSP before more pushes), SP0 = empty DSP, cells = diff/CELL.
    .ascii ": DEPTH SP@ SP0 SWAP - CELL / ; "
    // */MOD */  — double intermediate via M* then symmetric divide (matches ARM /)
    .ascii ": */MOD >R M* R> SM/REM ; "
    .ascii ": */ */MOD SWAP DROP ; "
    // ABORT / ABORT" — high-level; QUIT is pure CODE (XQUIT -> _do_quit).
    // ABORT: SP0 SP! clears data stack (TOS-cache model), then QUIT.
    .ascii ": ABORT SP0 SP! QUIT ; "
    .ascii ": ABORT\" STATE @ IF POSTPONE S\" POSTPONE TYPE POSTPONE ABORT ELSE 34 PARSE TYPE ABORT THEN ; IMMEDIATE "
    // FORGET <name>  remove name and all newer words; rewind HERE to name's header.
    // FIND leaves (c-addr 0|xt flag); 0= IF consumes flag — do not DROP xt after THEN.
    // Refuses names below USER-DICT (static kernel). HERE rewound via negative ALLOT.
    .ascii ": FORGET BL WORD FIND 0= IF DROP 63 EMIT CR EXIT THEN DUP USER-DICT U< IF DROP S\" protected\" TYPE CR EXIT THEN DUP @ LATEST ! DUP HERE - ALLOT DROP ; "
    // ANEW <name>  marker for reloadable modules (classic FPC/Win32Forth style).
    // First time: CREATE name. Later: EXECUTE name (DOES> FORGETs itself) then re-CREATE.
    .ascii ": ANEW >IN @ >R BL WORD FIND IF EXECUTE ELSE DROP THEN R> >IN ! CREATE LATEST @ , DOES> @ DUP @ LATEST ! DUP HERE - ALLOT DROP ; "
    // ON / OFF — store 1 or 0 at addr (classic: FILE-ECHO ON  /  FILE-ECHO OFF)
    .ascii ": ON 1 SWAP ! ; "
    .ascii ": OFF 0 SWAP ! ; "

    // --- 6. Core Ext (mostly high-level; 2>R/2R>/2R@ are CODE — colon would clobber IP) ---
    .ascii ": U> SWAP U< ; "
    // U.R ( u n -- ) right-justify u in a field of n characters (no trailing space)
    .ascii ": U.R >R <# #S #> R> OVER - 0 MAX SPACES TYPE ; "
    .ascii ": HOLDS BEGIN DUP WHILE 1- 2DUP + C@ HOLD REPEAT 2DROP ; "
    .ascii ": COMPILE, , ; "
    .ascii ": [COMPILE] ?COMP BL WORD FIND 0= IF DROP EXIT THEN DROP , ; IMMEDIATE "
    .ascii ": .( 41 PARSE TYPE ; IMMEDIATE "
    .ascii ": BUFFER: CREATE ALLOT ; "
    // VALUE / TO — DOES> body: does_ip at >BODY, value at >BODY CELL+
    .ascii ": VALUE CREATE , DOES> @ ; "
    .ascii ": TO ' >BODY CELL+ STATE @ IF POSTPONE LITERAL POSTPONE ! ELSE ! THEN ; IMMEDIATE "
    // DEFER family — default action ABORT until IS
    .ascii ": DEFER CREATE ['] ABORT , DOES> @ EXECUTE ; "
    .ascii ": DEFER@ >BODY CELL+ @ ; "
    .ascii ": DEFER! >BODY CELL+ ! ; "
    .ascii ": IS STATE @ IF POSTPONE ['] POSTPONE DEFER! ELSE ' DEFER! THEN ; IMMEDIATE "
    .ascii ": ACTION-OF STATE @ IF POSTPONE ['] POSTPONE DEFER@ ELSE ' DEFER@ THEN ; IMMEDIATE "
    // MARKER — executing name restores dictionary to just before MARKER was defined
    .ascii ": MARKER CREATE LATEST @ , DOES> @ DUP @ LATEST ! DUP HERE - ALLOT DROP ; "

    .byte 0  // null terminator

// Trampoline for REPL execution: IP points here, then after the word
// finishes via NEXT, it follows this cell to dict_restart which jumps back
// to _interpret_loop.
.align 8
dict_restart:                   // hidden entry, not in user dictionary
    .quad 0                     // link (end of chain)
    .quad 8                     // length=8 "RESTART" (won't be searched)
    .quad XRESTART              // code field
    .asciz "RESTART"
dict_restart_end:
    .space 8                    // pad to 8-byte boundary

.align 8
restart_cell:   .quad 0
next_diag:      .skip 32  // x5, x19, x22, x20 for crash debugging
catch_ok_cell:  .quad 0
    .quad dict_restart          // cell IP points to when executing from REPL

// ============================================================================
// Static Dictionary (native / CODE words)
// Stack comments use Forth notation ( before -- after ).
// "xt" = dictionary entry address (see header). "flag" = 0 | -1.
// ============================================================================
.align 8

dict_exit:  // EXIT ( -- )  return from colon definition
    .quad 0                 // link
    .quad 4                 // len
    .quad DOEXIT            // code
    .asciz "EXIT"
    .space 4

.align 8
dict_semi:  // ; ( -- ) immediate
    .quad dict_exit         // link -> EXIT
    .quad 0x101             // immediate|1
    .quad XSEMI             // code
    .byte 59
    .space 7

.align 8
dict_lit:  // LIT ( -- x )
    .quad dict_semi
    .quad 3
    .quad XLit
    .asciz "LIT"
    .space 5

.align 8
dict_dup:  // DUP ( x -- x x )
    .quad dict_lit
    .quad 3
    .quad XDUP
    .asciz "DUP"
    .space 5

.align 8
dict_drop:  // DROP ( x -- )
    .quad dict_dup
    .quad 4
    .quad XDROP
    .asciz "DROP"
    .space 4

.align 8
dict_swap:  // SWAP ( a b -- b a )
    .quad dict_drop
    .quad 4
    .quad XSWAP
    .asciz "SWAP"
    .space 4

.align 8
dict_over:  // OVER ( a b -- a b a )
    .quad dict_swap
    .quad 4
    .quad XOVER
    .asciz "OVER"
    .space 4

.align 8
dict_rot:  // ROT ( a b c -- b c a )
    .quad dict_over
    .quad 3
    .quad XROT
    .asciz "ROT"
    .space 5

.align 8
dict_nip:  // NIP ( a b -- b )
    .quad dict_rot
    .quad 3
    .quad XNIP
    .asciz "NIP"
    .space 5

.align 8
dict_tuck:  // TUCK ( a b -- b a b )
    .quad dict_nip
    .quad 4
    .quad XTUCK
    .asciz "TUCK"
    .space 4

.align 8
dict_pick:  // PICK ( u -- x )
    .quad dict_tuck
    .quad 4
    .quad XPICK
    .asciz "PICK"
    .space 4

.align 8
dict_tor:  // >R ( x -- ) (R: -- x )
    .quad dict_pick
    .quad 2
    .quad XTOR
    .asciz ">R"
    .space 6

.align 8
dict_rto:  // R> ( -- x ) (R: x -- )
    .quad dict_tor
    .quad 2
    .quad XRTO
    .asciz "R>"
    .space 6

.align 8
dict_rfetch:  // R@ ( -- x ) (R: x -- x )
    .quad dict_rto
    .quad 2
    .quad XRFETCH
    .asciz "R@"
    .space 6

.align 8
dict_plus:  // + ( n1 n2 -- n3 )
    .quad dict_rfetch
    .quad 1
    .quad XPLUS
    .byte 43
    .space 7

.align 8
dict_minus:  // - ( n1 n2 -- n3 )
    .quad dict_plus
    .quad 1
    .quad XMINUS
    .byte 45
    .space 7

.align 8
dict_star:  // * ( n1 n2 -- n3 )
    .quad dict_minus
    .quad 1
    .quad XSTAR
    .byte 42
    .space 7

.align 8
dict_slash:  // / ( n1 n2 -- n3 )
    .quad dict_star
    .quad 1
    .quad XSLASH
    .byte 47
    .space 7

.align 8
dict_mod:  // MOD ( n1 n2 -- n3 )
    .quad dict_slash
    .quad 3
    .quad XMOD
    .asciz "MOD"
    .space 5

.align 8
dict_slmod:  // /MOD ( n1 n2 -- rem quot )
    .quad dict_mod
    .quad 4
    .quad XSLMOD
    .asciz "/MOD"
    .space 4

.align 8
dict_equal:  // = ( n1 n2 -- flag )
    .quad dict_slmod
    .quad 1
    .quad XEQUAL
    .byte 61
    .space 7

.align 8
dict_less:  // < ( n1 n2 -- flag )
    .quad dict_equal
    .quad 1
    .quad XLESS
    .byte 60
    .space 7

.align 8
dict_greater:  // > ( n1 n2 -- flag )
    .quad dict_less
    .quad 1
    .quad XGREATER
    .byte 62
    .space 7

.align 8
dict_uless:  // U< ( u1 u2 -- flag )
    .quad dict_greater
    .quad 2
    .quad XULESS
    .asciz "U<"
    .space 6

.align 8
dict_and:  // AND ( x1 x2 -- x3 )
    .quad dict_uless
    .quad 3
    .quad XAND
    .asciz "AND"
    .space 5

.align 8
dict_or:  // OR ( x1 x2 -- x3 )
    .quad dict_and
    .quad 2
    .quad XORR
    .asciz "OR"
    .space 6

.align 8
dict_xor:  // XOR ( x1 x2 -- x3 )
    .quad dict_or
    .quad 3
    .quad XXOR
    .asciz "XOR"
    .space 5

.align 8
dict_invert:  // INVERT ( x1 -- x2 )
    .quad dict_xor
    .quad 6
    .quad XINVERT
    .asciz "INVERT"
    .space 2

.align 8
dict_zequal:  // 0= ( x -- flag )
    .quad dict_invert
    .quad 2
    .quad XZEQUAL
    .asciz "0="
    .space 6

.align 8
dict_zless:  // 0< ( n -- flag )
    .quad dict_zequal
    .quad 2
    .quad XZLESS
    .asciz "0<"
    .space 6

.align 8
dict_true:  // TRUE ( -- -1 )
    .quad dict_zless
    .quad 4
    .quad XTRUE
    .asciz "TRUE"
    .space 4

.align 8
dict_false:  // FALSE ( -- 0 )
    .quad dict_true
    .quad 5
    .quad XFALSE
    .asciz "FALSE"
    .space 3

.align 8
dict_oneplus:  // 1+ ( n -- n+1 )
    .quad dict_false
    .quad 2
    .quad XONEPLUS
    .asciz "1+"
    .space 6

.align 8
dict_oneminus:  // 1- ( n -- n-1 )
    .quad dict_oneplus
    .quad 2
    .quad XONEMINUS
    .asciz "1-"
    .space 6

.align 8
dict_cell:  // CELL ( -- 8 )
    .quad dict_oneminus
    .quad 4
    .quad XCELL
    .asciz "CELL"
    .space 4

.align 8
dict_cells:  // CELLS ( n -- n*8 )
    .quad dict_cell
    .quad 5
    .quad XCELLS
    .asciz "CELLS"
    .space 3

.align 8
dict_fetch:  // @ ( addr -- x )
    .quad dict_cells
    .quad 1
    .quad XFETCH
    .byte 64
    .space 7

.align 8
dict_store:  // ! ( x addr -- )
    .quad dict_fetch
    .quad 1
    .quad XSTORE
    .byte 33
    .space 7

.align 8
dict_cfetch:  // C@ ( addr -- char )
    .quad dict_store
    .quad 2
    .quad XCFETCH
    .asciz "C@"
    .space 6

.align 8
dict_cstore:  // C! ( char addr -- )
    .quad dict_cfetch
    .quad 2
    .quad XCSTORE
    .asciz "C!"
    .space 6

.align 8
dict_plusstore:  // +! ( n addr -- )
    .quad dict_cstore
    .quad 2
    .quad XPLUSSTORE
    .asciz "+!"
    .space 6

.align 8
dict_emit:  // EMIT ( char -- )
    .quad dict_plusstore
    .quad 4
    .quad XEMIT
    .asciz "EMIT"
    .space 4

.align 8
dict_key:  // KEY ( -- char )
    .quad dict_emit
    .quad 3
    .quad XKEY
    .asciz "KEY"
    .space 5

.align 8
dict_cr:  // CR ( -- )
    .quad dict_key
    .quad 2
    .quad XCR
    .asciz "CR"
    .space 6

.align 8
dict_dot:  // . ( n -- )
    .quad dict_cr
    .quad 1
    .quad XDOT
    .byte 46
    .space 7

.align 8
dict_udot:  // U. ( u -- )
    .quad dict_dot
    .quad 2
    .quad XUDOT
    .asciz "U."
    .space 6

.align 8
dict_dots:  // .S ( -- )
    .quad dict_udot
    .quad 2
    .quad XDOTS
    .asciz ".S"
    .space 6

.align 8
dict_type:  // TYPE ( addr u -- )
    .quad dict_dots
    .quad 4
    .quad XTYPE
    .asciz "TYPE"
    .space 4

.align 8
dict_state:  // STATE ( -- addr )
    .quad dict_type
    .quad 5
    .quad XSTATE
    .asciz "STATE"
    .space 3

.align 8
dict_base:  // BASE ( -- addr )
    .quad dict_state
    .quad 4
    .quad XBASE
    .asciz "BASE"
    .space 4

.align 8
dict_rbrack:  // ] ( -- ) switch to compile
    .quad dict_base
    .quad 1
    .quad XRBRA
    .byte 93
    .space 7

.align 8
dict_lbrack:  // [ ( -- ) immediate, switch to interpret
    .quad dict_rbrack
    .quad 0x101
    .quad XLBRA
    .byte 91
    .space 7

.align 8
dict_dp:  // DP ( -- a-addr )  dictionary pointer variable
    .quad dict_lbrack
    .quad 2
    .quad XDP
    .asciz "DP"
    .space 6

.align 8
dict_here:  // HERE ( -- addr )  also redefined high-level as DP @
    .quad dict_dp
    .quad 4
    .quad XHERE
    .asciz "HERE"
    .space 4

.align 8
dict_alot:  // ALLOT ( n -- )
    .quad dict_here
    .quad 5
    .quad XALLOT
    .asciz "ALLOT"
    .space 3

.align 8
dict_comma:  // , ( x -- )
    .quad dict_alot
    .quad 1
    .quad XCOMMA
    .byte 44
    .space 7

.align 8
dict_find:  // FIND ( c-addr -- c-addr 0 | xt 1 | xt -1 ) ANS counted string
    .quad dict_comma
    .quad 4
    .quad XFIND
    .asciz "FIND"
    .space 4

.align 8
dict_tick:  // ' ( "<spaces>name" -- xt )  xt = dictionary entry address
    .quad dict_find
    .quad 1
    .quad XTICK
    .byte 39
    .space 7

.align 8
dict_execute:  // EXECUTE ( xt -- )  run dictionary entry
    .quad dict_tick
    .quad 7
    .quad XEXECUTE
    .asciz "EXECUTE"
    .space 1

.align 8
dict_literal:  // LITERAL ( x -- ) immediate
    .quad dict_execute
    .quad 0x107             // immediate | len=7
    .quad XLITERAL
    .asciz "LITERAL"
    .space 1

.align 8
dict_immediate:  // IMMEDIATE ( -- )
    .quad dict_literal
    .quad 9
    .quad XIMMEDIATE
    .asciz "IMMEDIATE"
    .space 7

.align 8
dict_colon:  // : ( "name" -- )
    .quad dict_immediate
    .quad 1
    .quad XCOLON
    .byte 58
    .space 7

.align 8
dict_create:  // CREATE ( "name" -- )
    .quad dict_colon
    .quad 6
    .quad XCREATE
    .asciz "CREATE"
    .space 2

.align 8
dict_0branch:  // 0BRANCH ( -- )
    .quad dict_create
    .quad 7
    .quad X0Branch
    .asciz "0BRANCH"
    .space 1

.align 8
dict_branch:  // BRANCH ( -- )
    .quad dict_0branch
    .quad 6
    .quad XBranch
    .asciz "BRANCH"
    .space 2

.align 8
dict_bye:  // BYE ( -- )
    .quad dict_branch
    .quad 3
    .quad XBYE
    .asciz "BYE"
    .space 5

.align 8
dict_include:  // INCLUDE ( "name" -- )
    .quad dict_bye
    .quad 7
    .quad XINCLUDE
    .asciz "INCLUDE"
    .space 1

.align 8
dict_latest:  // LATEST ( -- addr )
    .quad dict_include
    .quad 6
    .quad XLATEST
    .asciz "LATEST"
    .space 2

.align 8
dict_qdup:  // ?DUP ( x -- x x | 0 )
    .quad dict_latest
    .quad 4
    .quad XQDUP
    .asciz "?DUP"
    .space 4

.align 8
dict_bracket_tick:  // ['] ( "name" -- entry ) immediate
    .quad dict_qdup
    .quad 0x103             // immediate | len=3
    .quad XBRACKET_TICK
    .byte 91        // '['
    .byte 39        // '''
    .byte 93        // ']'
    .space 5

.align 8
dict_lit_addr:  // LIT-ADDR ( -- addr )
    .quad dict_bracket_tick
    .quad 8
    .quad XLIT_ADDR
    .asciz "LIT-ADDR"
    .space 8

.align 8
dict_0br_addr:  // 0BRANCH-ADDR ( -- addr )
    .quad dict_lit_addr
    .quad 12
    .quad X0BRANCH_ADDR
    .asciz "0BRANCH-ADDR"
    .space 4

.align 8
dict_br_addr:  // BRANCH-ADDR ( -- addr )
    .quad dict_0br_addr
    .quad 11
    .quad XBRANCH_ADDR
    .asciz "BRANCH-ADDR"
    .space 5

.align 8
dict_exit_addr:  // EXIT-ADDR ( -- addr )
    .quad dict_br_addr
    .quad 9
    .quad XEXIT_ADDR
    .asciz "EXIT-ADDR"
    .space 7

.align 8
dict_negate:  // NEGATE ( n1 -- n2 ) ANS
    .quad dict_exit_addr
    .quad 6
    .quad XNEGATE
    .asciz "NEGATE"
    .space 2

.align 8
dict_abs:  // ABS ( n -- u ) ANS
    .quad dict_negate
    .quad 3
    .quad XABS
    .asciz "ABS"
    .space 5

.align 8
dict_min:  // MIN ( n1 n2 -- n3 ) ANS
    .quad dict_abs
    .quad 3
    .quad XMIN
    .asciz "MIN"
    .space 5

.align 8
dict_max:  // MAX ( n1 n2 -- n3 ) ANS
    .quad dict_min
    .quad 3
    .quad XMAX
    .asciz "MAX"
    .space 5

.align 8
dict_lshift:  // LSHIFT ( x1 u -- x2 ) ANS
    .quad dict_max
    .quad 6
    .quad XLSHIFT
    .asciz "LSHIFT"
    .space 2

.align 8
dict_rshift:  // RSHIFT ( x1 u -- x2 ) ANS
    .quad dict_lshift
    .quad 6
    .quad XRSHIFT
    .asciz "RSHIFT"
    .space 2

.align 8
dict_nequal:  // <> ( x1 x2 -- flag ) ANS
    .quad dict_rshift
    .quad 2
    .quad XNEQUAL
    .asciz "<>"
    .space 6

.align 8
dict_parse:  // PARSE ( char "ccc<char>" -- c-addr u ) ANS
    .quad dict_nequal
    .quad 5
    .quad XPARSE
    .asciz "PARSE"
    .space 3

.align 8
dict_word:  // WORD ( char "<chars>ccc<char>" -- c-addr ) ANS
    .quad dict_parse
    .quad 4
    .quad XWORD
    .asciz "WORD"
    .space 4

.align 8
dict_backslash:  // \ ( -- ) IMMEDIATE  ANS line comment
    .quad dict_word
    .quad 0x101
    .quad XBACKSLASH
    .byte 92
    .space 7

.align 8
dict_paren:  // ( ( -- ) IMMEDIATE  ANS paren comment
    .quad dict_backslash
    .quad 0x101
    .quad XPAREN
    .byte 40
    .space 7

.align 8
dict_docon_addr:  // DOCON-ADDR ( -- addr )  code address of DOCON (for CONSTANT)
    .quad dict_paren
    .quad 10
    .quad XDOCON_ADDR
    .asciz "DOCON-ADDR"
    .space 6

.align 8
dict_source:  // SOURCE ( -- c-addr u ) ANS
    .quad dict_docon_addr
    .quad 6
    .quad XSOURCE
    .asciz "SOURCE"
    .space 2

.align 8
dict_to_in:  // >IN ( -- a-addr ) ANS
    .quad dict_source
    .quad 3
    .quad XTOIN
    .asciz ">IN"
    .space 5

.align 8
dict_slit:  // (S") ( -- c-addr u ) runtime helper for S" / ."
    .quad dict_to_in
    .quad 4
    .quad XSLIT
    .asciz "(S\")"
    .space 4

.align 8
dict_squote:  // S" ( -- c-addr u ) IMMEDIATE ANS
    .quad dict_slit
    .quad 0x102
    .quad XSQUOTE
    .byte 83, 34                    // S"
    .space 6

.align 8
dict_dotquote:  // ." ( -- ) IMMEDIATE ANS
    .quad dict_squote
    .quad 0x102
    .quad XDOTQ
    .byte 46, 34                    // ."
    .space 6


.align 8
dict_do_rt:  // (DO) ( limit index -- ) R: -- limit index
    .quad dict_dotquote
    .quad 4
    .quad XDO_RT
    .asciz "(DO)"
    .space 4

.align 8
dict_qdo_rt:  // (?DO) ( limit index -- )
    .quad dict_do_rt
    .quad 5
    .quad XQDO_RT
    .asciz "(?DO)"
    .space 3

.align 8
dict_loop_rt:  // (LOOP) ( -- )
    .quad dict_qdo_rt
    .quad 6
    .quad XLOOP_RT
    .asciz "(LOOP)"
    .space 2

.align 8
dict_ploop_rt:  // (+LOOP) ( n -- )
    .quad dict_loop_rt
    .quad 7
    .quad XPLUSLOOP_RT
    .asciz "(+LOOP)"
    .space 1

.align 8
dict_i:  // I ( -- n )
    .quad dict_ploop_rt
    .quad 1
    .quad XI
    .byte 73
    .space 7

.align 8
dict_j:  // J ( -- n )
    .quad dict_i
    .quad 1
    .quad XJ
    .byte 74
    .space 7

.align 8
dict_unloop:  // UNLOOP ( -- )
    .quad dict_j
    .quad 6
    .quad XUNLOOP
    .asciz "UNLOOP"
    .space 2

.align 8
dict_leave:  // LEAVE ( -- )
    .quad dict_unloop
    .quad 5
    .quad XLEAVE
    .asciz "LEAVE"
    .space 3

.align 8
dict_does_rt:  // (DOES>) ( -- )
    .quad dict_leave
    .quad 7
    .quad XDOES_RT
    .asciz "(DOES>)"
    .space 1

.align 8
dict_pad:  // PAD ( -- c-addr )
    .quad dict_does_rt
    .quad 3
    .quad XPAD
    .asciz "PAD"
    .space 5

.align 8
dict_does:  // DOES> ( -- ) IMMEDIATE
    .quad dict_pad
    .quad 0x105
    .quad XDOES
    .asciz "DOES>"
    .space 3

.align 8
dict_evaluate:  // EVALUATE ( c-addr u -- ) ANS
    .quad dict_does
    .quad 8
    .quad XEVALUATE
    .asciz "EVALUATE"
    .space 8

.align 8
dict_catch:  // CATCH ( i*x xt -- j*x 0 | i*x n ) ANS
    .quad dict_evaluate
    .quad 5
    .quad XCATCH
    .asciz "CATCH"
    .space 3

.align 8
dict_throw:  // THROW ( k -- ) ANS
    .quad dict_catch
    .quad 5
    .quad XTHROW
    .asciz "THROW"
    .space 3

.align 8
dict_catch_ok:  // (CATCH-OK) internal
    .quad dict_throw
    .quad 10
    .quad XCATCH_OK
    .asciz "(CATCH-OK)"
    .space 6

.align 8
dict_contains:  // CONTAINS ( hay-a hay-u ned-a ned-u -- flag )
    .quad dict_catch_ok
    .quad 8
    .quad XCONTAINS
    .asciz "CONTAINS"
    .space 8

.align 8
dict_msfetch:  // MS@ ( -- u ) milliseconds (wall clock)
    .quad dict_contains
    .quad 3
    .quad XMSFETCH
    .asciz "MS@"
    .space 5

.align 8
dict_unused:  // UNUSED ( -- u ) free user dictionary bytes
    .quad dict_msfetch
    .quad 6
    .quad XUNUSED
    .asciz "UNUSED"
    .space 2

.align 8
dict_redef_warning:  // REDEF-WARNING ( -- addr )  warn on redefine when nonzero
    .quad dict_unused
    .quad 13
    .quad XREDEF_WARNING
    .asciz "REDEF-WARNING"
    .space 3

.align 8
dict_user_dict:  // USER-DICT ( -- addr )  base of user dictionary
    .quad dict_redef_warning
    .quad 9
    .quad XUSER_DICT
    .asciz "USER-DICT"
    .space 7

.align 8
dict_sp0:  // SP0 ( -- addr )  empty data-stack DSP
    .quad dict_user_dict
    .quad 3
    .quad XSP0
    .asciz "SP0"
    .space 5

.align 8
dict_spfetch:  // SP@ ( -- addr )  current DSP
    .quad dict_sp0
    .quad 3
    .quad XSPFETCH
    .asciz "SP@"
    .space 5

.align 8
dict_spstore:  // SP! ( addr -- )  set DSP; clear TOS cache
    .quad dict_spfetch
    .quad 3
    .quad XSPSTORE
    .asciz "SP!"
    .space 5

.align 8
dict_spaces:  // SPACES ( n -- )
    .quad dict_spstore
    .quad 6
    .quad XSPACES
    .asciz "SPACES"
    .space 2

.align 8
dict_ccomma:  // C, ( char -- )
    .quad dict_spaces
    .quad 2
    .quad XCCOMMA
    .asciz "C,"
    .space 6

.align 8
dict_stod:  // S>D ( n -- d )
    .quad dict_ccomma
    .quad 3
    .quad XSTOD
    .asciz "S>D"
    .space 5

.align 8
dict_twostar:  // 2* ( x1 -- x2 )
    .quad dict_stod
    .quad 2
    .quad XTWOSTAR
    .asciz "2*"
    .space 6

.align 8
dict_twoslash:  // 2/ ( x1 -- x2 )
    .quad dict_twostar
    .quad 2
    .quad XTWOSLASH
    .asciz "2/"
    .space 6

.align 8
dict_twofetch:  // 2@ ( a-addr -- x1 x2 )
    .quad dict_twoslash
    .quad 2
    .quad XTWOFETCH
    .asciz "2@"
    .space 6

.align 8
dict_twostore:  // 2! ( x1 x2 a-addr -- )
    .quad dict_twofetch
    .quad 2
    .quad XTWOSTORE
    .asciz "2!"
    .space 6

.align 8
dict_umstar:  // UM* ( u1 u2 -- ud )
    .quad dict_twostore
    .quad 3
    .quad XUMSTAR
    .asciz "UM*"
    .space 5

.align 8
dict_mstar:  // M* ( n1 n2 -- d )
    .quad dict_umstar
    .quad 2
    .quad XMSTAR
    .asciz "M*"
    .space 6

.align 8
dict_ummod:  // UM/MOD ( ud u1 -- u2 u3 )
    .quad dict_mstar
    .quad 6
    .quad XUMMOD
    .asciz "UM/MOD"
    .space 2

.align 8
dict_smrem:  // SM/REM ( d1 n1 -- n2 n3 )
    .quad dict_ummod
    .quad 6
    .quad XSMREM
    .asciz "SM/REM"
    .space 2

.align 8
dict_fmmod:  // FM/MOD ( d1 n1 -- n2 n3 )
    .quad dict_smrem
    .quad 6
    .quad XFMMOD
    .asciz "FM/MOD"
    .space 2

.align 8
dict_quit:  // QUIT ( -- )  CODE outer interpreter
    .quad dict_fmmod
    .quad 4
    .quad XQUIT
    .asciz "QUIT"
    .space 4

.align 8
dict_source_id:  // SOURCE-ID ( -- n )
    .quad dict_quit
    .quad 9
    .quad XSOURCE_ID
    .asciz "SOURCE-ID"
    .space 7

.align 8
dict_refill:  // REFILL ( -- flag )
    .quad dict_source_id
    .quad 6
    .quad XREFILL
    .asciz "REFILL"
    .space 2

.align 8
dict_accept:  // ACCEPT ( c-addr +n1 -- +n2 )
    .quad dict_refill
    .quad 6
    .quad XACCEPT
    .asciz "ACCEPT"
    .space 2

.align 8
dict_to_number:  // >NUMBER ( ud1 c-addr1 u1 -- ud2 c-addr2 u2 )
    .quad dict_accept
    .quad 7
    .quad XTONUMBER
    .asciz ">NUMBER"
    .space 1

.align 8
dict_environment_q:  // ENVIRONMENT? ( c-addr u -- false | i*x true )
    .quad dict_to_number
    .quad 12
    .quad XENVIRONMENT_Q
    .asciz "ENVIRONMENT?"
    .space 4

.align 8
dict_file_echo:  // FILE-ECHO ( -- addr )  echo INCLUDE lines when nonzero
    .quad dict_environment_q
    .quad 9
    .quad XFILE_ECHO
    .asciz "FILE-ECHO"
    .space 7

.align 8
dict_parse_name:  // PARSE-NAME ( -- c-addr u )
    .quad dict_file_echo
    .quad 10
    .quad XPARSE_NAME
    .asciz "PARSE-NAME"
    .space 6

.align 8
dict_2tor:  // 2>R ( x1 x2 -- ) ( R: -- x1 x2 )
    .quad dict_parse_name
    .quad 3
    .quad X2TOR
    .asciz "2>R"
    .space 5

.align 8
dict_2rto:  // 2R> ( -- x1 x2 ) ( R: x1 x2 -- )
    .quad dict_2tor
    .quad 3
    .quad X2RTO
    .asciz "2R>"
    .space 5

.align 8
dict_2rfetch:  // 2R@ ( -- x1 x2 ) ( R: x1 x2 -- x1 x2 )
    .quad dict_2rto
    .quad 3
    .quad X2RFETCH
    .asciz "2R@"
    .space 5

.align 8
dict_roll:  // ROLL ( xu ... x0 u -- ... xu )
    .quad dict_2rfetch
    .quad 4
    .quad XROLL
    .asciz "ROLL"
    .space 4

.align 8
dict_noname:  // :NONAME ( -- )  ; leaves xt
    .quad dict_roll
    .quad 7
    .quad XNONAME
    .asciz ":NONAME"
    .space 1

.align 8
dict_cstr:  // (C") ( -- c-addr ) runtime counted string
    .quad dict_noname
    .quad 4
    .quad XCSTR
    .asciz "(C\")"
    .space 4

.align 8
dict_cquote:  // C" ( -- c-addr ) IMMEDIATE
    .quad dict_cstr
    .quad 0x102
    .quad XCQUOTE
    .byte 67, 34                   // C"
    .space 6

.align 8
dict_sescape:  // S\" ( -- c-addr u ) IMMEDIATE
    .quad dict_cquote
    .quad 0x103
    .quad XSESCAPE
    .byte 83, 92, 34               // S\"
    .space 5

.align 8
dict_save_input:  // SAVE-INPUT ( -- xn..x1 n )
    .quad dict_sescape
    .quad 10
    .quad XSAVE_INPUT
    .asciz "SAVE-INPUT"
    .space 6

.align 8
dict_restore_input:  // RESTORE-INPUT ( xn..x1 n -- flag )
    .quad dict_save_input
    .quad 13
    .quad XRESTORE_INPUT
    .asciz "RESTORE-INPUT"
    .space 3

// ============================================================================
// User dictionary space (grows upward)
// Size = USER_DICT_SIZE (128 KiB); keep in sync with XUNUSED
// ============================================================================
.align 8
user_dict_area: .skip USER_DICT_SIZE
