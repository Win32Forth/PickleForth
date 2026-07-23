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
// ANS Forth (2012) status — PickleForth is NOT a conforming ANS system yet.
// ----------------------------------------------------------------------------
// Goal: grow toward ANS Core (and useful Core Ext) for words we implement.
//
// ANS-oriented subset (cell = 8 bytes / 64-bit). Not a full conforming system.
//
// Core-like (implemented, stack/semantics intended to match ANS):
//   Stack: DUP DROP SWAP OVER ROT PICK ?DUP 2DUP 2DROP 2SWAP 2OVER
//   Return: >R R> R@
//   Arith: + - * / MOD /MOD 1+ 1- NEGATE ABS MIN MAX LSHIFT RSHIFT
//   Logic: AND OR XOR INVERT
//   Compare: = <> < > U< 0= 0< 0<> 0> >= <= WITHIN  TRUE FALSE
//   Memory: @ ! C@ C! +! FILL ERASE  CELL+ CELLS CHAR+ CHARS ALIGN ALIGNED
//   Parse:  WORD PARSE  CHAR [CHAR]  BL
//   Comments: \  (
//   I/O: EMIT KEY CR TYPE SPACE . U.
//   Numeric input honors BASE; DECIMAL HEX
//   Compile: : ; CREATE VARIABLE CONSTANT , ALLOT HERE [ ] IMMEDIATE
//            LITERAL ' ['] EXECUTE RECURSE
//   Control: IF ELSE THEN BEGIN UNTIL AGAIN WHILE REPEAT EXIT
//
// Present but non-ANS or different (fix later):
//   FIND     — we use ( c-addr u ); ANS FIND uses counted string only
//   ' / xt   — xt is dictionary entry address (ANS xt is opaque)
//   >BODY    — also used for colon bodies (ANS: CREATE words)
//   >CODE >NAME >FLAGS >LINK NAME>STRING DOCOL? DOCON-ADDR — extensions
//   LIT BRANCH 0BRANCH + *-ADDR plumbing — internal
//   LATEST STATE BASE — address-pushing (BASE is ANS-like variable)
//   INCLUDE FLOAD ALIAS SEE WORDS .S — extensions / file-ish
//   CELL     — push 8; not an ANS word (CELL+ / CELLS are ANS)
//
// Still missing major ANS Core pieces:
//   SOURCE >IN EVALUATE REFILL
//   S" ." C"  MOVE CMOVE
//   VALUE TO DOES> POSTPONE
//   Pictured numeric output <# # #S #> HOLD SIGN  >NUMBER
//   DO LOOP +LOOP I J LEAVE UNLOOP  CASE OF ENDOF ENDCASE
//   CATCH THROW  ENVIRONMENT?
//
// Implementation notes:
//   - Indirect threaded; compiled cells are dictionary entry addresses
//   - Flags true=-1 false=0; case-insensitive find
//   - Prefer high-level Forth in forth_init_str; asm only when needed
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
    adrp x0, dict_docon_addr@page
    add  x0, x0, dict_docon_addr@pageoff
    str  x0, [x24]

    // HERE = user_dict_area
    adrp x0, here_ptr@page
    add  x0, x0, here_ptr@pageoff
    adrp x1, user_dict_area@page
    add  x1, x1, user_dict_area@pageoff
    str  x1, [x0]

    // Patch all dict entry code fields (Mach-O chained fixups broken for .quad cross-section refs)
    bl _patch_dict

    // Print welcome via raw SVC
    mov x0, #1
    adrp x1, str_hello@page
    add x1, x1, str_hello@pageoff
    mov x2, #17
    mov x16, #4
    svc #0x80

    // Initialize Forth from init string
    // Set word_cursor to init string
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    adrp x1, forth_init_str@page
    add x1, x1, forth_init_str@pageoff
    str x1, [x0]
    
    // Jump to interpreter loop to process init string
    // When done, it will print "ok" and go to _quit_loop (REPL)
    b _interpret_loop

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
    str x20, [x22, #-8]!
    DICT_BODY_ADDR x20, x21
    NEXT

DOCON:
    str x20, [x22, #-8]!
    DICT_BODY_ADDR x0, x21
    ldr x20, [x0]
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
    PATCH_LINK dict_here, dict_lbrack
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

    .purgem PATCH_CODE
    .purgem PATCH_LINK
    ret

// ============================================================================
// Stack Primitives
// ============================================================================
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
    // x0 was clobbered by SAVE_VM? No — SAVE_VM only stores x19-x24.
    // But we need the value: it is still in x0 until something overwrites it.
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

// HERE ( -- addr ) push current dictionary pointer
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

// FIND ( addr u -- xt -1 | addr u 0 ) find word in dictionary
// Stack: TOS=u, second=addr
XFIND:
    mov x1, x20        // x1 = u
    ldr x0, [x22]      // x0 = addr
    bl _find_word
    cbz x0, _xfind_not
    // Found: ( xt -1 )
    str x0, [x22]      // replace addr with xt
    mov x20, #-1
    NEXT
_xfind_not:
    // Not found: ( addr u 0 )
    str x20, [x22, #-8]!   // push u under TOS
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

// EXECUTE ( xt -- ) execute a dictionary entry
XEXECUTE:
    mov x0, x20
    ldr x20, [x22], #8
    // Set up trampoline so NEXT after the word returns to interpreter
    adrp x19, dict_restart@page
    add  x19, x19, dict_restart@pageoff
    adrp x1, XRESTART@page
    add  x1, x1, XRESTART@pageoff
    str  x1, [x19, #16]
    adrp x1, restart_cell@page
    add  x1, x1, restart_cell@pageoff
    str  x19, [x1]
    mov  x19, x1
    mov  x21, x0
    ldr  x1, [x0, #16]  // load code field (native code pointer)
    br   x1

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

// ; ( -- ) immediate: end colon definition
XSEMI:
    // Compile EXIT entry address
    adrp x0, dict_exit@page
    add x0, x0, dict_exit@pageoff
    bl _compile_cell
    // Set state to interpret mode
    adrp x0, state_var@page
    add x0, x0, state_var@pageoff
    str xzr, [x0]
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
    ldp x25, x26, [sp], #16
    RESTORE_VM
    // Set word_cursor to file_buffer
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    adrp x1, file_buffer@page
    add x1, x1, file_buffer@pageoff
    str x1, [x0]
    NEXT

_include_fail_restore:
    ldp x25, x26, [sp], #16
    RESTORE_VM
_include_fail:
    mov x0, #1
    adrp x1, str_quest@page
    add x1, x1, str_quest@pageoff
    mov x2, #2
    mov x16, #4
    svc #0x80
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

// PARSE ( char "ccc<char>" -- c-addr u )
// From word_cursor to delimiter or end; consumes delimiter if found.
// Does not skip leading delimiters (ANS PARSE).
XPARSE:
    mov w7, w20                     // delimiter
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    ldr x2, [x0]                    // c-addr = start
    mov x3, x2
_parse_scan:
    ldrb w4, [x3]
    cbz w4, _parse_eos
    cmp w4, w7
    b.eq _parse_found
    add x3, x3, #1
    b _parse_scan
_parse_found:
    sub x5, x3, x2                  // u
    add x3, x3, #1                  // skip delimiter
    str x3, [x0]
    b _parse_push
_parse_eos:
    sub x5, x3, x2
    str x3, [x0]
_parse_push:
    // Replace char (TOS) with c-addr, then push u
    mov x20, x2
    str x20, [x22, #-8]!
    mov x20, x5
    NEXT

// WORD ( char "<chars>ccc<char>" -- c-addr )
// Skip leading delimiters, parse until delimiter, store counted string
// in word_scratch (transient). Space delimiter also skips TAB/CR/LF.
XWORD:
    mov w7, w20                     // delimiter
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    ldr x2, [x0]
_word_skip:
    ldrb w4, [x2]
    cbz w4, _word_empty
    cmp w7, #32
    b.ne _word_skip_exact
    // space: skip space/tab/cr/lf
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
    // if ended on delimiter (not NUL), consume it
    ldrb w4, [x2]
    cbz w4, _word_store
    add x2, x2, #1
_word_store:
    str x2, [x0]                    // update cursor
    // counted string at word_scratch: max 63 chars
    cmp x5, #63
    b.ls _word_len_ok
    mov x5, #63
_word_len_ok:
    adrp x6, word_scratch@page
    add x6, x6, word_scratch@pageoff
    strb w5, [x6]                   // count byte
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
    mov x20, x6                     // c-addr of counted string
    NEXT
_word_empty:
    str x2, [x0]
    adrp x6, word_scratch@page
    add x6, x6, word_scratch@pageoff
    strb wzr, [x6]
    mov x20, x6
    NEXT

// \ ( -- ) IMMEDIATE  discard rest of parse area (to end of line)
XBACKSLASH:
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    ldr x1, [x0]
_bs_loop:
    ldrb w2, [x1]
    cbz w2, _bs_done
    cmp w2, #10
    b.eq _bs_done
    add x1, x1, #1
    b _bs_loop
_bs_done:
    str x1, [x0]
    NEXT

// ( ( -- ) IMMEDIATE  paren comment; discard until ')'
XPAREN:
    adrp x0, word_cursor@page
    add x0, x0, word_cursor@pageoff
    ldr x1, [x0]
_par_loop:
    ldrb w2, [x1]
    cbz w2, _par_done
    cmp w2, #41                     // ')'
    b.eq _par_found
    add x1, x1, #1
    b _par_loop
_par_found:
    add x1, x1, #1                  // skip ')'
_par_done:
    str x1, [x0]
    NEXT

// ============================================================================
// QUIT - Outer Interpreter
// ============================================================================
.align 4
_do_quit:
    adrp x23, return_stack@page
    add  x23, x23, return_stack@pageoff
    add  x23, x23, #2048
    adrp x0, state_var@page
    add  x0, x0, state_var@pageoff
    str  xzr, [x0]

_quit_loop:
    // Print prompt via raw SVC
    mov x0, #1
    adrp x1, str_prompt@page
    add x1, x1, str_prompt@pageoff
    mov x2, #5
    mov x16, #4
    svc #0x80

    // Read line
    adrp x0, input_buffer@page
    add  x0, x0, input_buffer@pageoff
    mov  x1, #255
    bl   _read_line
    cbz  x0, _quit_exit

    // Reset word cursor
    adrp x0, word_cursor@page
    add  x0, x0, word_cursor@pageoff
    adrp x1, input_buffer@page
    add  x1, x1, input_buffer@pageoff
    str  x1, [x0]

_interpret_loop:
    bl _next_word
    cbz x1, _interpret_done

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
    // Write "? " via SVC
    mov x0, #1
    adrp x1, str_quest@page
    add x1, x1, str_quest@pageoff
    mov x2, #2
    mov x16, #4
    svc #0x80
    // Print word via SVC
    adrp x0, word_scratch@page
    add x0, x0, word_scratch@pageoff
    bl _print_string_svc
    // Print newline
    mov x0, #10
    bl _putchar
    b _interpret_loop

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

// _read_line: x0=buf, x1=maxlen -> x0=buf ptr on success, 0 on EOF
// Must preserve all VM regs (x19-x24). Previous bug: x21 (W) was clobbered.
_read_line:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!
    stp x21, x22, [sp, #-16]!   // x21 is VM W — must save
    mov x19, x0                 // buf
    mov x20, x1                 // maxlen
    mov x21, #0                 // index
_rl_loop:
    cmp x21, x20
    b.ge _rl_done
    bl _getchar
    cmp w0, #-1
    b.le _rl_eof
    cmp w0, #10
    b.eq _rl_nl
    strb w0, [x19, x21]
    add x21, x21, #1
    b _rl_loop
_rl_nl:
    strb wzr, [x19, x21]        // null terminate
    mov x0, x19
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_rl_eof:
    cbz x21, _rl_null
    strb wzr, [x19, x21]
    mov x0, x19
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_rl_null:
    mov x0, #0
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret
_rl_done:
    strb wzr, [x19, x21]
    mov x0, x19
    ldp x21, x22, [sp], #16
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

// _next_word: parse next word -> x0=addr of word_scratch, x1=length (0=done)
_next_word:
    stp x29, x30, [sp, #-16]!
    mov x29, sp
    stp x19, x20, [sp, #-16]!

    adrp x19, word_cursor@page
    add x19, x19, word_cursor@pageoff
    ldr x19, [x19]

_nw_skip:
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

    // Null terminate
    adrp x4, word_cursor@page
    add x4, x4, word_cursor@pageoff
    str x19, [x4]

    mov x0, x2
    ldp x19, x20, [sp], #16
    ldp x29, x30, [sp], #16
    ret

_nw_eof:
    mov x0, #0
    mov x1, #0
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
input_buffer:   .skip 256
file_buffer:    .skip 65536
word_scratch:   .skip 64

state_var:      .quad 0
base_var:       .quad 10
here_ptr:       .quad 0
latest_var:     .quad 0
word_cursor:    .quad 0

str_hello:  .asciz "PickleForth v0.1\n"
str_prompt: .asciz "\nok> "
str_ok:     .asciz " ok\n"
str_bye:    .asciz "Bye!\n"
str_quest:  .asciz "? "
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

    // --- 4. Defining words / parse helpers using the above ---
    .ascii ": CHAR BL WORD COUNT DROP C@ ; "
    .ascii ": [CHAR] CHAR LIT-ADDR , , ; IMMEDIATE "
    .ascii ": VARIABLE CREATE 0 , ; "
    .ascii ": CONSTANT CREATE , DOCON-ADDR LATEST @ >CODE ! ; "
    .ascii ": RECURSE LATEST @ , ; IMMEDIATE "
    // FILL ( c-addr u char -- ); stack top is u, so bump addr via SWAP 1+ SWAP
    .ascii ": FILL >R BEGIN DUP WHILE OVER R@ SWAP C! SWAP 1+ SWAP 1- REPEAT R> DROP 2DROP ; "
    .ascii ": ERASE 0 FILL ; "

    // --- 5. Tools / extensions ---
    .ascii ": WORDS LATEST @ BEGIN DUP WHILE DUP NAME>STRING TYPE SPACE @ REPEAT DROP CR ; "
    .ascii ": DOCOL? >CODE @ ['] WORDS >CODE @ = ; "
    .ascii ": SEE ' DUP DOCOL? IF 58 EMIT SPACE ELSE 67 EMIT 79 EMIT 68 EMIT 69 EMIT SPACE THEN DUP NAME>STRING TYPE SPACE DUP DOCOL? 0= IF DROP 40 EMIT 112 EMIT 114 EMIT 105 EMIT 109 EMIT 105 EMIT 116 EMIT 105 EMIT 118 EMIT 101 EMIT 41 EMIT CR EXIT THEN >BODY BEGIN DUP @ DUP EXIT-ADDR = IF 2DROP 59 EMIT CR EXIT THEN DUP LIT-ADDR = IF DROP 8 + DUP @ . 8 + ELSE DUP NAME>STRING TYPE SPACE DUP BRANCH-ADDR = OVER 0BRANCH-ADDR = OR IF DROP 8 + DUP @ . SPACE 8 + ELSE DROP 8 + THEN THEN AGAIN ; "
    .ascii ": ALIAS CREATE LATEST @ >CODE SWAP >CODE @ SWAP ! ; "
    .ascii "' INCLUDE ALIAS FLOAD "

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
dict_here:  // HERE ( -- addr )
    .quad dict_lbrack
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
dict_find:  // FIND ( c-addr u -- xt -1 | c-addr u 0 )  non-ANS stack; xt = entry
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

// ============================================================================
// User dictionary space (grows upward)
// ============================================================================
.align 8
user_dict_area: .skip 16384
