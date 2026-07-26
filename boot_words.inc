// ============================================================================
// Boot word catalog (CODE primitives)
// ============================================================================
// One line per word:
//   BOOT_WORD "NAME", "( stack ) description", imm, CodeLabel
//
// imm: 0 = normal, 1 = IMMEDIATE
// CodeLabel: assembly entry point (XDUP, XDROP, DOEXIT, ...)
// Help strings start empty; fill in a later comment pass.
// ============================================================================

// Dense table row: name*, help*, imm, code*.
// Strings live in __TEXT,__cstring so the table stays contiguous (4 quads/row).
.macro BOOT_WORD name, help, imm, code
    .quad .Lbw_n\@, .Lbw_h\@, \imm, \code
    .section __TEXT,__cstring,cstring_literals
.Lbw_n\@:
    .asciz "\name"
.Lbw_h\@:
    .asciz "\help"
    .previous
.endm

.align 8
boot_word_table:
    BOOT_WORD "EXIT", "", 0, DOEXIT
    BOOT_WORD ";", "", 1, XSEMI
    BOOT_WORD "LIT", "", 0, XLit
    BOOT_WORD "DUP", "", 0, XDUP
    BOOT_WORD "DROP", "", 0, XDROP
    BOOT_WORD "SWAP", "", 0, XSWAP
    BOOT_WORD "OVER", "", 0, XOVER
    BOOT_WORD "ROT", "", 0, XROT
    BOOT_WORD "NIP", "", 0, XNIP
    BOOT_WORD "TUCK", "", 0, XTUCK
    BOOT_WORD "PICK", "", 0, XPICK
    BOOT_WORD ">R", "", 0, XTOR
    BOOT_WORD "R>", "", 0, XRTO
    BOOT_WORD "R@", "", 0, XRFETCH
    BOOT_WORD "+", "", 0, XPLUS
    BOOT_WORD "-", "", 0, XMINUS
    BOOT_WORD "*", "", 0, XSTAR
    BOOT_WORD "/", "", 0, XSLASH
    BOOT_WORD "MOD", "", 0, XMOD
    BOOT_WORD "/MOD", "", 0, XSLMOD
    BOOT_WORD "=", "", 0, XEQUAL
    BOOT_WORD "<", "", 0, XLESS
    BOOT_WORD ">", "", 0, XGREATER
    BOOT_WORD "U<", "", 0, XULESS
    BOOT_WORD "AND", "", 0, XAND
    BOOT_WORD "OR", "", 0, XORR
    BOOT_WORD "XOR", "", 0, XXOR
    BOOT_WORD "INVERT", "", 0, XINVERT
    BOOT_WORD "0=", "", 0, XZEQUAL
    BOOT_WORD "0<", "", 0, XZLESS
    BOOT_WORD "TRUE", "", 0, XTRUE
    BOOT_WORD "FALSE", "", 0, XFALSE
    BOOT_WORD "1+", "", 0, XONEPLUS
    BOOT_WORD "1-", "", 0, XONEMINUS
    BOOT_WORD "CELL", "", 0, XCELL
    BOOT_WORD "CELLS", "", 0, XCELLS
    BOOT_WORD "@", "", 0, XFETCH
    BOOT_WORD "!", "", 0, XSTORE
    BOOT_WORD "C@", "", 0, XCFETCH
    BOOT_WORD "C!", "", 0, XCSTORE
    BOOT_WORD "+!", "", 0, XPLUSSTORE
    BOOT_WORD "EMIT", "", 0, XEMIT
    BOOT_WORD "KEY", "", 0, XKEY
    BOOT_WORD "CR", "", 0, XCR
    BOOT_WORD ".", "", 0, XDOT
    BOOT_WORD "U.", "", 0, XUDOT
    BOOT_WORD ".S", "", 0, XDOTS
    BOOT_WORD "TYPE", "", 0, XTYPE
    BOOT_WORD "STATE", "", 0, XSTATE
    BOOT_WORD "BASE", "", 0, XBASE
    BOOT_WORD "]", "", 0, XRBRA
    BOOT_WORD "[", "", 1, XLBRA
    BOOT_WORD "DP", "", 0, XDP
    BOOT_WORD "HERE", "", 0, XHERE
    BOOT_WORD "ALLOT", "", 0, XALLOT
    BOOT_WORD ",", "", 0, XCOMMA
    BOOT_WORD "FIND", "", 0, XFIND
    BOOT_WORD "'", "", 0, XTICK
    BOOT_WORD "EXECUTE", "", 0, XEXECUTE
    BOOT_WORD "LITERAL", "", 1, XLITERAL
    BOOT_WORD "IMMEDIATE", "", 0, XIMMEDIATE
    BOOT_WORD ":", "", 0, XCOLON
    BOOT_WORD "CREATE", "", 0, XCREATE
    BOOT_WORD "0BRANCH", "", 0, X0Branch
    BOOT_WORD "BRANCH", "", 0, XBranch
    BOOT_WORD "BYE", "", 0, XBYE
    BOOT_WORD "INCLUDE", "", 0, XINCLUDE
    BOOT_WORD "LATEST", "", 0, XLATEST
    BOOT_WORD "?DUP", "", 0, XQDUP
    BOOT_WORD "[']", "", 1, XBRACKET_TICK
    BOOT_WORD "LIT-ADDR", "", 0, XLIT_ADDR
    BOOT_WORD "0BRANCH-ADDR", "", 0, X0BRANCH_ADDR
    BOOT_WORD "BRANCH-ADDR", "", 0, XBRANCH_ADDR
    BOOT_WORD "EXIT-ADDR", "", 0, XEXIT_ADDR
    BOOT_WORD "NEGATE", "", 0, XNEGATE
    BOOT_WORD "ABS", "", 0, XABS
    BOOT_WORD "MIN", "", 0, XMIN
    BOOT_WORD "MAX", "", 0, XMAX
    BOOT_WORD "LSHIFT", "", 0, XLSHIFT
    BOOT_WORD "RSHIFT", "", 0, XRSHIFT
    BOOT_WORD "<>", "", 0, XNEQUAL
    BOOT_WORD "PARSE", "", 0, XPARSE
    BOOT_WORD "WORD", "", 0, XWORD
    BOOT_WORD "\\", "", 1, XBACKSLASH
    BOOT_WORD "(", "", 1, XPAREN
    BOOT_WORD "DOCON-ADDR", "", 0, XDOCON_ADDR
    BOOT_WORD "SOURCE", "", 0, XSOURCE
    BOOT_WORD ">IN", "", 0, XTOIN
    BOOT_WORD "(S\")", "", 0, XSLIT
    BOOT_WORD "S\"", "", 1, XSQUOTE
    BOOT_WORD ".\"", "", 1, XDOTQ
    BOOT_WORD "(DO)", "", 0, XDO_RT
    BOOT_WORD "(?DO)", "", 0, XQDO_RT
    BOOT_WORD "(LOOP)", "", 0, XLOOP_RT
    BOOT_WORD "(+LOOP)", "", 0, XPLUSLOOP_RT
    BOOT_WORD "I", "", 0, XI
    BOOT_WORD "J", "", 0, XJ
    BOOT_WORD "UNLOOP", "", 0, XUNLOOP
    BOOT_WORD "LEAVE", "", 0, XLEAVE
    BOOT_WORD "(DOES>)", "", 0, XDOES_RT
    BOOT_WORD "PAD", "", 0, XPAD
    BOOT_WORD "DOES>", "", 1, XDOES
    BOOT_WORD "EVALUATE", "", 0, XEVALUATE
    BOOT_WORD "CATCH", "", 0, XCATCH
    BOOT_WORD "THROW", "", 0, XTHROW
    BOOT_WORD "(CATCH-OK)", "", 0, XCATCH_OK
    BOOT_WORD "CONTAINS", "", 0, XCONTAINS
    BOOT_WORD "MS@", "", 0, XMSFETCH
    BOOT_WORD "UNUSED", "", 0, XUNUSED
    BOOT_WORD "REDEF-WARNING", "", 0, XREDEF_WARNING
    BOOT_WORD "USER-DICT", "", 0, XUSER_DICT
    BOOT_WORD "SP0", "", 0, XSP0
    BOOT_WORD "SP@", "", 0, XSPFETCH
    BOOT_WORD "SP!", "", 0, XSPSTORE
    BOOT_WORD "SPACES", "", 0, XSPACES
    BOOT_WORD "C,", "", 0, XCCOMMA
    BOOT_WORD "S>D", "", 0, XSTOD
    BOOT_WORD "2*", "", 0, XTWOSTAR
    BOOT_WORD "2/", "", 0, XTWOSLASH
    BOOT_WORD "2@", "", 0, XTWOFETCH
    BOOT_WORD "2!", "", 0, XTWOSTORE
    BOOT_WORD "UM*", "", 0, XUMSTAR
    BOOT_WORD "M*", "", 0, XMSTAR
    BOOT_WORD "UM/MOD", "", 0, XUMMOD
    BOOT_WORD "SM/REM", "", 0, XSMREM
    BOOT_WORD "FM/MOD", "", 0, XFMMOD
    BOOT_WORD "QUIT", "", 0, XQUIT
    BOOT_WORD "SOURCE-ID", "", 0, XSOURCE_ID
    BOOT_WORD "REFILL", "", 0, XREFILL
    BOOT_WORD "ACCEPT", "", 0, XACCEPT
    BOOT_WORD ">NUMBER", "", 0, XTONUMBER
    BOOT_WORD "ENVIRONMENT?", "", 0, XENVIRONMENT_Q
    BOOT_WORD "FILE-ECHO", "", 0, XFILE_ECHO
    BOOT_WORD "PARSE-NAME", "", 0, XPARSE_NAME
    BOOT_WORD "2>R", "", 0, X2TOR
    BOOT_WORD "2R>", "", 0, X2RTO
    BOOT_WORD "2R@", "", 0, X2RFETCH
    BOOT_WORD "ROLL", "", 0, XROLL
    BOOT_WORD ":NONAME", "", 0, XNONAME
    BOOT_WORD "(C\")", "", 0, XCSTR
    BOOT_WORD "C\"", "", 1, XCQUOTE
    BOOT_WORD "S\\\"", "", 1, XSESCAPE
    BOOT_WORD "SAVE-INPUT", "", 0, XSAVE_INPUT
    BOOT_WORD "RESTORE-INPUT", "", 0, XRESTORE_INPUT
    .quad 0, 0, 0, 0

.equ BOOT_WORD_COUNT, 144

// Empty help used by : / CREATE / :NONAME
.align 8
boot_h_empty:
    .asciz ""

// C strings for _boot_cache_cfa
.align 8
boot_cmp_lit: .asciz "LIT"
boot_cmp_exit: .asciz "EXIT"
boot_cmp_slit: .asciz "(S\")"
boot_cmp_cstr: .asciz "(C\")"
boot_cmp_type: .asciz "TYPE"
boot_cmp_branch: .asciz "BRANCH"
boot_cmp_0branch: .asciz "0BRANCH"
boot_cmp_does_rt: .asciz "(DOES>)"
boot_cmp_catch_ok: .asciz "(CATCH-OK)"

