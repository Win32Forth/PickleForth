PickleForth is a relatively simple Terminal Console based Forth system for the MacOS M1 - M5 series processors. It is written in Assembly language, and was initially written using OpenCode platform and the (free) Big Pickle AI model for coding. Initial development progressed quickly, but I later learned that Big Pickle is not the best model for assembly language coding and debugging. I switched over to Grok (not-free) for debugging and to extend PickleForth to be a more complete Forth system. PickleForth is an indirect threaded Forth, and keeps several Forth variables in registers, so it should be lightning fast (see below). For the moment, it consists of one primary source file, forth.s, assisted by two .inc files that hold MACROS for header construction. The headers for Assembly words are constructd by the assembler, and the highlevel colon definitions in PickleForth are defind as .ascii strings and compile at system startup time. 

I have not yet decided whether portions of PickleForth will make their way into TZForth. One of my regrets in developing TZForth is that so much of it is written in Swift, and not Forth itself. Consequently, when I started PickleForth, I instructed the AI to start building all new additions as High Level Forth words, unless assembly was needed for performance reasons. There are about 107 CODE words in PickleForth, and about 109 COLON definitions.

I don't know if anyone will find PicklForth interesting, but, as with all of my Forth Systems, PickleForth is public domain. If you  do choose to study PickleForth, please remember that it is still repidly evolving, while I extend it to be closer to a full(er) implementation of ANS Forth.

Yesterday I tested PickleForth with an empty DO LOOP against the same code in TZForth on the same computer. I found that PickleForth is 143 times faster than TZForth for this simple operation. That translates to 7 million loops per second for TZForth, and one (1) billion loops per second for PickleForth.
Today, we added stack pictures and brief help text to all of the dictionary words when you use SEE 'word' or HELP 'word'. We also re-organized the header structure;
// Dictionary header format (built at runtime; grows up with HERE):
//   HFA:  counted HELP (stack pic + text), pad 8 (empty = count 0)
//   NFA:  counted NAME (uppercase), pad 8
//   LFA:  LINK  = previous CFA (or 0)     @ CFA-16  >LINK
//   FFA:  FLAGS @ CFA-8: low32 NFA_OFF, bits32-62 HFA_OFF, bit63 IMM
//   CFA:  CODE (** xt **)                 >CODE (= xt)
//   BODY: @ CFA+8                         >BODY


