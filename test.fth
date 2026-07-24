\ Words

HEX FF DUP . DECIMAL .  CR  \ FF 255
7 CONSTANT SEVEN  SEVEN .  CR \ 7
VARIABLE V  99 V !  V @ . CR \ 99
: FACT DUP 1 > IF DUP 1- RECURSE * THEN ;
5 FACT .                  CR \ 120
1 ( skip ) 2 + .          CR \ 3
CREATE PAD 8 ALLOT  PAD 5 65 FILL  PAD 5 TYPE CR \ AAAAA

: T 5 0 DO I . LOOP CR ;
T
\ 0 1 2 3 4

: T 10 0 DO I . 2 +LOOP CR ;
T
\ 0 2 4 6 8

: T 3 0 DO 2 0 DO J . I . SPACE LOOP CR LOOP ;
T
\ nested I/J