--------------------------- MODULE onePlaceBuffer ---------------------------
EXTENDS Sequences

CONSTANT Messages
VARIABLES input, buffer, output

vars == <<
    input,
    buffer,
    output
>>

Init == /\ input  = Messages
        /\ buffer = <<>>
        /\ output = <<>>

\* Send only if buffer is empty and there are unsent packets.
Send == /\ buffer = <<>> /\ Len(input) /= 0
        /\ input' = Tail(input)
        /\ buffer' = << Head(input) >>
        /\ UNCHANGED << output >>

\* Read only if the buffer is not empty
Read == /\ buffer /= <<>>
        /\ output' = Append(output, buffer[1])
        /\ buffer' = <<>>
        /\ UNCHANGED << input >>

Next == \/ Send
        \/ Read
        
Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Sun May 12 00:14:14 NZST 2019 by zva
\* Created Thu May 09 23:26:39 NZST 2019 by zva
