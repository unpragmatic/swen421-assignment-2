------------------------------ MODULE dataWire ------------------------------
EXTENDS Sequences, Integers

CONSTANTS CORRUPT_DATA, QUEUE_LIMIT
(* --fair algorithm transfer
variable inputQueue = <<>>, outputQueue = <<>>

fair+ process send = "send"
begin
send:
    \* Send the data packet across.
    while TRUE do
        await Len(inputQueue) /= 0;
        await Len(outputQueue) <= QUEUE_LIMIT;
        outputQueue := Append(outputQueue, Head(inputQueue));
        inputQueue := Tail(inputQueue);
    end while;      
end process;

fair+ process drop = "drop"
begin
drop:
    \* Drop the packet.
    while TRUE do
        await Len(inputQueue) /= 0;
        inputQueue := Tail(inputQueue);
    end while;      
end process;

fair+ process corrupt = "corrupt"
begin
corrupt:
    \* Send across a corrupted data packet.
    while TRUE do
        await Len(inputQueue) /= 0;
        await Len(outputQueue) <= QUEUE_LIMIT;
        \* Assumes that all data packets are 2-tuples.
        outputQueue := Append(outputQueue, << CORRUPT_DATA, CORRUPT_DATA >>);
        inputQueue := Tail(inputQueue);
    end while;
end process;
end algorithm; *)

\* BEGIN TRANSLATION
\* Label send of process send at line 12 col 5 changed to send_
\* Label drop of process drop at line 24 col 5 changed to drop_
\* Label corrupt of process corrupt at line 34 col 5 changed to corrupt_
VARIABLES inputQueue, outputQueue

vars == << inputQueue, outputQueue >>

ProcSet == {"send"} \cup {"drop"} \cup {"corrupt"}

Init == (* Global variables *)
        /\ inputQueue = <<>>
        /\ outputQueue = <<>>

send == /\ Len(inputQueue) /= 0
        /\ Len(outputQueue) <= QUEUE_LIMIT
        /\ outputQueue' = Append(outputQueue, Head(inputQueue))
        /\ inputQueue' = Tail(inputQueue)

drop == /\ Len(inputQueue) /= 0
        /\ inputQueue' = Tail(inputQueue)
        /\ UNCHANGED outputQueue

corrupt == /\ Len(inputQueue) /= 0
           /\ Len(outputQueue) <= QUEUE_LIMIT
           /\ outputQueue' = Append(outputQueue, << CORRUPT_DATA, CORRUPT_DATA >>)
           /\ inputQueue' = Tail(inputQueue)

Next == send \/ drop \/ corrupt

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ SF_vars(send)
        /\ SF_vars(drop)
        /\ SF_vars(corrupt)

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat May 11 23:32:39 NZST 2019 by zva
\* Last modified Fri May 10 20:23:45 NZST 2019 by zva
\* Last modified Fri May 10 17:46:42 AEST 2019 by zva
\* Created Thu May 09 20:50:46 NZST 2019 by zva
