------------------------------ MODULE dataWire ------------------------------
EXTENDS Sequences

(* --algorithm transfer
variable inputQueue = <<>>, outputQueue = <<>>
begin
    while TRUE do
        await Len(inputQueue) /= 0;
        either
            outputQueue := Append(outputQueue, Head(inputQueue));
            inputQueue := Tail(inputQueue);
        or
            inputQueue := Tail(inputQueue);
            outputQueue := outputQueue;
        end either
    end while
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES inputQueue, outputQueue

vars == << inputQueue, outputQueue >>

Init == (* Global variables *)
        /\ inputQueue = <<>>
        /\ outputQueue = <<>>

Next == /\ Len(inputQueue) /= 0
        /\ \/ /\ outputQueue' = Append(outputQueue, Head(inputQueue))
              /\ inputQueue' = Tail(inputQueue)
           \/ /\ inputQueue' = Tail(inputQueue)
              /\ outputQueue' = outputQueue

Spec == Init /\ [][Next]_vars

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu May 09 21:39:19 NZST 2019 by zva
\* Created Thu May 09 20:50:46 NZST 2019 by zva
