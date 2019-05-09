---------------------------- MODULE abpReceiver ----------------------------

EXTENDS Sequences, Naturals, Integers
CONSTANT Messages
(* --algorithm receive
variable output = <<>>, outputQueue = <<>>, inputQueue = <<>>
begin
    while Len(output) /= Len(Messages) do
        await Len(inputQueue) /= 0;
        output := Append(output, Head(inputQueue));
        inputQueue := Tail(inputQueue);
    end while
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES output, outputQueue, inputQueue, pc

vars == << output, outputQueue, inputQueue, pc >>

Init == (* Global variables *)
        /\ output = <<>>
        /\ outputQueue = <<>>
        /\ inputQueue = <<>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(output) /= Len(Messages)
               THEN /\ Len(inputQueue) /= 0
                    /\ output' = Append(output, Head(inputQueue))
                    /\ inputQueue' = Tail(inputQueue)
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << output, inputQueue >>
         /\ UNCHANGED outputQueue

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Thu May 09 22:15:36 NZST 2019 by zva
\* Created Thu May 09 21:58:48 NZST 2019 by zva
