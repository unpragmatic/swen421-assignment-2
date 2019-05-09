----------------------------- MODULE abpSender -----------------------------
EXTENDS Sequences, Naturals, Integers
CONSTANT Messages
(* --algorithm send
variable input = Messages, outputQueue = <<>>, inputQueue = <<>>
begin
    while Len(input) /= 0 do
        await Len(outputQueue) < 5;
        outputQueue := Append(outputQueue, Head(input));
        input := Tail(input)
    end while
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES input, outputQueue, inputQueue, pc

vars == << input, outputQueue, inputQueue, pc >>

Init == (* Global variables *)
        /\ input = Messages
        /\ outputQueue = <<>>
        /\ inputQueue = <<>>
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF Len(input) /= 0
               THEN /\ Len(outputQueue) < 5
                    /\ outputQueue' = Append(outputQueue, Head(input))
                    /\ input' = Tail(input)
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << input, outputQueue >>
         /\ UNCHANGED inputQueue

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu May 09 22:17:35 NZST 2019 by zva
\* Created Thu May 09 21:13:00 NZST 2019 by zva
