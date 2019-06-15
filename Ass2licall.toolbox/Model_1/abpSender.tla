----------------------------- MODULE abpSender -----------------------------
EXTENDS Sequences, Naturals, Integers, TLC
CONSTANT Messages, QUEUE_LIMIT

(* --fair algorithm send
variable input = Messages, outputQueue = <<>>, inputQueue = <<>>, bit = 0

fair+ process sendData = "sendData"
begin
send:
    \* While there is still unsent data.
    while Len(input) /= 0 do
        await Len(outputQueue) <= QUEUE_LIMIT;
        \* Send the data.
        outputQueue := Append(outputQueue, << Head(input), bit >>);
    end while;
end process;

fair+ process readAck = "readAck"
begin
read:
    \* While there is still unsent data.
    while Len(input) /= 0 do
        await Len(inputQueue) /= 0;
        \* If an acknowledgement is found for the sent data
        \* then mark it as sent (by removing it from send queue)
        \* and flip the bit for the next piece of data.
        if Head(inputQueue)[2] = bit then
            bit := 1 - bit;
            input := Tail(input);
        end if;
        
        \* Reading from the input queue, removes an element from it.
        inputQueue := Tail(inputQueue);
    end while
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES input, outputQueue, inputQueue, bit, pc

vars == << input, outputQueue, inputQueue, bit, pc >>

ProcSet == {"sendData"} \cup {"readAck"}

Init == (* Global variables *)
        /\ input = Messages
        /\ outputQueue = <<>>
        /\ inputQueue = <<>>
        /\ bit = 0
        /\ pc = [self \in ProcSet |-> CASE self = "sendData" -> "send"
                                        [] self = "readAck" -> "read"]

send == /\ pc["sendData"] = "send"
        /\ IF Len(input) /= 0
              THEN /\ Len(outputQueue) <= QUEUE_LIMIT
                   /\ outputQueue' = Append(outputQueue, << Head(input), bit >>)
                   /\ pc' = [pc EXCEPT !["sendData"] = "send"]
              ELSE /\ pc' = [pc EXCEPT !["sendData"] = "Done"]
                   /\ UNCHANGED outputQueue
        /\ UNCHANGED << input, inputQueue, bit >>

sendData == send

read == /\ pc["readAck"] = "read"
        /\ IF Len(input) /= 0
              THEN /\ Len(inputQueue) /= 0
                   /\ IF Head(inputQueue)[2] = bit
                         THEN /\ bit' = 1 - bit
                              /\ input' = Tail(input)
                         ELSE /\ TRUE
                              /\ UNCHANGED << input, bit >>
                   /\ inputQueue' = Tail(inputQueue)
                   /\ pc' = [pc EXCEPT !["readAck"] = "read"]
              ELSE /\ pc' = [pc EXCEPT !["readAck"] = "Done"]
                   /\ UNCHANGED << input, inputQueue, bit >>
        /\ UNCHANGED outputQueue

readAck == read

Next == sendData \/ readAck
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ SF_vars(sendData)
        /\ SF_vars(readAck)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Sat May 11 23:32:52 NZST 2019 by zva
\* Created Thu May 09 21:13:00 NZST 2019 by zva
