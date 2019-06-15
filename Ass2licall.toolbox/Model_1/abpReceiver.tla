---------------------------- MODULE abpReceiver ----------------------------

EXTENDS Sequences, Naturals, Integers
CONSTANT Messages, QUEUE_LIMIT

(* --fair algorithm receive
variable output = <<>>, outputQueue = <<>>, inputQueue = <<>>, bit = 0

fair+ process sendAck = "sendAck"
begin
send:
    while TRUE do
        \* Need to receive at least one packet of data before
        \* sending acknowledgements.
        if Len(output) >= 1 then
            \* Send acknowledgement.
            await Len(outputQueue) <= QUEUE_LIMIT;  
            outputQueue := Append(outputQueue, << 1 - bit, 1 - bit >>)
        end if;
    end while;
end process;

fair+ process readData = "readData"
begin
read:
    while TRUE do
        \* If received data matches the current bit then
        \* add it to the output, and also flip the bit
        \* in preparation for the next packet.
        await Len(inputQueue) /= 0;
        if Head(inputQueue)[2] = bit then
            bit := 1 - bit;
            output := Append(output, Head(inputQueue)[1]);
        end if;
        
        \* Reading from the input queue, removes an element from it.
        inputQueue := Tail(inputQueue);
    end while
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES output, outputQueue, inputQueue, bit

vars == << output, outputQueue, inputQueue, bit >>

ProcSet == {"sendAck"} \cup {"readData"}

Init == (* Global variables *)
        /\ output = <<>>
        /\ outputQueue = <<>>
        /\ inputQueue = <<>>
        /\ bit = 0

sendAck == /\ IF Len(output) >= 1
                 THEN /\ Len(outputQueue) <= QUEUE_LIMIT
                      /\ outputQueue' = Append(outputQueue, << 1 - bit, 1 - bit >>)
                 ELSE /\ TRUE
                      /\ UNCHANGED outputQueue
           /\ UNCHANGED << output, inputQueue, bit >>

readData == /\ Len(inputQueue) /= 0
            /\ IF Head(inputQueue)[2] = bit
                  THEN /\ bit' = 1 - bit
                       /\ output' = Append(output, Head(inputQueue)[1])
                  ELSE /\ TRUE
                       /\ UNCHANGED << output, bit >>
            /\ inputQueue' = Tail(inputQueue)
            /\ UNCHANGED outputQueue

Next == sendAck \/ readData

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ SF_vars(sendAck)
        /\ SF_vars(readData)

\* END TRANSLATION


=============================================================================
\* Modification History
\* Last modified Sat May 11 23:33:00 NZST 2019 by zva
\* Created Thu May 09 21:58:48 NZST 2019 by zva
