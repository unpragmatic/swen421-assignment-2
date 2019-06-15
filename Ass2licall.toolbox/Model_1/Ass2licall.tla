----------------------------- MODULE Ass2licall -----------------------------


(*  The Alternating Bit Protocol  https://en.wikipedia.org/wiki/Alternating_bit_protocol
All code should contain brief documentation and be easy to understand.

Rename and finish this module.
       To add other modules >File>Open Module>Add TLA+ Module
Build the dataWire Module containing  a FAULTY Channel with input and output - 
      it can non deterministically send, corrupt or drop a packet. 
This must be  instantiated twice, dataWire for sending data and  ackWire for sending acknowledgements.  


Build two other Modules  abpSender and  abpReceiver.

The abpSender shares  dataSend (a sequence of data items + bits) with the dataWire input and 
       ackSend (a sequence of acknowlagement bits) with the ackWire output

The abpReceiverr shares  dataReceive (a sequence of data items + bits) with the dataWire output and 
       ackReceive (a sequence of acknowledgement bits) with the ackWire input


Build a one place buffer in the module OnePlaceBufferSpec and show that abpMain is a refinement of 
 OnePlaceBufferSpec. 
 
               Complete the 6 parts below  
 
 18%  (1) RENAME and finish this module  (must be TLA+)
          18% = 9% how thoroughly the protocol has been tested + 9% correctness
    (parts 2 to 5 - 18% = 8% simplicity and inteligibility + 10% correctness)
 18%  (2) build abpSender      (must contain PlusCal )
 18%  (3) build abpReceiver    (must contain PlusCal )
 18%  (4) build onePlaceBuffer (may be TLA+ or PluaCal)
 18%  (5) build dataWire       (must contain PlusCal )                          
 10%  (6) in this module explain what model you built and what they verify 
                   and explain what you have not verified  
 100% 
 
 HANDIN the zipped directory built from the TLA+ tool it must 
     contain  all 5 files + the models you used    
     
   
   The TLA+ code in this file is only gor guidence you are free to 
   amend as you want.                
*)
 
EXTENDS Naturals, Integers, TLC, Sequences, Bags, FiniteSets

(*
Messages: 
    A sequence of messages to send.
    
CORRUPT_DATA:
    A model value representing corrupt data.
*)
CONSTANTS Messages, QUEUE_LIMIT, CORRUPT_DATA
VARIABLES senderInQueue,
          senderOutQueue,
          receiverInQueue,
          receiverOutQueue,
          senderInput,
          receiverOutput,
          senderPc, senderBit,
          receiverBit
             
vars == <<
    senderInQueue,
    senderOutQueue,
    receiverInQueue,
    receiverOutQueue,
    senderInput,
    receiverOutput,
    senderPc, senderBit,
    receiverBit
>> 

----------------------------------
\* The message receiver
receiver == INSTANCE abpReceiver WITH
            output <- receiverOutput,
            inputQueue <- receiverInQueue,
            outputQueue <- receiverOutQueue,
            bit <- receiverBit

\* The message sender
sender == INSTANCE abpSender WITH 
            input <- senderInput,
            inputQueue <- senderInQueue,
            outputQueue <- senderOutQueue,
            pc <- senderPc, bit <- senderBit

\* Used for sending data
senderToReceiverWire == INSTANCE dataWire WITH 
            inputQueue <- senderOutQueue,
            outputQueue <- receiverInQueue

\* used to sending acknowledgements
receiverToSenderWire == INSTANCE dataWire WITH
            inputQueue <- receiverOutQueue,
            outputQueue <- senderInQueue
            
----------------------------------
(* Used for refinement check *)
\* Returns all but the last element of a seqence.
AllButFirst(tuple) == SubSeq(tuple, 1, Len(tuple) - 1)

\* Establish equivilents for the OPB. Note we no ghost variables 
\* are used, instead there is a direct mapping from ABP to a
\* OPB, where we consider the latest element of the receiver
\* output as the one place buffer until it becomes acknowledged.
\* Once it has become acknowledged, the buffer is "empty".
\* It is acknowledged if the sender's and receiver's bits match
\* otherwise it has yet to be acknowledged. Similarly, the 
\* input and output need to be adjusted to disclude the unacknowledged
\* packet on the buffer.

\* This is better than using a ghost variable, as there is no chance
\* to alter either spec's behaviour. Instead it relies on both specs
\* having the same fundamental behaviour.

\* If not acknowledged, then the buffer is the last element of the output.
\* otherwise, it is empty.

OPBBuffer == IF senderBit /= receiverBit
             THEN IF Len(receiverOutput) /= 0 THEN << receiverOutput[Len(receiverOutput)] >> ELSE << >>
             ELSE << >>

\* If not acknowledged, then the input needs to disclude the packet on
\* the buffer. Otherwise, it is just the normal input.
OPBInput ==  IF senderBit /= receiverBit
             THEN IF Len(senderInput) /= 0 THEN Tail(senderInput) ELSE << >>
             ELSE senderInput

\* If not acknowledged, then the output needs to disclude the packet on
\* the buffer. Otherwise, it is just the normal output. 
OPBOutput == IF senderBit /= receiverBit
             THEN IF Len(receiverOutput) /= 0 THEN AllButFirst(receiverOutput) ELSE << >>
             ELSE receiverOutput


OPB == INSTANCE onePlaceBuffer WITH input <- OPBInput, output <- OPBOutput, buffer <- OPBBuffer

----------------------------------
(* Just all the variables that are unchanged for each
   module instance. Written here just to avoid repetition. 
*)

receiverUnchanged ==    UNCHANGED <<
                              senderInQueue,
                              senderOutQueue,
                              senderInput,
                              senderPc, senderBit
                          >>
                          
senderUnchanged ==      UNCHANGED <<
                              receiverInQueue,
                              receiverOutQueue,
                              receiverOutput,
                              receiverBit
                          >> 

dataChannelUnchanged == UNCHANGED <<
                              senderInQueue,
                              receiverOutQueue,
                              senderInput,
                              receiverOutput,
                              senderPc, senderBit,
                              receiverBit
                          >>

ackChannelUnchanged ==  UNCHANGED <<
                              senderOutQueue,
                              receiverInQueue,
                              senderInput,
                              receiverOutput,
                              senderPc, senderBit,
                              receiverBit
                          >> 

(* Actions *)
\* Receiver
receiverSend == /\ receiver!sendAck /\ receiverUnchanged                          
receiverRead == /\ receiver!readData /\ receiverUnchanged
receiverNext == receiverSend \/ receiverRead


\* Sender
senderSend == /\ sender!sendData /\ senderUnchanged
senderRead == /\ sender!readAck /\ senderUnchanged
senderNext == senderSend \/ senderRead


\* Data channel
dataChannelSend ==  /\ senderToReceiverWire!send /\ dataChannelUnchanged
dataChannelDrop ==  /\ senderToReceiverWire!drop /\ dataChannelUnchanged 
dataChannelCorrupt == /\ senderToReceiverWire!corrupt /\ dataChannelUnchanged 

dataChannelNext == dataChannelSend \/ dataChannelDrop \/ dataChannelCorrupt


\* Acknowledgement channel
ackChannelSend == /\ receiverToSenderWire!send /\ ackChannelUnchanged
ackChannelDrop == /\ receiverToSenderWire!drop /\ ackChannelUnchanged
ackChannelCorrupt == /\ receiverToSenderWire!corrupt /\ ackChannelUnchanged

ackChannelNext ==  ackChannelSend \/ ackChannelDrop \/ ackChannelCorrupt  
 
------------------------------------   

Init == /\ sender!Init
        /\ receiver!Init
        /\ senderToReceiverWire!Init
        /\ receiverToSenderWire!Init      


Next ==  \/ senderNext
         \/ receiverNext
         \/ dataChannelNext 
         \/ ackChannelNext
         

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(senderSend) 
        /\ WF_vars(senderRead)
        /\ WF_vars(receiverSend)
        /\ WF_vars(receiverRead)
        /\ SF_vars(dataChannelSend)
        /\ SF_vars(ackChannelSend)

       
(* Add invariants + properties + Explain to a non expert what they show. *)   
---------
Range(T) == { T[x] : x \in DOMAIN T }

ValidData == Range(Messages)
ValidBits == {0, 1}
ValidDataPackets == (ValidData \X ValidBits) \union {<<CORRUPT_DATA, CORRUPT_DATA>>}
ValidAckPackets == { <<b, b>> : b \in ValidBits } \union { <<CORRUPT_DATA, CORRUPT_DATA>> }

\* Just basic type invariant.
\*
\* Ensures that the queues are sequences of packets
\* (in the correct format and type).
\*
\* Ensures that the input and output only consist of valid data.
\*
\* Ensures that bits are either 0 or 1.
TypeOK == /\ senderInQueue \in [1..Len(senderInQueue) -> ValidAckPackets]
          /\ senderOutQueue \in [1..Len(senderOutQueue) -> ValidDataPackets]
          /\ receiverInQueue \in [1..Len(receiverInQueue) -> ValidDataPackets]
          /\ receiverOutQueue \in [1..Len(receiverOutQueue) -> ValidAckPackets]
          /\ senderInput \in [1..Len(senderInput) -> ValidData]
          /\ receiverOutput \in [1..Len(receiverOutput) -> ValidData]
          /\ senderBit \in ValidBits
          /\ receiverBit \in ValidBits

\* Ensures that send input and receive output only take on
\* values that have the packets in the right order. That is
\* as if they were sent consecutively.
\* e.g.
\* senderInput = ["Hello", "world"] or ["world"] or []
\* receiverOutput = [] or ["Hello"] or ["Hello", "world"]
ValidSendInput == { SubSeq(Messages, i, Len(Messages)) : i \in 1..Len(Messages)+1  }
ValidReceiverOutput == { SubSeq(Messages, 1, i) : i \in 0..Len(Messages) }

SequenceOK == /\ senderInput \in ValidSendInput
              /\ receiverOutput \in ValidReceiverOutput 

\* Ensures that values are sent sequentially. Note that
\* "SequenceOK" only checks that the value of input and output
\* are valid, not the sequence they occur in.
MessageReceivedSequence == \A i \in 0..Len(Messages)-1 : (receiverOutput = SubSeq(Messages, 1, i) ~> (receiverOutput = SubSeq(Messages, 1, i+1)))
MessageSentSequence == \A i \in 1..Len(Messages) : (senderInput = SubSeq(Messages, i, Len(Messages))) ~> (senderInput = SubSeq(Messages, i+1, Len(Messages)))

\* Ensures that ackowledgement bits get acknowledged.
\* Note that the reverse does not hold. 
BitAcknowledged == \A b \in ValidBits : (receiverBit = b) ~> (senderBit = b)

\* A property that says that eventually, the receiver's output
\* will (always) be the input Messages. Aka, the receiver will
\* eventually receive all the data.
MessageReceived == <>[](receiverOutput = Messages)

\* The sender will eventually know all the data has been 
\* successfully been sent.
MessageSent == <>[](senderInput = << >>)

\* The bits will eventually match and be the same forever.
\* Not a particularly useful property.
BitMatch == <>[](senderBit = receiverBit)

\* Just some bad properties used for debugging
BadSequence == (receiverOutput = <<"Hello", "world">>) ~> (receiverOutput = <<"aaa">>)
BadSome == <>(receiverOutput = <<"Heasdlo", "world">>)
-------------          
(*  Your explanation (10%)

RUNNING:

See the included screenshot for model setup. Not sure if it gets saved 
along with the model.

You can set QUEUE_LIMIT as high as you want, but a QUEUE_LIMIT of 4 takes
5 minutes to run and the time required increases exponentially as the
QUEUE_LIMIT increases.

EXPLANATION:

This specification of the alternating bit protocol involves four key 
agents: the sender, receiver, senderToReceiverWire, and receiverToSenderWire.

These are relatively self explanatory. The sender sends the data packets and
listens for acknowledgements (acks), in contrast the receiver sends ack packets
and listens for data. This sending and listening happens over the corresponding
wires.

Notably, these wires are not perfect. They can drop or even corrupt packets
that are sent through them. This deterimental characteristic exists to verify
that, even with a poor connection between sender and receiver, using the 
alternating bit protocol (ABP) enables lossless transfer of data. This property
is encoded by "MessageReceived". 

However, there are some key assumptions that are made to make this verification
possible. Most importantly: a data packet repeatedly sent along the wire will
eventually be transfer successfully. This assumption is perhaps unrealistic
since a real wire that is lossy might be disconnected, and thus it is impossible
for a successful transfer to happen. 

Furthermore, it is also assumed that corrupted packets are discernable from
uncorrupted packets. This is also perhaps unrealistic, since in reality this
is not possible without some mechanism to detect data corruption (such as
checksums and hashes), and even then it is possible to construct corrupted
packets that bypass detection.

Another key assumption, is that none of the models stagger indefinitely. In a
spec where that is possible, the sender could simply never send a packet and
thus the message will never be received.

However, for the purposes of this specification these assumptions are fair.
Since many real world scenarios have these transfer characteristics. Most
notably: the internet.

Without these assumptions, the "MessageReceived" property under ABP is not
verifiable. The first assumption is written in "Spec" as 
"SF_vars(dataChannelSend)" and "SF_vars(ackChannelSend)". The second is
accomplished by using a model value for "CORRUPT_DATA" in order to discern
corrupted data from uncorrupted data. The last assumption is also written
in "Spec" as the various weak fairness statements (WF_vars(...)).

*)

=============================================================================
\* Modification History
\* Last modified Sun May 12 00:14:38 NZST 2019 by zva
\* Created Thu May 09 20:37:40 NZST 2019 by zva
