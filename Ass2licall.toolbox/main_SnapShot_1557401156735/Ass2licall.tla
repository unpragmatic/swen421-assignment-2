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

CONSTANTS Messages
VARIABLES senderInQueue,
          senderOutQueue,
          receiverInQueue,
          receiverOutQueue,
          senderInput,
          receiverOutput,
          senderPc,
          receiverPc
             
vars == <<
    senderInQueue,
    senderOutQueue,
    receiverInQueue,
    receiverOutQueue,
    senderInput,
    receiverOutput,
    senderPc,
    receiverPc
>> 
           
                          
----------------------------------

receiver == INSTANCE abpReceiver WITH
            output <- receiverOutput,
            inputQueue <- receiverInQueue,
            outputQueue <- receiverOutQueue,
            pc <- receiverPc

sender == INSTANCE abpSender WITH 
            input <- senderInput,
            inputQueue <- senderInQueue,
            outputQueue <- senderOutQueue,
            pc <- senderPc
\* Used for sending data
senderToReceiverWire == INSTANCE dataWire WITH 
            inputQueue <- senderOutQueue,
            outputQueue <- receiverInQueue
\* used to sending acknowledgements
receiverToSenderWire == INSTANCE dataWire WITH
            inputQueue <- receiverOutQueue,
            outputQueue <- senderInQueue
            
----------------------------------
(* Used for refinement check
OPB == INSTANCE OnePlaceBufferSpec
----------------------------------
 ghost variables must not change the behaviour of the module.  
   They are only used to define the refinement
*)
Init == /\ sender!Init
        /\ receiver!Init
        /\ senderToReceiverWire!Init
        /\ receiverToSenderWire!Init


receiverNext == /\ receiver!Next
                /\ UNCHANGED <<
                              senderInQueue,
                              senderOutQueue,
                              senderInput,
                              senderPc
                          >>

senderNext == /\ sender!Next
              /\ UNCHANGED <<
                              receiverInQueue,
                              receiverOutQueue,
                              receiverOutput,
                              receiverPc
                          >> 
                
                       

dataChannel ==  /\ senderToReceiverWire!Next
                /\ UNCHANGED <<
                              senderInQueue,
                              receiverOutQueue,
                              senderInput,
                              receiverOutput,
                              senderPc,
                              receiverPc
                          >> 

ackChannel ==  /\ receiverToSenderWire!Next
               /\ UNCHANGED <<
                              senderOutQueue,
                              receiverInQueue,
                              senderInput,
                              receiverOutput,
                              senderPc,
                              receiverPc
                          >>  
 
------------------------------------   
      
Next ==  \/ senderNext
         \/ receiverNext
         \/ dataChannel 
         \/ ackChannel
         

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
       
       (* Add invariants + properties + Explain to a non expert what they show. *)   
---------

MessageReceived == <>(receiverOutput = Messages)

-------------          
(*  Your explanation (10%)
  Briefly describe the models you used and  what they verify



Explain what has not been verified.
*)

=============================================================================
\* Modification History
\* Last modified Thu May 09 22:28:55 NZST 2019 by zva
\* Created Thu May 09 20:37:40 NZST 2019 by zva
