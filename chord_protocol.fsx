#time "on"
#r "nuget: Akka.FSharp"

open System
open Akka.Actor
open Akka.FSharp
open System.Security.Cryptography
open System.Numerics

let system = ActorSystem.Create("Chord")

// Input from Command Line
let nodesCount = fsi.CommandLineArgs.[1] |> int
let requestCount = fsi.CommandLineArgs.[2] |> int

type InitiatorMessage = 
    | Init of (int*int)
    | Joined
    | Completed of int

type ChordMessage = 
    | CreateRing
    | Join of IActorRef
    | UpdateNodeDetails
    | FindSuccessor of bigint * bigint * int
    | SetSuccessor of bigint * int
    | FindSuccessorPredecessor
    | SendPredecessorToSender
    | SetSuccessorPredecessor of bigint
    | Stabilize
    | Notify of bigint
    | FixFingers
    | Route of string * bigint * int
    | StartRouting of int
    
    
//Functions
let generate_hash id =
    // Generates SHA1 hash for node ID
    let hashString =    System.Text.Encoding.ASCII.GetBytes(id |> string)
                        |> SHA1Managed.Create().ComputeHash
                        |> Array.map (fun (x : byte) -> System.String.Format("{0:x2}", x))
                        |> String.concat System.String.Empty
            
    BigInteger.Parse("0"+hashString, System.Globalization.NumberStyles.HexNumber)

let Chord (mailbox:Actor<_>) = 
    //Variables
    let random = Random()
    let mutable fingers = Array.create 160 -1I
    let mutable predecessor = -1I
    let mutable successorsPredecessor = -1I
    let mutable nodeId = BigInteger.Parse(mailbox.Self.Path.Name)
    let mutable next = 0
    let nodeAddr = "akka://Chord/user/"
    let initiatorRef = select "akka://Chord/user/Initiator" system

    //Functions
    let find_closest_preceding_node id = 
        let mutable i = 159

        //To skip to initialized entries in finger table
        while fingers.[i] = -1I do
            i <- i-1
            
        //To find closest preceding node
        if nodeId < id then
            while (fingers.[i]>=0I && (fingers.[i]<=nodeId || fingers.[i]>=id)) do
                i <- i-1
        else
            while (fingers.[i]>=0I && (fingers.[i]>=id && fingers.[i]<=nodeId)) do
                i <- i-1
        if i < 0 then
            nodeId
        else 
            fingers.[i]
                
    let rec loop () = actor {
        let! message = mailbox.Receive()
        match message with

        | CreateRing                            ->  predecessor <- -1I
                                                    Array.set fingers 0 nodeId
                                                    mailbox.Self <! UpdateNodeDetails
                                                    initiatorRef <! Joined

        | Join(nodeInRing)                      ->  //printfn "Joined"
                                                    //printfn "node in ring %A" nodeInRing
                                                    predecessor <- -1I
                                                    nodeInRing <! FindSuccessor(nodeId, nodeId, 0)

        | UpdateNodeDetails                     ->  system.Scheduler.ScheduleTellRepeatedly(TimeSpan.FromMilliseconds(1000.0), TimeSpan.FromMilliseconds(200.0), mailbox.Self, FixFingers)
                                                    system.Scheduler.ScheduleTellRepeatedly(TimeSpan.FromMilliseconds(1000.0), TimeSpan.FromMilliseconds(200.0), mailbox.Self, FindSuccessorPredecessor)

        | Stabilize                             ->  if (successorsPredecessor <> -1I &&
                                                        ((fingers.[0]<nodeId && (fingers.[0]>successorsPredecessor || successorsPredecessor>nodeId)) || 
                                                        (nodeId<successorsPredecessor && successorsPredecessor<fingers.[0]))) then
                                                        Array.set fingers 0 successorsPredecessor
                                                    
                                                    let successorRef = select (nodeAddr + (fingers.[0]|>string)) system
                                                    successorRef <! Notify(nodeId)

        | Notify(id)                            ->  if (predecessor = -1I || 
                                                        (predecessor<id && id<nodeId) ||
                                                        (id > nodeId && (id>predecessor || id < nodeId))) then
                                                            predecessor <- id


        | FixFingers                            ->  next <- next + 1
                                                    if next <= 159 then
                                                        let nodeRef = select (nodeAddr + (nodeId|>string)) system
                                                        let entry = nodeId + ((2.0** ((next-1)|>float)) |> bigint)
                                                        nodeRef <! FindSuccessor(nodeId, entry%((2.0**160.0)|>bigint), next)
                                                    else
                                                        next <- 0

        | FindSuccessor(source, id, index)      ->  //printfn "In find successor"
                                                    let idRef = select (nodeAddr+(source|>string)) system
                                                    //Corner case: Handling second node join
                                                    if nodeId = fingers.[0] then
                                                        Array.set fingers 0 id
                                                        idRef <! SetSuccessor(nodeId, index)
                                                
                                                    //Handling node join greater than second join
                                                    else
                                                        if (nodeId<id && id<=fingers.[0]  ||    //ID is between node and its sucessor
                                                            (fingers.[0]<nodeId && (id>nodeId || id<=fingers.[0]))) then    //Edge case
                                                            idRef <! SetSuccessor(fingers.[0], index)
                                                        else
                                                            let closestPrecedingId = find_closest_preceding_node(id)
                                                            let closesPrecedingRef = select (nodeAddr + (closestPrecedingId|>string)) system
                                                            closesPrecedingRef <! FindSuccessor(source, id, index)

        | Route(msg, key, hop)                  ->  let hopCount = hop + 1
                                                    if (nodeId<predecessor && (predecessor<key || key<=nodeId)) || (predecessor<key && key<=nodeId) then
                                                        initiatorRef <! Completed(hopCount)
                                                    else 
                                                        //Handling node join greater than second join
                                                        if (nodeId<key && key<=fingers.[0]  ||    //ID is between node and its sucessor
                                                            (fingers.[0]<nodeId && (key>nodeId || key<=fingers.[0]))) then    //Edge case
                                                            let nodeRef = select (nodeAddr+(fingers.[0]|>string)) system 
                                                            nodeRef <! Route(msg, key, hopCount)
                                                        else
                                                            let closestPrecedingId = find_closest_preceding_node(key)
                                                            let closesPrecedingRef = select (nodeAddr + (closestPrecedingId|>string)) system
                                                            closesPrecedingRef <! Route(msg, key, hopCount)

        | FindSuccessorPredecessor              ->  let successorRef = select (nodeAddr + (fingers.[0]|>string)) system
                                                    successorRef <! SendPredecessorToSender

        | SendPredecessorToSender               ->  mailbox.Sender() <! SetSuccessorPredecessor(predecessor)

        | SetSuccessorPredecessor(predecessorId)->  successorsPredecessor <- predecessorId
                                                    let nodeRef = select (nodeAddr + (nodeId|>string)) system
                                                    nodeRef <! Stabilize
                                                    

        | SetSuccessor(successor, index)        ->  //printfn "In set successor"
                                                    Array.set fingers index successor
                                                    
                                                    if index = 0 then
                                                        mailbox.Self <! UpdateNodeDetails
                                                        initiatorRef <! Joined
                                                    //else 
                                                        //let nodeRef = select (nodeAddr + (nodeId|>string)) system
                                                        //nodeRef <! FixFingers(index)
        
        | StartRouting (requestCount)           ->  for i in 1..requestCount do
                                                        let msg = random.Next()
                                                        system.Scheduler.ScheduleTellOnce(TimeSpan.FromSeconds(1.0), mailbox.Self, Route(msg|>string, generate_hash(msg), -1))
                                                        //mailbox.Self <! Route(msg|>string, generate_hash(msg), -1)
                                                                   
        return! loop()
    }
    loop()



let Initiator (mailbox:Actor<_>) = 
    //Variables
    let mutable nodeList = []
    let mutable nodesCount = 0
    let mutable requestCount = 0
    let mutable nodeIndex = 0
    let mutable requestCounter = 0
    let mutable average = 0.0
    let mutable totalRequest = 0
    
    let rec loop () = actor {
        let! message = mailbox.Receive()
        match message with

        | Init (nodes, requests) -> nodesCount <- nodes
                                    requestCount <- requests
                                    totalRequest <- nodesCount * requestCount
                                    nodeList <- [for i in 0..nodesCount-1 do yield (spawn system (generate_hash (i+3) |> string) Chord)]
                                        
                                    //Initializing ring creation with the first node
                                    nodeList.Item(0) <! CreateRing
        
        | Joined                 -> let sender = mailbox.Sender()
                                    printfn "Joined %s" sender.Path.Name
                                    //system.Scheduler.ScheduleTellRepeatedly(TimeSpan.FromMilliseconds(1000.0), TimeSpan.FromMilliseconds(500.0), nodeList.Item(nodeIndex), FixFingers(0))
                                    //system.Scheduler.ScheduleTellRepeatedly(TimeSpan.FromMilliseconds(1000.0), TimeSpan.FromMilliseconds(500.0), nodeList.Item(nodeIndex), FindSuccessorPredecessor)
                                        
                                    nodeIndex <- nodeIndex + 1
                                    //printfn "In main %d" nodeIndex
                                    if nodeIndex >= nodesCount then
                                        //System.Threading.Thread.Sleep(120000);
                                        for i in 0 .. nodesCount - 1 do
                                            nodeList.Item(i) <! StartRouting(requestCount)
                                    else
                                        //printfn "Joining %d" nodeIndex
                                        nodeList.Item(nodeIndex) <! Join(nodeList.Item(nodeIndex-1))

        | Completed(hops)        -> requestCounter <- requestCounter + 1
                                    average <- average + (hops|>double)

                                    printfn "request converged %i in %i hops" requestCounter hops

                                    if requestCounter = totalRequest then
                                        average <- average / (totalRequest|>double)
                                        printfn "Average hops for %i nodes and %i requests per node = %O" nodesCount requestCount average
                                        mailbox.Context.System.Terminate() |> ignore  
        
        return! loop()
    }
    loop()




[<EntryPoint>]
let main argv =

    // Start of the algorithm - spawn Boss, the delgator
    let intiator = spawn system "Initiator" Initiator
    intiator <! Init(nodesCount, requestCount)
    system.WhenTerminated.Wait()

    0 // return an integer exit code