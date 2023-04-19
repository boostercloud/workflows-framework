\pagebreak
# The nature of integrations: Orchestration, Fault Tolerance, Concurrency, and Communication

## The problem

Integrating systems poses a series of challenges that are unique to running a process outside the memory space of a machine:

1. **Orchestration**: The actions to be performed on the other systems need to be orchestrated, this is, setting up an order or a workflow for them to execute. Some examples would be:
    1. Actions that need to be executed in series, each one after the previous has been successfully executed and accepted.
        1. There’s also the possibility that one of these steps is composed with a battery of actions that can, and often should, (for efficiency reasons) be performed in parallel. Which would imply following the patterns for point `b`.
    2. Actions that can, and often should, (for efficiency reasons) be performed in parallel.
        1. There’s also that some of the actions might be composed of a series of actions, that have to be executed following the patterns for point `a`.
    3. In both of the previous cases, there might be a need to “undo” the actions that have been already executed successfully when one of them is rejected or fails.
        1. This poses the additional challenge that the undo actions might fail or be rejected.
    4. Both scenarios `a.i` and `b.i` might nest upon each other, it’s unlikely that it would happen at many levels, but enough to become difficult do reason about without a helpful abstraction. Then take into account `c` and `c.i` and you can begin to see why orchestration is not a trivial issue.
2. **Fault tolerance**: Integrations actions can fail or produce unexpected results for reasons that do not depend on the [safety of the code](#code-safety) performing them:
    1. External services that fail to respond:
        1. After a defect in its algorithms causes it to fail (e.g. Dividing by zero).
        2. Due to network problems.
        3. After receiving an excessive load.
        4. Because another external service they themselves depend on failed to respond.
    2. Half completed previous attempts that left the system in an incoherent state.
3. **Concurrency:** Integrations cause systems to interact with each other in a continuous stream of activity. Some of these actions will have constraints that are hard to guarantee if there are other processes trying to perform the same action over the same resource.
e.g. Two actions might involve requesting the available stock for a product, which happens to be six units, both of them are trying to reserve four units, and since they are unaware of the other, they deem the stock sufficient to make the reservation, only to find later that one of the reservations cannot be fulfilled. Some cases:
    1. Concurrent access, different processes.
    e.g. Another user might be trying, at the same time, to reserve the same meeting room for a period of the day that overlaps with our reservation. In certain scenarios, we can’t completely prevent issues from coming from this vector.
    2. Concurrent access, same process. It is possible that we might process the same workflow twice at the same time. There are plenty of reasons for this, some examples would be:
        - A misconfiguration in a message queue that allows two different consumers to receive the same message.
        - A mistake from a sender that puts two copies of the same message in a queue.
        - A synchronous operation that had no mechanism to prevent double requests.
        - A polling mechanism that is deployed in a zero-downtime manner, having both the exiting and entering processor poll the same task at the same time.
4. **Communication**: There is a need to send a message from one step of the process to another since they do not exist in the same machine. REST APIs, RPC protocols, and messaging/streaming are the most used ones, but for reliability, [the last option is the preferred one for its asynchrony and the ease of building abstraction and utility layers around, to prevent contract coupling, facilitate data translation, avoid corrupted data to go through](https://www.enterpriseintegrationpatterns.com/patterns/messaging/Messaging.html)…


> **???** It is understandable to find that `1.c, undoing actions` should fall under `Fault tolerance`, especially given that the [existing literature](https://www.researchgate.net/publication/341244111_Fault_Tolerant_Central_Saga_Orchestrator_in_RESTful_Architecture) puts it under such umbrella. It is one of the key takeaways of this monogram to make a clear differentiation in this case, and to treat actions that have been [rejected](#completed-task) in a different manner to actions that have [failed](#failed-task).

## Existing approaches

### Enterprise Integration Patterns

There’s plenty of literature on the subject, but it’s hard to argue that [Enterprise Integration Patterns](https://www.enterpriseintegrationpatterns.com/) is anything but the most influential collection of patterns to solve these problems.

While the book talks about enterprise integration, where most of the applications being integrated are third parties, the patterns are widely used, especially when it comes to emulating behaviors that are convenient in non-distributed scenarios.

e.g., The saga pattern is commonly used to emulate ACID transactions.

Enterprise Integration Patterns is a recommended reading for anyone looking to deep dive in the subject of choreography of processes across systems and building maintainable integrations in general.

A deep understanding of these patterns will give you a solid grasp on how to handle `orchestration` and `communication` in business processes that require integrations with third parties.

### Formal Methods

Truth tables can help us explore the possible outputs of a conditional statement by mapping every possible condition evaluated. Anyone who ever got a conditional wrong, meaning every developer, knows that even apparently simple evaluations get misinterpreted often.

Using a truth table allows one to visualize all the possible states, which forces the mind to actively reason about the problem.

This is all well for conditionals running inside the memory of a single computer, but distributed systems integrating other distributed systems have a spectrum of possible interactions with so many combinations that no table that fits within the observable universe can hold them.

- [ ]  *TODO: Add a diagram illustrating the space of states in a distributed system.*

Tools like [TLA$^+$](https://lamport.azurewebsites.net/tla/tla.html) and [Alloy](https://haslab.github.io/formal-software-design/) can help us reason about every step in a process that can fail for different reasons by forcing us to specify every possible way the system can behave.

For systems having just six points of failure and two concurrent requests against the same resource, plus all the possible branching decisions to be made, the count of possible states gets in the order of millions. Since it’s impossible for a human to explore every possible state of such a system in a lifetime, these tools also allow us to define validations:

- Simple invariants that the system should never violate.
e.g. Stock should never be negative.
- Relatively simple temporal properties.
e.g. All orders should be eventually processed.
- More complex temporal properties.
e.g. An order that is completed, canceled, or returned can never exit that state.

Then these tools will run a model checker that will verify that these validations hold, and if it finds a single series of states that don’t, it produces an error with a trace of said series.

A passing specification is effectively a mathematical proof that the design of a system cannot present any unexpected behavior, given that:

- The assumptions made while specifying the system were accurate.
- The possible points of failure were all modeled.
- The properties and invariants constrain every undesirable behavior.

Those are quite a few conditions that have to be met. Fortunately, these models are easy to iterate on, significantly cheaper than any implementation, and, more often than not, are correct.

Azure’s [Cosmos DB has some of its guarantees](https://github.com/Azure/azure-cosmos-tla) modeled with TLA$^+$. [NASA](https://ntrs.nasa.gov/citations/20210020643) also uses it, and so does [Amazon](https://awsmaniac.com/how-formal-methods-helped-aws-to-design-amazing-services/).

> **!!!** It’s not the intention of this paper to give an introduction to these techniques beyond this brief explanation.

The solutions detailed in this paper are verified using TLA$^+$, you don’t need to learn TLA$^+$ to understand the solutions themselves or to implement them, but you might need to learn if you want to understand the verification.

Some of those solutions will make some compromises, given that the problems will be proven to be unsolvable in a deterministic way.

These techniques allow us to address `fault tolerance` and `concurrency` issues, but they also require sheer design discipline in verifying every scenario where this is a concern.

## The proposed solution

This paper will shape all the elements needed to model a unique take on the Process Manager Pattern that borrows (liberally) one idea from the Saga Pattern in order to design a `State Machine` that will be composed of `Tasks`, each one of them with every possible outcome mapped in a way that it will eventually perform a `Outcome event` which represent a final state in a `State Machine`.
