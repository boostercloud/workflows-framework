# Railway Event Processor

## When it doubt, your system is probably distributed

The need to integrate with third-party services is prevalent in the software industry. Many cross-cutting problems present massive and unique challenges that require specialized focus to solve; some of them would be:

- Making sure that transactional emails are sent to consumers without being filtered as spam requires such a degree of commitment that there are companies that do exclusively that.
- Receiving payments online, interacting with the myriad of platforms available, and with the banks reaches a point of complexity that many payment providers become banks themselves to make the service more reliable.
- Keeping track of interactions with customers has enough nuance to create an entire industry of Customer Relationship Management.
- Logistics and chain of supply.
- Providing customer support.
- Authentication and authorization.

The issue with this is that, no matter how simple you think your application is, having any of those increasingly necessary integrations, effectively turn any system into a distributed one, and in the words of Leslie Lamport:

> A distributed system is one in which the failure of a computer you didn't even know existed can render your own computer unusable.

Any integration with these systems, services in your own company, or actually anything that happens outside the memory assigned on your program, like a database, presents four major challenges:

- Orchestration.
- [Fault tolerance](#fault-tolerance).
- [Concurrency handling](#concurrency-handling).
- Communication.

> **!!!** This research looks to address Fault Tolerance and Concurrency Handling, but since they can’t be addressed without taking into account the other two, orchestration will be handled using the [Process Manager Pattern](https://www.enterpriseintegrationpatterns.com/patterns/messaging/ProcessManager.html), with some lessons learned from the Saga Pattern, and Communication will be solved via event streams and read models. It might catch the attention of the reader that, given the spotlight that message streaming platforms have in enterprise environments, to the point that seminal books as [enterprise integration patterns deal almost exclusively with messaging](https://www.enterpriseintegrationpatterns.com/patterns/messaging/Messaging.html), as a matter of fact, the read models that will be used for scheduling can, and often should, be stored via message queues, but that extra step will be omitted for simplicity.

The language described in this paper has the aspiration to be a framework usable as a bridge between engineering and business teams, so the degree of complexity of any given integration is visible and understandable by everybody involved.

First, the problem will be laid out in terms of the nature of integrations and why they are a constant challenge that requires . Then the core concepts will be introduced, the `Task`, the `Compromise`, and the `Transition`.

All of these will be put together with an example in the `Workflow` definition.

Finally, a design will be provided for the abstraction of every kind of `Task`, with a formal proof of correctness for each. Together with the solutions, there will be proof of the unsolvable nature of the opaque integrations.

The solution design is built around the assumption of an event sourced, or at least event-driven system, and it should be possible to apply these principles to such systems without any modification. A non-event-oriented system can implement this pattern with relative ease as long as it follows the `Command Query Responsibility Segregation` principle. Beyond that, major concessions might be needed, forfeiting the correctness provided out of the box by this framework.

The end goal is to provide a [safe](#code-safety) structure to connect every step of these processes, so they can be built and maintained as a deterministic state machine.

> Every part of the paper is written as a sub page at the moment to facilitate review, later on, this will be merged in a single document.
