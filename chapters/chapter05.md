# Technical categories of tasks

## External action required

The `Task` is waiting for the third party to continue the execution.

e.g. A webhook from a payment provider or a response sent by a human.

## Idempotency enabled

The `Task` is executed against a service that provides a mechanism to uniquely identify an action. Said mechanism allows us to try to perform the action knowing that it will only impact the system once even if we have attempted it on the past or there is a duplicated process attempting the same action. This removes concerns for concurrency and fault tolerance, as it is possible to just attempt the action until we get an acceptance or rejection result and succeed in directing the workflow toward the desired next `Task`.

e.g. Many payment providers accept an `Idempotency Key` in their requests, so if we attempt a refund, and we generate a unique key per refund, we know we will never refund more than once.

## Optimistic lock enabled

This is a`Task` with the following characteristics:

- Either the API of the third party offers:
    - A way to attach a unique identifier to the action we want to perform.
    - A query mechanism that allows filtering via the aforementioned unique identifier.
- Or:
    - The nature of the task makes it so that the action can be identified deterministically without an additional identifier.
    - And the API offers a query mechanism that allows querying for that.
- A multistep process that can be canceled at any time before it is completed.

This way, we can, before we even start processing it, detect whether there is another process trying to perform the same action or whether there was a previous attempt that faulted. This allows us to attempt the action and verify between steps again for faulty concurrent access. Finally, it is possible to run a cleanup after one process has been successful. That is, we virtually allow multiple processes to race concurrently, allowing only the first of them to write the result and canceling the others.

## Pessimistic lock enabled

This is a `Task` with the following characteristics:

- Either the API offers:
    - A way to attach a unique identifier to the action we want to perform.
    - A query mechanism that allows filtering via the aforementioned unique identifier.
- Or:
    - The nature of the task makes it so that the action can be identified deterministically without an additional identifier.
    - And the API offers a query mechanism that allows to query for that.

Without a multistep process that can be canceled at any time, we must rely on a central place to lock any other processes out of attempting the operation.

That is, we won’t allow a second attempt to run if there’s an ongoing process.

## Black boxed

This `Task` provides no ability to reliably determine if the operation is being performed by another process, or whether we are attempting it again from a previous failure.

For these processes, the beginning of an attempt is stored, so is the result, any attempt that starts, will check if there was a previous beginning recorded without a matching result, if that’s the case, a possible failure is detected, as it is impossible to know if the action was performed and its outcome. 

This case would require compromising in case of failure. A decision needs to be made if it’s detected that there was a previous attempt that did not finish:

- Have a human review it.
- Ignore it and move on.
- Retry it up to a certain amount of times.

# Common language definitions

All these definitions, for the sake of simplicity, will be condensed from the perspective of the common language into these three terms, so when discussing the design of workflows that integrate third parties, they will get referred to in the following three categories.

## To Do

This is the `External Action Required` type. An external service needs to reach to continue the workflow.

## Trivial

Services that have an explicit idempotency mechanism, rare, but always preferable.

Integrating with this category poses no challenge both in terms of correctness and performance. 

We can count on any action performed towards this service as that they will eventually [complete](#completed-task).

## Deterministic

This includes optimistic and pessimistic lock enabled third parties.

Integrating with this category poses a challenge in terms of correctness. The simplest approach is to consider all of them pessimistic and switch to the optimistic ones if there's a performance problem.

We can count on any action performed towards this service as that they will eventually [complete](#completed-task).

## Opaque

Black boxed.

These present an unsolvable challenge in terms of correctness, as we can neither guarantee a single execution nor failure (in the case of having a record of the attempt starting but not of the attempt outcome).

A business decision needs to be made in terms of what to do when failure is suspected.
