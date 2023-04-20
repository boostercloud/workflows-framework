# The Task

An abstraction over a single step in a workflow, it is modeled after a state of a state machine, and all its possible results, including those of failure, will point out to a different task.

### To-Do Item

They require one external action to happen: a user interaction, receiving a message from a queue, a webhook from a payment provider, or other similar interactions. Once that is received, a decision will be made to move to the next step.

### State

A step in the workflow that will perform an action synchronously and, using the result of such action, will decide on the next step.

> **!** Notice that neither of them are concerned with fault, the goal of the abstraction is exclusively to make a decision.
