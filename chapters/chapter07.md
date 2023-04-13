# Compromise Decision of Black Boxed Tasks

Once taken the concerns into account, a decision has to be made about handling possible failure for the task:

> **!** This is about `possible failure` it is often possible to guarantee that a task has failed, if that’s the case, that failure will be treated as it would in a deterministic `task`.

## At least once

If there’s a suspicion that the task has failed, it will be retried indefinitely, assuming the risk that it might happen more than once. It is important to understand that this means to attempt it until its success `is registered` or it expires, meaning that it might even succeed indefinitely.

e.g. Blocking a user that has been deemed hostile should be attempted until success is registered.

## Up to `n` times

If there’s a suspicion that the task has failed, it will be retried a certain amount of times, assuming the risk that it might happen more than once.

e.g. Sending a verification code as an SMS, it’s desirable to guarantee that it gets sent, but the costs could pile up rather quickly if the retries happen indefinitely for every user.

## At most once

If there’s a suspicion that the task has failed, it’s given up silently.

e.g. Sending a welcome email.

## Important: Human intervention required

If there’s a suspicion that the task has failed, there will be a step where a human has to make a decision. This is not a special kind of compromise, as there’s already a kind of task for this, the `External Action Required`.

e.g. A user requested the deletion of their private data, but the confirmation email could not be sent, it is desirable to reach out to the user to avoid legal risks.

# The conclusion

The outcome of a task that has been deemed `possibly failed` needs to be mapped to a business outcome, that is, a `transition`. All of the other conclusions are mapped just like the deterministic ones.
