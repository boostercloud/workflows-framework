\pagebreak
# Business concerns of a Black Boxed Task

This includes all the factors we need to take into account when making compromises over black-boxed tasks. This part of the framework is not formal, it aims to provide a checklist of factors to consider when making a decision, the decision itself is formal, as it will have an abstraction on top of it.

# Visibility

How likely is the non-execution or failure of the task to be perceived.

- **Self-evident.** By its own nature, the failure will be noticed.
e.g. If a refund is never sent, the user will eventually complain.
- **Traceable.** It’s possible to add reliable tracking mechanisms to follow up on the action being performed.
e.g. The deduction of the loyalty points from a user that purchased a product using them fails. We would need to set an alert for it and have someone verify what happened.
- **Invisible.** We can’t guarantee to know the outcome of a task.
e.g. We cannot determine whether an email has been opened or not. Mechanisms like tracking pixels might be blocked by the email service, so it’s possible that an email that was read shows as unread.

# Necessity

How critical is the step to the workflow

- **Must happen.** The workflow can’t continue without this step.
e.g. The payment must be confirmed before we start handling an order.
- **Should happen.** The workflow can continue, but there’s a consequence if it fails.
e.g. Bank account number validations are known to put back customers when they make a typo, so it’s desirable to allow them to continue and then reach out to them about a failed payment.
- **Nice to have.** It’s not needed, but it is presumed that it adds some value to the product.
e.g. Sending a satisfaction survey.

# Concern

Who gets directly hurt if the task fails:

- **Own.**
e.g. There’s a failure when registering an order as sent, and it gets sent twice.
- **Third party.**
e.g. The delivery data for an order to a logistics company gets corrupted, and the provider needs to reach out to fix the issue.
- **Customer.**
e.g. A refund is not sent when it’s due.

# Risk

The kind of consequences suffered:

- **Reputation.**
- **Legal.**
- **Data breach.**
- **Economic loss.**
