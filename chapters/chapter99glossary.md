# Glossary

#### Code safety:
Property of code that handles every possible state it can go through. A safe function has constraints in its input, so every possible value that is allowed by the compiler is valid, never throws exceptions for any valid value of its input, and always returns a valid value, specified by its return type.

#### Completed task:
A task that has executed without fault. This definition is not concerned as to whether the action was accepted or rejected.

e.g. A fraud check that returns a result, regardless of the user being deemed trustworthy or not, has completed.

#### Concurrency handling:
Capacity of a system to behave in a predictable manner when interacting with a resource that can be accessed by another process, be it a third party, another instance of the current system or another process that is part of the same system.

#### Failed task:
A task that could not be completed after all of the fault tolerance mechanisms have exhausted any option to recover or the task can’t be performed for other reasons.

e.g. An email provider throttled a request, a circuit breaker acts in to give the service some time to recover, after the request successfully goes through, it returns a Bad Request response because the content had some invalid characters.

e.g. A SMS provider rejects an attempt to send a message because the associated account does not have enough credits.

#### Fault tolerance:
Capacity of a system to continue functioning in a predictable manner after an external action fails to execute as expected, it is assumed that the fault is transient, that is, that the external system will be able to eventually respond.

