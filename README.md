# Smart contract programming language group - initial survey
## Contract examples
### Multisig
For sending arbitrary transactions, good example of basic handling of cryptography

### Transferable token
Ubiquitous. Minimal example of handling ownership, which is what blockchains are all about. Can we formally prove that "the total amount of tokens is constant" from our example?

### Registry
Widespread, more handling of ownership.

### Sealed auction
Widespread and critical to get right, look at ICOs and ENS.

### State channel
Come in many different forms, but a toy state channel that just handles signature verification and keeps one hash of a state should suffice, with as simple of a challenge mechanism as possible.

### Quadratic voting
For a set of preapproved actors.

## Desiderata
- Intuitive, the behavior of the code matches the intent of the programmer

- Easy to reason about the state of a contract
  (Metric : Complexity of proofs)
- Intuitive handling of cryptographic functions
  (Metric : Number of coders crying on Stack Exchange)
- Easy to handle ownership, since this is probably the most common use of stateful contracts on a blockchain
  (Metric : Complexity of proofs regarding ownership)
- Correct by construction code, type checking of the code assures that it satisfies its intended properties
  (Metric : Proof theoretic strength of the type system)
- Compositionality
  (Metric : Largest individual part making up a composed system, smaller is better)

## Tools & Paradigms
I believe the most important thing to achieve all of the points above is a safe, theoretically sound type system.
By safe, I mean a language in which, as far as is possible, "well-typed programs cannot go wrong". The intent of the programmer should be reflected as closely as possible in the type declaration of a function. Instances of `throw` (or when `return false` is used for the same purpose) in Solidity should correspond to a failure of type check.

Depending on the structure of the type system, some type checking may need to be done at execution time. In that case, there should be a keyword `unsafe` that disables this to increase performance.

Keeping track of state can be done with monads or using linear types. Inspiration can be taken from Krishnaswami's 'Integrating Linear and Dependent Types', https://www.cl.cam.ac.uk/~nk480/dlnl-paper.pdf; handling pointers is not all that different from handling ownership.

The specifics of how new types are introduced varies greatly with the design of the type system. At the very least, I would like to see function, sum and product types. The type system should be closely related to, or a direct implementation of a well studied type system such as the Calculus of Inductive Constructions, (Intensional or Extensional) Martin Löf Type Theory, λP2 or ιλP2.

Cryptographic functionality can be included as primitve types. For example, in a state channel, one could update the state only if `msg : ECVerify(person, previousstate)` type checks.

Compositionality can be achieved by having functions as first class citizens.

## Misc
The property of termination arises naturally for some type systems and not for others. The two roads of ensuring termination come from a complex type system or conservative expressiveness. I don't think guaranteed termination should be actively pursued, but I am happy if it ends up being a property of our system.