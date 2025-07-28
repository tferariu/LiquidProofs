State Modeling Discussion Report
Tudor Ferariu July 24, 2025

review by Philip Wadler


First paragraph -- good

"We refer to the UTxO locked by our validator script as the "Smart
Contract", as this is how they are implemented on the Cardano
blockchain." Usually it is a NFT---you should mention this.

--add some lead-in to the NFT ThreadToken

"This context is the most complex component, as it encodes all the
information in the transaction being validated, the inputs, outputs,
signatories, as well as the datum and redeemer. The main reason why
they are given separately, even though they are technically
redundant" Here "they" means datum and redeemer. That's clear to
you, but not to the reader who has seen a list of five things:
inputs, outputs, signatories, datum, redeemer.

--be in the reader's mindset
--pronoun refers to the last nouns you mentioned.


"→ is a binary relation on Q" Where do the labels come into it?
And the actions Σ? Are the labels the same as Σ or distinct?

--arrow is actually ternary operaiton
--keep in mind reader (dont autocomplete information)
--check formalism corresponds directly to what I have in mind
--another way to check: triple, dangling reference
--use 1 name for 1 thing

"inputs of the validator" This refers to all five of the things
in your list above, one of which is inputs---bound to confuse your
reader.

"The redeemer becomes input" Now inputs has three meanings: the list
of five, the entry "inputs" in that list, the entry "redeemer" in that
list.

--literature forcing contradiction
--input -> input utxo
--redeemer input state machine


"What is the datum and value of our state if the transaction spends
the entire smart contract and does not propagate it further?"
In formal text, you need to cite Figure 2 here. I found this paragraph
confusing, because it doesn't refer to the idea of three relations that
we have already agreed: initial, continuing, terminal.

--rejig so that which relation used determines continuing or not
--description of high level relates to low level
--continuing built in
--translation gets more complicated
--check things line up properly

--dont hide self-continuation in the library
--theorem linking high level to low level !!
--rexplore levle of abstraction
--high level higher
--low level lower

--tying into spec..? just use their spec as low-level

--relation between low level and ledger / separate or conflate them
--predicate from low to high

--change high level so it doesn't talk about continuing


--document on choice
--separate low level -> ledger
--or high -> ledger


--find instance of scriptcontext used for their tests for ledger model

--cons : - low level much mroe convenient
--       - maybe incomplete components

"This is not necessarily an issue because, for a correctly defined
state transition system, we can easily prove that these components are
not necessary" Good. Another reason it is not an issue is because
eventually we will prove an equivalence between the transition
relation and the validator, showing that the transition cannot depend
on information not available to the validator. Aha, you state this two
sentences later!

--maybe make the two closer


"the type of Input States is different from Output States, so we need
to somehow translate from one to the other" Using _≅_ as the name for
this is a bad idea, as _≅_ typically denotes an equivalence relation
and this relation doesn't even have the right type for an equivalence.
Perhaps ~ is a better name.

--use a different symbol

"but they only contain the information that they require, which makes
them unsuitable for inductive reasoning on state transitions."  You
could use the same fix as before, introducing a ~ relation between
states with inputs and states with outputs, but now the type system
doesn't give as much help.

--add this as an example

"but it is still needlessly complicated and undesirable" I don't know
what this sentence means. I think it means "I (Tudor) don't like it",
but dressed up to sound more objective.

--use sketches to show shorters and cleanest spec
--habit: honesty, just say I don't like this one, then find more objective


By the end, you have convinced me that monolithic state is the best
alternative, so the document achieves it's goal.


-- MORE FORMALLY
-- more checking, pronouns, figures, citations, etc.



