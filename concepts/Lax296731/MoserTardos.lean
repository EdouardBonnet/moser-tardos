import Mathlib
import Lax296731.MoserTardosDefinitions

/-!
---
title: The Moser–Tardos theorem
type: theorem
---
Let a finite family of mutually independent random variables determine a
finite family of measurable bad events.  For a bad event $A$, let $\Gamma(A)$
be the other bad events sharing a variable with $A$.  If there are numbers
$x(A)\in(0,1)$ such that
$$
  \Pr[A] \le x(A)\prod_{B\in\Gamma(A)}(1-x(B)),
$$
then some assignment avoids every bad event.  Moreover, the Moser--Tardos
resampling algorithm resamples each $A$ at most an expected
$x(A)/(1-x(A))$ times, so its expected total number of resamplings is at most
the sum of these bounds.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax296731.MoserTardos

open Lax296731.MoserTardosDefinitions

/--
The constructive asymmetric Lovász local lemma (Moser--Tardos, Theorem 1.2),
including its expected resampling bounds.
-/
axiom moser_tardos
    {Event : Type} [Fintype Event] [DecidableEq Event]
    {Variable : Type} [Fintype Variable] [DecidableEq Variable]
    (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (distribution i)]
    (variablesOf : Event → Finset Variable)
    (badEvent : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (badEvent_measurable : ∀ A, MeasurableSet (badEvent A))
    (selectionRule : ResamplingRule Value variablesOf badEvent)
    (x : Event → NNReal)
    (x_positive : ∀ A, 0 < x A)
    (x_less_than_one : ∀ A, x A < 1)
    (local_lemma_hypothesis : ∀ A,
      eventProbability Value distribution variablesOf badEvent A ≤
        ((x A * ∏ B ∈ dependencyNeighborhood variablesOf A, (1 - x B) : NNReal) :
          ℝ≥0∞)) :
    (∃ assignment : Assignment Value,
        ∀ A, ¬violates Value variablesOf badEvent assignment A) ∧
      (∀ A, expectedResamplings Value distribution variablesOf badEvent selectionRule A ≤
        ((x A / (1 - x A) : NNReal) : ℝ≥0∞)) ∧
      (∑ A : Event,
          expectedResamplings Value distribution variablesOf badEvent selectionRule A) ≤
        ∑ A : Event, ((x A / (1 - x A) : NNReal) : ℝ≥0∞)

end Lax296731.MoserTardos
