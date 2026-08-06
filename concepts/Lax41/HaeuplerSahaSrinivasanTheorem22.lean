import Mathlib
import Lax41.HaeuplerSahaSrinivasanDefinitions

/-!
---
title: Haeupler–Saha–Srinivasan Theorem 2.2
type: theorem
---
Suppose the asymmetric local-lemma conditions hold for a finite set
$\mathcal A$ of bad events.  Let $B$ be any event determined by the same
independent random variables, whether or not $B$ belongs to $\mathcal A$.
The probability that $B$ is true at least once during the Moser--Tardos
algorithm is at most
$$
  \Pr[B]\prod_{C\in\Gamma(B)}(1-x(C))^{-1}.
$$
In particular, the same bound holds for the probability that $B$ is true in
the output distribution of the algorithm.
-/

set_option autoImplicit false

open scoped ENNReal

namespace Lax41.HaeuplerSahaSrinivasanTheorem22

open Lax41.MoserTardosDefinitions
open Lax41.HaeuplerSahaSrinivasanDefinitions

/-- The distributional local lemma of Haeupler, Saha, and Srinivasan, Theorem 2.2. -/
axiom theorem_2_2
    {Event : Type} [Fintype Event] [DecidableEq Event]
    {Variable : Type} [Fintype Variable] [DecidableEq Variable]
    (Value : Variable → Type) [∀ i, MeasurableSpace (Value i)]
    (distribution : ∀ i, MeasureTheory.Measure (Value i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (distribution i)]
    (badEvents : Finset Event)
    (variablesOf : Event → Finset Variable)
    (event : ∀ A, Set (LocalAssignment Value (variablesOf A)))
    (event_measurable : ∀ A, MeasurableSet (event A))
    (selectionRule : ResamplingRule Value
      (badEventVariables badEvents variablesOf)
      (badEventSet Value badEvents variablesOf event))
    (x : BadEventIndex badEvents → NNReal)
    (x_positive : ∀ A, 0 < x A)
    (x_less_than_one : ∀ A, x A < 1)
    (local_lemma_hypothesis : ∀ A,
      eventProbability Value distribution
          (badEventVariables badEvents variablesOf)
          (badEventSet Value badEvents variablesOf event) A ≤
        ((x A * ∏ C ∈ dependencyNeighborhood badEvents variablesOf A.1,
          (1 - x C) : NNReal) : ℝ≥0∞))
    (B : Event) :
    let upperBound :=
      eventProbability Value distribution variablesOf event B *
        ((∏ C ∈ dependencyNeighborhood badEvents variablesOf B,
          (1 - x C)⁻¹ : NNReal) : ℝ≥0∞)
    probabilityEventEverOccurs Value distribution badEvents variablesOf event
        selectionRule B ≤ upperBound ∧
      probabilityEventInOutput Value distribution badEvents variablesOf event
        selectionRule B ≤ upperBound

end Lax41.HaeuplerSahaSrinivasanTheorem22
