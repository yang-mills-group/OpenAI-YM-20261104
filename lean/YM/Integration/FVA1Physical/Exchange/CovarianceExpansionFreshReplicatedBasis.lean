import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPostedCovariance
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionReplicaAfterHearing

/-! Two fresh independent physical postings on the same, possibly already marked,
unit-normalized original history. The four signed settings cancel all older
singleton and pair terms before the two positive fibre laws are compared. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Marker Multi Comparison.RG02.Cumulants MeasureTheory RG
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {C : Census V}

def freshPairSecant (old : Poly C) (a b : V) (s : C.Mode) (h : V → ℂ) : ℂ :=
  let A : V → ℂ := Pi.single a (h a)
  let B : V → ℂ := Pi.single b (h b)
  ((postedUnit old (A+B)).part s - (postedUnit old B).part s) -
    ((postedUnit old A).part s - (postedUnit old 0).part s)

/-- The coefficient of two *fresh* sources exactly equals the independent
exponential source row. There is no restriction on the previously deposited
pair, or on its two singletons. -/
theorem fresh_pair_is_filed (old : Poly C) (unit : old.part C.quiet = 1)
    (a b : V) (ab : a ≠ b) (s : C.Mode) (pair : s.val = {a,b}) (h : V → ℂ) :
    freshPairSecant old a b s h = (Poly.pass (Multi.lambda C h)).part s := by
  let A : V → ℂ := Pi.single a (h a)
  let B : V → ℂ := Pi.single b (h b)
  change ((postedUnit old (A+B)).part s - (postedUnit old B).part s) -
    ((postedUnit old A).part s - (postedUnit old 0).part s) = _
  have a0 : A b = 0 := by simp [A, Ne.symm ab]
  have ab1 : (A+B) b = B b := by simp [a0]
  rw [posted_pair_increment old unit (A+B) B a b ab s pair ab1,
    posted_pair_increment old unit A 0 a b ab s pair a0, pass_lambda]
  simp [pair, A, B, ab]
  ring

/-- At a nonbare posting the only price left for the *double fresh secant* on
two positive vacua is the oscillation of their actions against the physical
two-source product. Earlier mixed and singleton deposits are unrestricted. -/
theorem fresh_pair_replica {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
    (old : X → Poly C) (unit : ∀x, (old x).part C.quiet = 1)
    (i j : V) (apart : i ≠ j) (s : C.Mode) (pair : s.val = {i,j})
    (h : X → V → ℂ) (env : Envelope (fun x => h x i * h x j))
    {k a b r : X → ℝ} (kn : ∀x,0≤k x) (ap : ∀x,0<a x) (bp : ∀x,0<b x)
    (rm : Measurable r) (anchor : ℝ) (same : ∀x,Real.log (a x)-Real.log (b x)=r x+anchor) :
    let u := fun x => k x*a x
    let v := fun x => k x*b x
    let original := fun x => freshPairSecant (old x) i j s (h x)
    let filed := fun x => (Poly.pass (Multi.lambda C (h x))).part s
    Integrable u μ → Integrable v μ → 0<(∫x,u x ∂μ) → 0<(∫x,v x ∂μ) →
    2*(∫x,u x ∂μ)*(∫x,v x ∂μ)*
      ‖FrozenRead.meanOn μ u original - FrozenRead.meanOn μ v filed‖ ≤
        ∫z, Replica.actionBill u v r z * ‖h z.1 i*h z.1 j-h z.2 i*h z.2 j‖ ∂μ.prod μ := by
  intro u v original filed ui vi up vp
  have join : original = filed := funext fun x => fresh_pair_is_filed _ (unit x) i j apart s pair (h x)
  have raw : filed = fun x => h x i * h x j := by
    funext x
    change (Poly.pass (Multi.lambda C (h x))).part s = _
    rw [pass_lambda, pair]
    simp [apart]
  rw [join,raw]
  exact Replica.reading kn ap bp rm anchor same env ui vi up vp

end YM.Integration.FVA1Physical.Exchange.RoseCut
