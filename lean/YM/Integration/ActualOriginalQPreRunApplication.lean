import YM.Integration.ActualOriginalQPreRunRequest
import YM.Integration.FullQLocalPreRunPurchase

/-!
Apply a covered original-Q request on one already selected receipt.
Coverage is a predicate on the pre-Run request family alone. Every later
covered order and load uses the same R, the same raised Sheet and its same n.
No new Run is selected by this file, and no countable coverage theorem is
postulated. The complete initial Grant and its two actual local floors are
derived from the existing receipt.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOriginalQPreRunApplication
open Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato
open FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric.Retained
open scoped Topology

variable {G : Gauge}

private def cast_grant {V : Type} [DecidableEq V] [Fintype V]
    (R : Run G) (hG : G.Simple)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (W : ProfileWidths) (P : WidthPayment R.family W)
    {C₁ C₂ : Census V} {J₁ J₂ : Request V}
    (hC : C₁ = C₂) (hJ : J₁ = J₂)
    {caps : Handoff.OutputCapacities} {floor n : ℕ → ℕ}
    {pre : LocalComparison.Global.PreBlockConstant}
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0))
    (H : Grant (R := C₁) caps (RunFormalChain.fromRun R) J₁
      (ActualRequestNumericSchedule.selected R hG hReadout W P J₁ cap hcap hcap0)
      floor n pre) :
    Grant (R := C₂) caps (RunFormalChain.fromRun R) J₂
      (ActualRequestNumericSchedule.selected R hG hReadout W P J₂ cap hcap hcap0)
      floor n pre := by
  cases hC
  cases hJ
  exact H

variable {I : ℕ → Type} [∀ k, DecidableEq (I k)] [∀ k, Fintype (I k)]
  {B : ∀ k, Census (I k)} {J : ∀ k, Request (I k)}
  {D : MS.Local.Physical.Deck G}

/-- Literal coverage on the canonical finite alphabet, before any Run.
An external finite-alphabet relabeling must be proved before using this test. -/
structure CoveredAt (k : ℕ) (u : I k → MS.Rake.Label D) (K : Request (I k)) : Prop where
  census : B k = Stock.census (I k)
  request : J k = ActualOriginalQPreRunRequest.request u K

/-- A family-wide coverage obligation; there is no Run or clock parameter. -/
def Covers {Q : Type*} (index : Q → ℕ)
    (u : ∀ q, I (index q) → MS.Rake.Label D)
    (K : ∀ q, Request (I (index q))) : Prop :=
  ∀ q, CoveredAt (B := B) (J := J) (index q) (u q) (K q)

variable {hG : G.Simple} {R : Run G}
  (r : PreRun.Receipt hG I B J R)

/-- The unbounded numerical input passed to the unchanged initial factory. -/
def baseSchedule (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (k : ℕ) (K : Request (I k)) (cap : ℕ → ℝ)
    (hcap : ∀ m, 0 ≤ cap m) (hcap0 : Tendsto cap atTop (𝓝 0)) :
    NumericSchedule R.family K :=
  ActualRequestNumericSchedule.atRun R hG hReadout
    (r.chosen.entry k).widths (PreRun.width_payment r k) K cap hcap hcap0

/-- Exact Grant at the same request and bounded schedule as InitialSelection. -/
def initialGrant (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (k : ℕ) (u : I k → MS.Rake.Label D) (K : Request (I k))
    (h : CoveredAt (B := B) (J := J) k u K)
    (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :
    Grant (R := Stock.census (I k)) (r.chosen.entry k).capacities
      (RunFormalChain.fromRun R) (ActualOriginalQPointSetup.request R u K)
      (ActualOriginalQInitialInput.schedule R hG u K
        (baseSchedule r hReadout k K cap hcap hcap0))
      (r.chosen.entry k).floor r.n (r.chosen.entry k).constant :=
  cast_grant R hG hReadout (r.chosen.entry k).widths
    (PreRun.width_payment r k) h.census h.request cap hcap hcap0
    (PreRun.grant r hReadout k cap hcap hcap0)

/-- The same n pays both local floors before every later datum and period. -/
theorem initial_local_floors (k : ℕ) :
    ∃ first : ℕ, ∀ d : LocalFormal.Datum R.family (Stock.census (I k)),
      first ≤ d.level → Handoff.LocalFloors (r.chosen.entry k).floor r.n d := by
  obtain ⟨first, hf⟩ := PreRun.floors_eventually r k
  exact ⟨first, fun d hd => hf d.level hd⟩

/-- Every covered request uses this same receipt and this same R. -/
def familyGrant {Q : Type*}
    (index : Q → ℕ) (u : ∀ q, I (index q) → MS.Rake.Label D)
    (K : ∀ q, Request (I (index q)))
    (cover : Covers (B := B) (J := J) index u K)
    (hReadout : RG05Preconstruction.ReadoutPurchase R.b)
    (q : Q) (cap : ℕ → ℝ) (hcap : ∀ m, 0 ≤ cap m)
    (hcap0 : Tendsto cap atTop (𝓝 0)) :=
  initialGrant r hReadout (index q) (u q) (K q) (cover q) cap hcap hcap0

end YM.Integration.ActualOriginalQPreRunApplication
end
