import YM.Integration.WilsonOriginalPointTaste
import YM.Integration.WilsonOriginalPointUnitTest
import YM.Integration.WilsonRetainedMarkedInletHard

/-! The original physical point test pays every ordinary and forced field on the common signed band. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPointTaste
open Function Finset Lattice Wilson RG Marker Overlay FVA1 RG3.Held RG3.Script.Picnic LocalComparison ComparisonDensity.Address
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V] [Fintype V]
    (D : V→Orbit) (a : Bands (YM.Stock.census V) P) (h : a.Active) {w : V→ℝ} {u c d b δ κ : ℝ}
    (t : a.Radial w u c d b) (H : P.activities.Valid P.p δ κ)

/-- The very same signed harmonic field on the actual four-dimensional nonterminal source is
billed at the original support allowance and includes the quiet physical charge once. -/
def Priced (x : IndependentTests D) : Prop :=
  let v := QLocalRadialPublication.bands a (evaluations D (testInclusion D x))
  ∃ (live : v.Active) (bounded : v.Radial w u c d b),
    let A := WilsonRetainedMarkedInlet.incoming v live bounded H
    A.Pays w (P.p.supportExponent-1) (WilsonRetainedMarkedInletRegular.cost P.p*(Fintype.card V*c)) (κ+Fintype.card V*(d*b)) ∧
    ∀U,A.density () U=((representation D a).leaf (testInclusion D x)).density U ∧ A.gas () U=v.cluster U

include h t in
theorem paid (hz : a.units=0) (x : IndependentTests D) : Priced D a (w:=w) (u:=u) (c:=c) (d:=d) (b:=b) H x := by
  let γ (y : IndependentTests D) := evaluations D (testInclusion D y)
  let v := QLocalRadialPublication.bands a (γ x)
  have live := QLocalRadialPublication.active a h (γ x)
  have radial : v.Radial w u c d b := QLocalRadialPublication.tested_radial a t.pure (M:=fun _=>1) (fun _=>zero_le_one)
    (fun j=>by simp) t γ (fun y i=>WilsonOriginalPointModes.root_bound D y i) x
  have zero : v.units=0 := by funext i;change γ x i*a.units i=0;rw [hz];simp
  refine ⟨live,radial,WilsonRetainedMarkedInletHard.original v live radial H,?_⟩
  intro U
  have view := density D a h t H (testInclusion D x) U
  have model := QLocalRadialPublication.density a (γ x) h t H U
  exact ⟨(WilsonRetainedMarkedInlet.original v live radial H zero U).trans (model.symm.trans view.symm),WilsonRetainedMarkedInlet.forced v live radial H U⟩

end YM.Integration.WilsonOriginalPointTaste
