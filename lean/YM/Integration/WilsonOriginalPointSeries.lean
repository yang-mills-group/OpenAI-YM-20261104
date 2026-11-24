import YM.Integration.WilsonOriginalPointTaste

/-! Absolute physical point series for the ambient old root, with its marked radius retained. -/

noncomputable section
namespace YM.Integration.WilsonOriginalPointTaste
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Overlay FVA1 RG3.Held RG3.Forms RG3.Script.Picnic
open LocalComparison ComparisonDensity.Address
open scoped Classical Topology BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] (D : V→Orbit)
  {G : Gauge} {n : Side} {P : Rep G n} (a : Bands (Stock.census V) P)

/-- Each arbitrary input has its own positive convergence radius. The contracted bill is unchanged. -/
theorem ambient_radius {w : V→ℝ} {u c d b : ℝ} (t : a.Radial w u c d b)
    (x : TestSpace D) : ((representation D a).menu.terms x).Radial
    (fun v => w v/(1+‖evaluations D x v‖)) u c d b := by
  let M (v : V) := 1+‖evaluations D x v‖
  have pos (v : V) : 0<M v := by dsimp [M]; positivity
  exact QLocalRadialPublication.tested_radial a
    (fun v=>div_pos (t.1 v) (pos v)) (fun v=>(pos v).le)
    (fun v=>le_of_eq (div_mul_cancel₀ _ (pos v).ne')) t
    (fun _ : Unit=>evaluations D x) (fun _ v=>by dsimp [M]; linarith) ()

/-- Original charged forced rows, hard-cluster catalogue and regular log all converge at
this ambient test, including outside the unit ball. -/
theorem ambient_series {w : V→ℝ} {u c d b δ κ : ℝ} (ha : a.Active) (t : a.Radial w u c d b)
    (H : P.activities.Valid P.p δ κ) (x : TestSpace D) :
    (∀i U,Summable (fun j=>((representation D a).menu.terms x).tagged i j U)) ∧
    (∀U,Summable (fun i=>((representation D a).menu.terms x).packet i U)) ∧
    ∀U,Summable (fun i=>((representation D a).leaf x).contents.ray i U) := by
  have live:=(active D a ha x).articles
  have due:=ambient_radius D a t x
  exact ⟨fun i U=>(((representation D a).menu.terms x).baseBound live due H U).1 i,
    fun U=>(((representation D a).menu.terms x).population live due H U).1,
    fun U=>(((representation D a).menu.terms x).bulkBound live due U).1⟩

/-- Reading a fixed physical mode spends one inverse of the purchased radius on each
occupied mark. The formula includes the quiet mode. -/
theorem coefficient {τ : ℝ} (hτ : 0<τ) (z : Poly (Stock.census V)) (k : (Stock.census V).Mode) :
    ‖z.part k‖ ≤ Poly.price (fun _=>τ) z / τ^k.val.card := by
  apply (le_div_iff₀ (pow_pos hτ _)).2
  have due := Finset.single_le_sum (f := fun j : (Stock.census V).Mode=>Poly.toll (fun _=>τ) j*‖z.part j‖)
    (fun j _=>mul_nonneg (Poly.worth (fun _=>hτ) j).le (norm_nonneg _)) (Finset.mem_univ k)
  simpa only [Poly.price,Poly.toll,Finset.prod_const,mul_comm] using due

end YM.Integration.WilsonOriginalPointTaste
