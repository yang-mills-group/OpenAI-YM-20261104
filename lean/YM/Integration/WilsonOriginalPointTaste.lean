import YM.Integration.QLocalRadialBudget
import YM.Integration.LocalComparisonFunctionalRetains

/-! The manuscript's radial publisher on actual ambient point functions, with the same original tags and sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPointTaste
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Overlay FVA1 RG3.Held RG3.Forms RG3.Script.Picnic
open LocalComparison ComparisonDensity.Address
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {P : Rep G n} {V : Type} [DecidableEq V] [Fintype V]
variable (D : V→Orbit) (a : Bands (YM.Stock.census V) P)

def evaluations (x : TestSpace D) (i : V) : ℂ := (x i).val 0

def representation : Taste (TestSpace D) a.origins P (YM.Stock.census V) :=
  QLocalRadialBudget.taste a (evaluations D) a.rays a.support (fun _ _=>0)

omit [Fintype V] in
private theorem monomial (s : Finset V) (c : ℂ) :
    Letter ℂ (fun v=>(D v).Mood) s (fun x=>(∏ i∈s,(x i).val 0)*c) := by
  have separate (x : TestSpace D) (i : V) (hi : i∈s) (b : (D i).Mood) :
      (∏ v∈s,(update x i b v).val 0)=b.val 0*(∏ v∈s.erase i,(x v).val 0) := by
    rw [←Finset.mul_prod_erase s (fun v=>(update x i b v).val 0) hi,update_self]
    apply congrArg (b.val 0 * ·)
    exact Finset.prod_congr rfl fun v hv=>by rw [update_of_ne (Finset.ne_of_mem_erase hv)]
  constructor
  · intro x y eqv
    exact congrArg (·*c) (Finset.prod_congr rfl fun i hi=>congrArg (fun b : (D i).Mood=>b.val 0) (eqv i hi))
  · intro x i hi f g
    simp only [separate x i hi]
    change (f.val 0+g.val 0)*_*c=_
    simp only [add_mul]
  · intro x i hi r f
    simp only [separate x i hi]
    change (r*f.val 0)*_*c=r*(_*_*c)
    simp only [mul_assoc]

/-- The complete old input is an actual independent-slot multilinear function before all tests. -/
theorem multilinear : Multilinear D (representation D a) where
  regular i U := monomial D (a.rays i).val (a.H i U)
  forced i j U := monomial D (a.marks i j).val (a.entries i j U)
  unit i := by
    change Letter ℂ (fun v=>(D v).Mood) {i} (fun x=>(x i).val 0*a.units i)
    simpa only [Finset.prod_singleton] using monomial D {i} (a.units i)
  captions i := Letter.still

theorem active (h : a.Active) (x : TestSpace D) : ((representation D a).leaf x).Active :=
  ⟨QLocalRadialPublication.active a h (evaluations D x),⟨h.proper,h.pins⟩⟩

/-- The original prescribed point addresses remain at the same actual lower roots. -/
theorem retains (h : a.Active) : FunctionalRetains (representation D a) (fun v=>{a.origins v}) :=
  FunctionalRetains.of_active (fun x=>active D a h x)

/-- All physical regular and forced entries are multiplied in their actual square-free modes. -/
theorem density (h : a.Active) {w : V→ℝ} {u c d b δ κ : ℝ} (t : a.Radial w u c d b)
    (H : P.activities.Valid P.p δ κ) (x : TestSpace D) (U : Config G n) :
    ((representation D a).leaf x).density U=NativeWeightedColors.fuse id (evaluations D x) (a.density U) := by
  rw [QLocalRadialPublication.density a (evaluations D x) h t H U]
  change (Real.exp (P.exponent U):ℂ) • (Poly.pass (((QLocalRadialPublication.bands a (evaluations D x)).extra U)+(∑' i : ℕ,Poly.send (a.rays i) 0))*_)=_
  simp only [Poly.send_zero,tsum_zero,add_zero]
  rfl

end YM.Integration.WilsonOriginalPointTaste
