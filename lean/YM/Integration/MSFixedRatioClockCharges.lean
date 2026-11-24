import YM.Comparison.RG02.Adjacent.Sale
import YM.RegulatorIR.Primitives.Verse
import YM.FormalBulk08.Wine.Cab

/-! The native finite moving-field invoice on every coupling grade and tensor rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSFixedRatioClockCharges
open Function Filter Finset PowerSeries Comparison.RG02 Comparison.RG02.Adjacent
open Comparison.RG02.Moving Comparison.RG02.Moving.Path RegulatorIR FormalBulk08
open scoped Classical Topology BigOperators ContDiff

theorem powers (f : ℝ→ℝ) (hf : ContDiffAt ℝ ∞ f 0) (j : ℕ) :
    Prim.tale (f^j)=(Prim.tale f)^j := by
  induction j with
  | zero=>
    rw [pow_zero,pow_zero]
    change Prim.tale (fun _:ℝ=>1)=1
    exact (Prim.tale_const 1).trans (map_one _)
  | succ j ih=>
    rw [pow_succ,pow_succ,Prim.tale_mul (f:=f^j) (g:=f) (hf.pow j) hf,ih]

theorem charged (K : UnitCost) (e j r : ℕ) :
    motion (Adjacent.money K 0 j r) e=if j≤e then
      (Wine.bill (Prim.tale K.rating) (Prim.tale (fun t=>(K.rating t)⁻¹)) e j r : ℂ) else 0 := by
  rw [Adjacent.triangular]
  split_ifs with h
  · let f:=fun t=>Adjacent.tags 0 j r (K.rating t)
    have hf : ContDiffAt ℝ ∞ f 0 := (Adjacent.checks K 0 j r).of_le le_top
    have hr : ContDiffAt ℝ ∞ K.rating 0 := K.smooth.of_le le_top
    have hu : ContDiffAt ℝ ∞ (fun t=>(K.rating t)⁻¹) 0 :=
      hr.inv (by rw [K.origin]; exact one_ne_zero)
    have expected : Prim.tale f=(Prim.tale K.rating)^j*(Prim.tale (fun t=>(K.rating t)⁻¹))^r := by
      have he : f=K.rating^j*(fun t=>(K.rating t)⁻¹)^r := by
        funext t
        simp [f,Adjacent.tags]
      rw [he,Prim.tale_mul (f:=K.rating^j) (g:=(fun t=>(K.rating t)⁻¹)^r) (hr.pow j) (hu.pow r),powers K.rating hr,powers _ hu]
    change Assembly.jet (Complex.ofRealCLM ∘ f) (e-j) 1=
      Complex.ofRealCLM (coeff (e-j) ((Prim.tale K.rating)^j*(Prim.tale (fun t=>(K.rating t)⁻¹))^r))
    have hfe : ContDiffAt ℝ (↑(e-j)) f 0 := hf.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [←Assembly.jet_apply_left Complex.ofRealCLM f (e-j) hfe]
    apply congrArg Complex.ofRealCLM
    exact (Prim.tale_jet (f:=f) (e-j)).symm.trans (congrArg (coeff (e-j)) expected)
  · rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {W : Adjacent.Display X}
theorem measured (K : UnitCost) (k : ℕ) {p : ℕ→ℤ} (hw : Adjacent.Charge k p W)
    {e : ℕ} (he : e≤k) (x : X) :
    Adjacent.born W K 0 k e x=W e x + ∑ j∈range e,∑ r∈range ((p j).toNat+1),
      (Wine.bill (Prim.tale K.rating) (Prim.tale (fun t=>(K.rating t)⁻¹)) e j r : ℂ)*
        Assembly.jet (W j) r x := by
  rw [Adjacent.ledger K 0 k hw e he]
  congr 1
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro r _
  rw [charged,if_pos (mem_range.mp hj).le]
end YM.Integration.MSFixedRatioClockCharges
end
