import YM.Integration.WilsonOriginalForcedMarkerIntake

/-! The final once-divided hard bill, on the actual supports and budgets
authorized for both mergers, for the selected occupied difference. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalForcedMarkerPrice
open Function Filter Finset Lattice Wilson RG Ac Marker QuadraticLocal QuadraticLocal.Fusion
open QuadraticLocal.Canopy QuadraticLocal.Fusion.Attached RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe
open Push Push.Corrected Push.AbsoluteSums
open WilsonForcedMarkerLine WilsonOriginalForcedMarkerMerger
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {p : BudgetPoint} {a b r q : ℝ} {B:ℕ}
    {V : Type} [DecidableEq V] {R : Marker.Census V} {o : V→Site n}
    {v : V} {T I : Type*} {U W : Activities G n} {w : V→ℝ}
    {P:ℕ→ForcedAddress G n} {K:Code G n}

def Invoice (A B:Hard T p P K o R) (w:V→ℝ) (b:ℕ) (a price:ℝ) : Prop :=
  ∃ f:ℕ→Poly R,(∀ i t U,Width.Covered (B.hard t i U-A.hard t i U) (f i)) ∧
    Ac.Hit (fun i=>(P i).support) b (fun i=>Poly.price w (f i)) a price

theorem paid (A T₁ C:Hard T p P K o R)
    (hit : Related v (q:ℂ) A T₁ C) (hq:0≤q) (hw:∀ i,0<w i)
    (lo:A.Paid w B a b) (hi:C.Paid w B a r) : Invoice A T₁ w B a (q*(r+b)) := by
  obtain ⟨g,hg,low⟩:=lo.wages
  obtain ⟨f,hf,high⟩:=hi.wages
  refine ⟨fun i=>(q:ℂ) • (f i+g i),?_,?_⟩
  · intro i t Z j
    have L:=hit t i Z
    have hp : T₁.hard t i Z - A.hard t i Z = (q:ℂ) • (C.hard t i Z-A.hard t i Z) := by rw [L.value]; abel
    rw [hp,Poly.part_smul,Poly.part_smul,Poly.part_plus,norm_mul,Complex.norm_real,Real.norm_of_nonneg hq]
    change q*‖(C.hard t i Z).part j-(A.hard t i Z).part j‖ ≤ ((q:ℂ)*((f i).part j+(g i).part j)).re ∧ _
    constructor
    · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re]
      exact mul_le_mul_of_nonneg_left
        ((norm_sub_le ..).trans (add_le_add (hf i t Z j).1 (hg i t Z j).1)) hq
    · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_im,
        (hf i t Z j).2,(hg i t Z j).2,add_zero,mul_zero,zero_mul]
  · intro y
    refine Extra.Multi.Budget.mono (Extra.Multi.Budget.scale (budget_plus (high y) (low y)) hq) ?_ ?_ le_rfl
    · intro i; split
      · exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le
      · exact le_rfl
    · intro i; split_ifs
      · dsimp only
        rw [Poly.adapted,Complex.norm_real,Real.norm_of_nonneg hq]
        calc
          _ ≤ (q*(Poly.price w (f i)+Poly.price w (g i)))*_ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Poly.addition hw ..) hq) (Real.exp_pos _).le
          _ = _ := by ring
      · simp

theorem first [Fintype V] {e f:ℝ} (A:Hard T p U.forced U.K o R)
    (D:Kiosk.First p U W e f a) (hw:∀ i,0<w i) (ha:0≤a) (price:A.Paid w p.B (a+1) e) :
    (Kiosk.First.led A D).Paid w p.B a f :=
  Kiosk.turned _ _ _ ((Kiosk.shape D.oldP D.oldV A).paid D.roll D.softens hw ha
    (Kiosk.turned _ _ A price) D.softPaid D.funds)

theorem second [Fintype V] [Countable I] {e f:ℝ} (A:Hard T p U.forced U.K o R)
    (M:ShiftRows T I G p o R) (D:Kiosk.Second p U W e f a r) (hw:∀ i,0<w i)
    (ha:0≤a) (price:A.Paid w p.B (a+1) e) (fee:M.Budget w p.B (a+1) r) :
    (Kiosk.Second.canopy A M D).Paid w p.B a f :=
  Kiosk.turned D.projection.symm D.keeps.symm _ (M.budgets D.softens
    (Kiosk.shape D.oldP D.oldV A) hw ha D.softPaid (Kiosk.turned _ _ A price) fee D.funds)

end YM.Integration.WilsonOriginalForcedMarkerPrice
end
