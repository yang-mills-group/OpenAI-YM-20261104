import YM.Integration.WilsonPositionProgramTrialTorusLine

/-! The actual based even inverse on the same finite regulator as the
occupied Fourier covariance. The origin subtraction keeps its full source
dependence before any coordinate is differentiated. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialBasedGhost
open Finset Lattice Pert.Orb
open WilsonPositionProgramTrialTorusLine (green)
open scoped Classical BigOperators
variable {G : Gauge} {n : Side}

def pole (x y : Site n) : ℝ := green (x-y)

theorem even (x : Site n) : green (-x)=green x := by
  apply Pert.Full.toroid_even

theorem lap_pole (x y : Site n) :
    lap (fun z => pole z y) x= -(if x=y then 1 else 0)+(n.val:ℝ)^(-4:ℤ) := by
  rw [show lap (fun z => pole z y) x=lap green (x-y) by
    unfold lap pole
    apply sum_congr rfl
    intro i _
    dsimp only
    rw [show x+step i-y=x-y+step i by abel,show x-step i-y=x-y-step i by abel]]
  change lap (fun y : Site n => (Pert.Full.toroid y).re) (x-y) = _
  rw [lap_shift]
  by_cases h : x=y <;> simp [h,sub_eq_zero]

def field (f : Site n → G.Color) (x : Site n) : G.Color := ∑ y, pole x y • f y

theorem lap_field (f : ↥(Mean G n)) (x : Site n) : lap (field f.val) x = -f.val x := by
  have one (y : Site n) :
      lap (fun z => pole z y • f.val y) x=lap (fun z => pole z y) x • f.val y := by
    unfold lap
    rw [Finset.sum_smul]
    apply sum_congr rfl
    intro i _
    simp only [two_smul,add_smul,sub_smul]
  have total : lap (field f.val) x=∑ y, lap (fun z => pole z y • f.val y) x := by
    unfold field lap
    simp_rw [two_smul,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    exact Finset.sum_comm
  rw [total]
  simp_rw [one,lap_pole,add_smul,neg_smul,ite_smul,one_smul,zero_smul]
  rw [Finset.sum_add_distrib,←Finset.smul_sum,sumM,smul_zero,add_zero,Finset.sum_neg_distrib]
  simp

theorem field_even (f : ↥(Mean G n)) (x : Site n) : field f.val (-x)=field f.val x := by
  have fe : ∀ y, f.val (-y)=f.val y := (show _ ∧ _ from f.property).1
  unfold field
  rw [←Equiv.sum_comp (Equiv.neg (Site n)) (fun y => pole (-x) y • f.val y)]
  apply sum_congr rfl
  intro y _
  change green (-x-(-y)) • f.val (-y)=green (x-y) • f.val y
  rw [show -x-(-y)=-(x-y) by abel,even,fe]

def based (f : ↥(Mean G n)) : ↥(Pert.Orb.Zero G n) :=
  ⟨fun x => field f.val x-field f.val 0,⟨fun x => congrArg (·-field f.val 0) (field_even f x),
    by change field f.val 0-field f.val 0=0; exact sub_self _⟩⟩

theorem solved (f : ↥(Mean G n)) : (bridgeEquiv G n).symm f=based f := by
  apply (bridgeEquiv G n).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  funext x
  change f.val x=divB (grad (fun x => field f.val x-field f.val 0)) x
  rw [show divB (grad (fun x => field f.val x-field f.val 0)) x= -lap (field f.val) x by
    unfold divB grad lap
    rw [←Finset.sum_neg_distrib]
    apply sum_congr rfl
    intro i _
    simp only [sub_add_cancel,two_smul]
    abel]
  rw [lap_field,neg_neg]

/-- The even image and the anchored term on a genuine responded mean source. -/
theorem original (f : ↥(Mean G n)) (x : Site n) :
    ((bridgeEquiv G n).symm f).val x =
      ∑ y, ((green (x-y)+green (x+y))/2-green y) • f.val y := by
  have fe : ∀ y, f.val (-y)=f.val y := (show _ ∧ _ from f.property).1
  have mirror : (∑ y, green (x+y) • f.val y)=field f.val x := by
    rw [←Equiv.sum_comp (Equiv.neg (Site n)) (fun y => green (x+y) • f.val y)]
    apply sum_congr rfl
    intro y _
    change green (x+(-y)) • f.val (-y)=green (x-y) • f.val y
    rw [←sub_eq_add_neg,fe]
  rw [solved]
  change field f.val x-field f.val 0=_
  have pin : field f.val 0=∑ y, green y • f.val y := by simp [field,pole,even]
  rw [pin]
  simp_rw [sub_smul,Finset.sum_sub_distrib,add_div,add_smul,div_eq_mul_inv,mul_comm _ (2:ℝ)⁻¹,mul_smul]
  rw [Finset.sum_add_distrib,←Finset.smul_sum,←Finset.smul_sum,mirror]
  change field f.val x-_= (2:ℝ)⁻¹ • field f.val x+(2:ℝ)⁻¹ • field f.val x-_
  rw [←add_smul,show (2:ℝ)⁻¹+2⁻¹=1 by norm_num,one_smul]

end YM.Integration.WilsonPositionProgramTrialBasedGhost
