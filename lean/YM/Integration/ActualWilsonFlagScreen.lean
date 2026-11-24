import YM.Integration.ActualWilsonPunctureReserve

/-! Pointwise exterior-flag attenuation of the original reweighted Wilson readout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonFlagScreen
open Function Finset Lattice Wilson RG Extra.Histories SectorNext.Vacuum Push.AbsoluteSums ActualWilsonPacketSplit
open Marker Source Labels RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained Comparison.RG02 PhysicalNext.Repeat.Legato
open ActualWilsonAxisSpectator
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem charged (W : Rep G n) (Q : BudgetPoint) {w : ℝ} (hw : w≤1) (H : W.activities.KBound W.p w)
    (hB : Q.B=W.p.B) (hQ : 2*W.p.supportExponent≤Q.supportExponent) (j : ℕ) (U : Config G n) (y : ℂ) :
    let F := flags W.p.threshold U
    let T := scopes W j
    W.p.mass T ‖y*dressed W j U‖ ≤ Real.exp (-flagRate W.p*F.card)*Q.mass T ‖y‖ := by
  intro F T
  let r := flagRate W.p
  let D := F \ T
  let I := F ∩ T
  have hd : ‖dressed W j U‖ ≤ Real.exp (-r*D.card) := by
    apply (ActualWilsonExteriorSpectator.minor W hw H j U).trans
    have h : (if D=∅ then (1:ℝ) else w)≤1 := by split <;> first | exact le_rfl | exact hw
    exact (mul_le_mul_of_nonneg_right h (Real.exp_pos _).le).trans_eq (one_mul _)
  have hc : (D.card : ℝ)+I.card=F.card := by exact_mod_cast Finset.card_sdiff_add_card_inter F T
  have he : Real.exp (-r*D.card)=Real.exp (-r*F.card)*Real.exp (r*I.card) := by
    rw [←Real.exp_add]
    congr 1
    linear_combination -r*hc
  calc
    _ ≤ W.p.mass T (‖y‖*Real.exp (-r*D.card)) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) (Real.exp_pos _).le
    _ = Real.exp (-r*F.card)*W.p.mass T ‖(Real.exp (r*I.card):ℂ)*y‖ := by
      rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      unfold BudgetPoint.mass
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ActualWilsonPunctureReserve.reserve W.p Q hB hQ F T y) (Real.exp_pos _).le

theorem rows (X W : Rep G n) (Q : BudgetPoint) {w : ℝ} (hw : w≤1)
    (HX : X.activities.KBound X.p w) (HW : W.activities.KBound W.p w) (hp : W.p=X.p)
    (e : ℕ → ℕ) (hd : ∀ j,scopes W (e j)=scopes X j)
    (hB : Q.B=X.p.B) (hQ : 2*X.p.supportExponent≤Q.supportExponent) (U : Config G n) (y : ℕ → ℂ)
    {q : ℝ} (H : SumBudget (fun j => Q.mass (scopes X j) ‖y j‖) q) :
    let t := Real.exp (X.exponent U-W.exponent U)
    let r := Real.exp (-flagRate X.p*(flags X.p.threshold U).card)
    let f j := y j*((t:ℂ)*dressed X j U-dressed W (e j) U)
    SumBudget (fun j => X.p.mass (scopes X j) ‖f j‖) ((t+1)*r*q) := by
  intro t r f
  have ht : 0≤t := (Real.exp_pos _).le
  have hr : 0≤r := (Real.exp_pos _).le
  apply budget_mono (budget_scale (x := (t+1)*r) (mul_nonneg (add_nonneg ht zero_le_one) hr) H)
  · exact fun j => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  intro j
  let T := scopes X j
  let a := y j*dressed X j U
  let b := y j*dressed W (e j) U
  have ha : X.p.mass T ‖a‖≤r*Q.mass T ‖y j‖ := charged X Q hw HX hB hQ j U (y j)
  have hB' : Q.B=W.p.B := hp.symm ▸ hB
  have hQ' : 2*W.p.supportExponent≤Q.supportExponent := hp.symm ▸ hQ
  have hb' := charged W Q hw HW hB' hQ' (e j) U (y j)
  rw [hp,hd j] at hb'
  have hb : X.p.mass T ‖b‖≤r*Q.mass T ‖y j‖ := hb'
  have hf : f j=(t:ℂ)*a-b := by dsimp only [f,a,b];ring
  have hf' : ‖f j‖≤t*‖a‖+‖b‖ := by
    rw [hf]
    apply (norm_sub_le _ _).trans_eq
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  calc
    _ ≤ X.p.mass T (t*‖a‖+‖b‖) := mul_le_mul_of_nonneg_left hf' (Real.exp_pos _).le
    _ = t*X.p.mass T ‖a‖+X.p.mass T ‖b‖ := by unfold BudgetPoint.mass;ring
    _ ≤ t*(r*Q.mass T ‖y j‖)+r*Q.mass T ‖y j‖ := add_le_add (mul_le_mul_of_nonneg_left ha ht) hb
    _ = _ := by ring

end YM.Integration.ActualWilsonFlagScreen
