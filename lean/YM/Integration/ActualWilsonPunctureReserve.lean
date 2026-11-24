import YM.Integration.ActualWilsonExteriorSpectator

/-! Pay the flags inside each puncture with its requested support reserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonPunctureReserve
open Function Finset Lattice Wilson RG Extra.Histories SectorNext.Vacuum Push.AbsoluteSums ActualWilsonPacketSplit
open Marker Source Labels RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained Comparison.RG02 PhysicalNext.Repeat.Legato
open ActualWilsonAxisSpectator
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem reserve (P Q : BudgetPoint) (hB : Q.B=P.B) (hq : 2*P.supportExponent ≤ Q.supportExponent)
    (F T : Support n) (y : ℂ) :
    P.mass T ‖(Real.exp (flagRate P*(F ∩ T).card):ℂ)*y‖ ≤ Q.mass T ‖y‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  unfold BudgetPoint.mass
  rw [hB,←mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  apply Real.exp_le_exp.mpr
  have h := inventory_pay P (Finset.inter_subset_right (s₁ := F) (s₂ := T))
  have e := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (coverNumber P.B T): (0:ℝ) ≤ _)
  linarith

theorem cancel (P : BudgetPoint) (F T : Support n) :
    Real.exp (-flagRate P*F.card)*Real.exp (flagRate P*(F \ T).card)*Real.exp (flagRate P*(F ∩ T).card)=1 := by
  have h : ((F \ T).card:ℝ)+(F ∩ T).card=F.card := by exact_mod_cast Finset.card_sdiff_add_card_inter F T
  rw [←Real.exp_add,←Real.exp_add,←Real.exp_zero]
  congr 1
  rw [←h]
  ring

theorem paired (X W : Rep G n) (Q : BudgetPoint) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1)
    (HX : X.activities.KBound X.p w) (HW : W.activities.KBound W.p w)
    (e : ℕ → ℕ) (hp : W.p=X.p) (hd : ∀ j,scopes W (e j)=scopes X j)
    (hB : Q.B=X.p.B) (hq : 2*X.p.supportExponent ≤ Q.supportExponent)
    (U : Config G n) (y : ℕ → ℂ) {r : ℝ} (H : SumBudget (fun j => Q.mass (scopes X j) ‖y j‖) r) :
    let P := X.p
    let F := flags P.threshold U
    let f j := y j*((W.activities.gas W.p U:ℂ)*dressed X j U-(X.activities.gas X.p U:ℂ)*dressed W (e j) U)
    SumBudget (fun j => if (F \ scopes X j).Nonempty then P.mass (scopes X j) ‖f j‖ else 0)
      (2*w^2*Real.exp (-(2*flagRate P)*F.card)*r) := by
  intro P F f
  let T := scopes X
  let t := Real.exp (-flagRate P*F.card)
  let b j := Real.exp (flagRate P*(F ∩ T j).card)
  let g j := (b j:ℂ)*y j
  have Hg : SumBudget (fun j => P.mass (T j) ‖g j‖) r := budget_mono H
    (fun j => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (fun j => reserve P Q hB hq F (T j) (y j))
  have H' := ActualWilsonExteriorSpectator.paired X W hw0 hw HX HW e hp hd U g Hg
  have h := budget_scale (x := t) (Real.exp_pos _).le H'
  have he (j : ℕ) :
      t*(if (F \ T j).Nonempty then Real.exp (flagRate P*(F \ T j).card)*P.mass (T j)
        ‖g j*((W.activities.gas W.p U:ℂ)*dressed X j U-(X.activities.gas X.p U:ℂ)*dressed W (e j) U)‖ else 0)
        =(if (F \ T j).Nonempty then P.mass (T j) ‖f j‖ else 0) := by
    by_cases hj : (F \ T j).Nonempty
    · have hb : 0<b j := Real.exp_pos _
      simp only [if_pos hj,g,f,BudgetPoint.mass,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hb]
      have hc : t*Real.exp (flagRate P*(F \ T j).card)*b j=1 := cancel P F (T j)
      linear_combination Real.exp (P.supportExponent*coverNumber P.B (T j))*‖y j‖*
        ‖(W.activities.gas W.p U:ℂ)*dressed X j U-(X.activities.gas X.p U:ℂ)*dressed W (e j) U‖ * hc
    · simp only [if_neg hj,mul_zero]
  have hc : t*((2*w^2*Real.exp (-flagRate P*F.card))*r)=2*w^2*Real.exp (-(2*flagRate P)*F.card)*r := by
    have ht : t*Real.exp (-flagRate P*F.card)=Real.exp (-(2*flagRate P)*F.card) := by
      dsimp only [t]
      rw [←Real.exp_add]
      congr 1
      ring
    linear_combination 2*w^2*r*ht
  rw [←hc]
  exact (congrArg (fun q : ℕ→ℝ => SumBudget q (t*((2*w^2*Real.exp (-flagRate P*F.card))*r))) (funext he)).mp h

end YM.Integration.ActualWilsonPunctureReserve
