import YM.Integration.WilsonOriginalMicroscopicGuardedPosterior

/-! Restoring a canonical guarded column costs only its actual finite label
norm and the original date's common threshold. The latter is independent of
the ultraviolet cutoff and period at the time the column is submitted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicGuardedWallet
open Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Extra.Multi
open PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals
open WilsonOriginalMicroscopicGuardedTrial WilsonOriginalMicroscopicGuardedPosterior
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G)
local notation "F" d:max => R.family.labels.level d
local notation "S" d:max => R.family.localSection d
def loss (d K:ℕ):ℝ:=(1+BasisCost.price (S d))*
  (max 1 ((R.family.path.levels.budget K).threshold)⁻¹)^BasisCost.slots (F d)

theorem nonneg (d K:ℕ):0 ≤ loss R d K:=by
  unfold loss
  have h:0 ≤ BasisCost.price (S d):=zero_le_one.trans (BasisCost.price_pos _)
  exact mul_nonneg (by positivity) (pow_nonneg (zero_le_one.trans (le_max_left ..)) _)

theorem one (d:Fin 3→ℕ)(N p K:ℕ)(live:K ≤ N)(v:∀a:Fin 3,R.family.label (d a))(a:Fin 3):
    cap R d N p K v a ≤ loss R (d a) K*(F (d a)).coeffSize (v a):=by
  let W:=R.family.path.rep N p K
  let F₀:=(F (d a))
  let u:=v a
  let t:=max 1 W.p.threshold⁻¹
  let h:=t^BasisCost.slots F₀
  have tp:1 ≤ t:=le_max_left _ _
  have hp:1 ≤ h:=one_le_pow₀ tp
  have normed:=BasisCost.coeff_nonneg u
  have xp:0 ≤ BasisCost.price (S (d a)):=zero_le_one.trans (BasisCost.price_pos _)
  have base:F₀.coeffSize (F₀.scaled W.p.threshold⁻¹ (F₀.core u)) ≤ h*F₀.coeffSize u:=by
    apply LE.le.trans _ (mul_le_mul_of_nonneg_left (BasisCost.coeff_le u) (zero_le_one.trans hp))
    rw [Frame.coeffSize,Frame.coeffSize,mul_sum]
    apply sum_le_sum
    intro z hz
    rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr W.p.threshold_pos.le) _)]
    refine mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (inv_nonneg.mpr W.p.threshold_pos.le) (le_max_right (1:ℝ) W.p.threshold⁻¹) _).trans ?_) (norm_nonneg _)
    exact pow_le_pow_right₀ tp (Finset.le_sup (f:=fun i=>(F₀.grades i).2) hz)
  have scalar:‖u 0‖ ≤ h*F₀.coeffSize u:=(BasisCost.coord_le u 0).trans (le_mul_of_one_le_left normed hp)
  have fixed:W.p=R.family.path.levels.budget K:=(R.makes.wilson.represents N p K live).vac
  change ‖u 0‖+BasisCost.price (S (d a))*F₀.coeffSize (F₀.scaled W.p.threshold⁻¹ (F₀.core u)) ≤ _
  calc _ ≤ h*F₀.coeffSize u+BasisCost.price (S (d a))*(h*F₀.coeffSize u):=
      add_le_add scalar (mul_le_mul_of_nonneg_left base xp)
    _ = (1+BasisCost.price (S (d a)))*h*F₀.coeffSize u:=by ring
    _ = _:=by dsimp [loss,h,t,F₀,u];rw [fixed]

def invoice (d:Fin 3→ℕ)(K:ℕ)(M:Fin 3→ℝ)(s:Finset (Fin 3)):ℝ:=
  2*(∏a∈s,loss R (d a) K*M a)*(stencils R d s:ℝ)

theorem original (d:Fin 3→ℕ)(N p K:ℕ)(live:K ≤ N)(v:∀a:Fin 3,R.family.label (d a))
    (M:Fin 3→ℝ)(earned:∀a,(F (d a)).coeffSize (v a) ≤ M a)(s:Finset (Fin 3)):
    gross R d N p K v s*(stencils R d s:ℝ) ≤ invoice R d K M s:=by
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_left _ zero_le_two
  apply Finset.prod_le_prod
  · intro a _
    unfold cap
    exact add_nonneg (norm_nonneg _) (mul_nonneg (zero_le_one.trans (BasisCost.price_pos _)) (BasisCost.coeff_nonneg _))
  · intro a _
    exact (one R d N p K live v a).trans (mul_le_mul_of_nonneg_left (earned a) (nonneg R _ K))

end YM.Integration.WilsonOriginalMicroscopicGuardedWallet
end
