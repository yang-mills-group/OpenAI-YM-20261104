import YM.Integration.QLocalPhysicalBirthPurchase
import YM.Integration.WilsonOriginalOPEPageMenu

/-! Restore the actual finite atomic radii and rescale a true site invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedOPEPriceChange
open Finset Lattice Wilson RG Source Labels Marker FVA1 MergeProof MergeProof.Accent MergeProof.Replicums
open Extra.Trajectories Push.GridApprox.Nil Push.AbsoluteSums Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {n : Side} {I W : Type} [Fintype I] [DecidableEq W] [Fintype W]

theorem scaled (X : I→Support n) (B : ℕ) (f g : I→ℝ) (σ b h : ℝ)
    (hh : 0≤h) (hg : ∀i,0≤g i) (bound : ∀i,g i≤h*f i) (funded : Ac.Hit X B f σ b) :
    Ac.Hit X B g σ (h*b) := by
  intro x
  have paid := (funded x).2.2
  rw [tsum_fintype] at paid
  refine ⟨fun i=>ite_nonneg (mul_nonneg (hg i) (Real.exp_nonneg _)) le_rfl,Summable.of_finite,?_⟩
  rw [tsum_fintype]
  apply le_trans _ (mul_le_mul_of_nonneg_left paid hh)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases atSite : x∈X i
  · simp only [if_pos atSite]
    rw [←mul_assoc]
    exact mul_le_mul_of_nonneg_right (bound i) (Real.exp_nonneg _)
  · simp only [if_neg atSite,mul_zero,le_refl]

variable {G : Gauge} {P : Rep G n} {Γ : Census W}

def restore (ρ : ℝ) : ℝ := (max 1 ρ⁻¹)^(Fintype.card W)

theorem restored (q : I→Page Γ P) (o : Positions W n) (v : I→ℝ) (ρ : ℝ) (hρ : 0<ρ)
    {b : ℝ} (safe : MenuSafe q o v (fun _=>ρ) b) :
    MenuSafe q o v (fun _=>1) (restore (W:=W) ρ*b) := by
  let C := restore (W:=W) ρ
  have hC : 0≤C := pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  refine ⟨safe.each,fun _=>zero_lt_one,scaled _ _ _ _ _ _ C hC ?_ ?_ safe.hit⟩
  · intro i
    exact mul_nonneg (mul_nonneg (Poly.worth (fun _=>zero_lt_one) _).le (norm_nonneg _)) (Page.nonneg _ (safe.each i))
  · intro i
    let e := (q i).s.val.card
    have small : (ρ^e)⁻¹≤C := by
      rw [←inv_pow]
      exact (pow_le_pow_left₀ (inv_nonneg.mpr hρ.le) (le_max_right 1 ρ⁻¹) _).trans
        (pow_le_pow_right₀ (le_max_left 1 ρ⁻¹) (Finset.card_le_univ _))
    have prior : 1≤C*ρ^e := by
      calc 1 = (ρ^e)⁻¹*ρ^e := (inv_mul_cancel₀ (pow_ne_zero _ hρ.ne')).symm
           _ ≤ C*ρ^e := mul_le_mul_of_nonneg_right small (pow_nonneg hρ.le _)
    have base := mul_nonneg (norm_nonneg (q i).chip) (Page.nonneg _ (safe.each i))
    simpa [Page.due,Poly.toll,e,mul_assoc] using (mul_le_mul_of_nonneg_right prior base)

end YM.Integration.WilsonRootedOPEPriceChange
