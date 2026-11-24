import YM.Integration.WilsonPosteriorProjectionBank
import YM.Integration.WilsonPosteriorProjectionWire
import YM.Next.FOUNDATIONS.LinkBounds
import YM.MSbar.Rolling.Skirt

/-! The original full prescribed holonomy in the actual moving coarse chart.
The component price uses the torus distance from its own root, at every
link, including the period cut. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionTestGrowth

open Set Function Filter Finset Lattice Wilson RG Source Labels Next.Foundations Precision Tree Exterior
open MSbar.Cacao MSbar.Rolling Push.Uniform WilsonPosteriorProjectionWire
open WilsonPosteriorProjectionRay
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

def screen (G : Gauge) (n : Side) (g : ℝ) : Directions G n →L[ℝ] Positions (Primary n G) :=
  g⁻¹ • (photograph (G:=G) (c:=n)).toContinuousLinearMap

def curve (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) (g : ℝ) :=
  screen G n g ∘ testLog H d o J

theorem regular (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) (g : ℝ) :
    ContDiffAt ℝ ω (curve H d o J g) 0 :=
  (screen G n g).contDiff.contDiffAt.comp 0 (testLog_diff H d o J)

theorem center (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) (g : ℝ) :
    curve H d o J g 0 = 0 := by simp only [curve,comp_apply,testLog_zero,map_zero]

theorem physical (H : Hol G) (d : ℕ) (o : Site n) (J : Jet G) {g : ℝ} (hg : g ≠ 0) :
    H.testLinks d o J =ᶠ[𝓝 0] postcard G n g ∘ curve H d o J g := by
  filter_upwards [increment_testLog H d o J] with t read
  rw [read]
  change increment 1 (testLog H d o J t) =
    represent (tint G _ (g • (g⁻¹ • display (testLog H d o J t))))
  rw [smul_smul,mul_inv_cancel₀ hg,one_smul]
  simpa only [one_smul,direction_display] using
    (field (G:=G) (c:=n) 1 1 (display (testLog H d o J t))).symm

theorem ray (H : Hol G) (d k : ℕ) (o : Site n) (J : Jet G) (g : ℝ) :
    iteratedDeriv k (curve H d o J g) 0 = screen G n g (iteratedDeriv k (testLog H d o J) 0) := by
  unfold curve iteratedDeriv
  rw [(screen G n g).iteratedFDeriv_comp_left (testLog_diff H d o J) le_top]
  rfl

/-- The spatial constant precedes the volume, source position, fitted
amplitude, thermal coupling, and primary coordinate. -/
theorem spatial (H : Hol G) (d k : ℕ) (J : Jet G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : Side) (o : Site n) (g θ : ℝ),
      0 < g → 0 ≤ θ → θ ≤ 1 → ∀ a : Primary n G,
      |iteratedDeriv k (curve H d o (θ • J) g) 0 a| ≤
        g⁻¹ * (C*θ*(1+(separation a.1.1 o : ℝ))^(k-1)) := by
  obtain ⟨C,pos,price⟩ := testLog_bound H d k J
  refine ⟨C,pos,?_⟩
  intro n o g θ hg hθ θ1 a
  rw [ray]
  change |g⁻¹ * ((iteratedDeriv k (testLog H d o (θ • J)) 0 ⟨a.1.1,axisEquiv.symm a.1.2⟩) a.2)| ≤ _
  rw [abs_mul,abs_of_pos (inv_pos.mpr hg)]
  apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr hg).le
  apply le_trans _ (price n o ⟨a.1.1,axisEquiv.symm a.1.2⟩ θ hθ θ1)
  exact (Real.norm_eq_abs _).symm.le.trans (PiLp.norm_apply_le _ _)

end YM.Integration.WilsonPosteriorProjectionTestGrowth
end

