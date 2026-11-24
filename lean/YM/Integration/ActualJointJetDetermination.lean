import YM.Comparison.RG02.Assembly.Vertices
import Mathlib.Topology.ClusterPt

/-!
A homogeneous joint jet is determined by all unit-coupling slices.
This is algebraic: no analyticity or finite-dimensionality is assumed.
The compared jets have the same total order. Normalizing different marked
powers, and extracting these slices from prescribed ray coefficients, are
separate steps.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualJointJetDetermination
open Function Filter
open Comparison.RG02.Assembly
open scoped BigOperators Topology

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The literal factorial-normalized joint derivative is homogeneous. -/
theorem jet_smul (f : E → W) (n : ℕ) (s : ℝ) (x : E) :
    jet f n (s • x) = s ^ n • jet f n x := by
  unfold jet
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]
  rw [mul_comm]

private theorem jet_continuous (f : E → W) (n : ℕ) :
    Continuous (jet f n) :=
  continuous_const.smul ((iteratedFDeriv ℝ n f 0).cont.comp
    (continuous_pi fun _ => continuous_id))

/-- Values at every (1,A) determine the entire joint homogeneous jet,
including the zero-coupling hyperplane by continuity. -/
theorem jet_eq_of_unit_slice (f g : ℝ × E → W) (n : ℕ)
    (h : ∀ A : E, jet f n (1, A) = jet g n (1, A)) :
    ∀ z : ℝ × E, jet f n z = jet g n z := by
  have hnonzero (s : ℝ) (hs : s ≠ 0) (A : E) :
      jet f n (s, A) = jet g n (s, A) := by
    have hx : s • ((1 : ℝ), s⁻¹ • A) = (s, A) := by
      apply Prod.ext
      · change s * 1 = s
        exact mul_one s
      · change s • (s⁻¹ • A) = A
        rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
    calc
      jet f n (s, A) = s ^ n • jet f n (1, s⁻¹ • A) := by
        rw [← hx, jet_smul]
      _ = s ^ n • jet g n (1, s⁻¹ • A) :=
        congrArg (fun v : W => s ^ n • v) (h (s⁻¹ • A))
      _ = jet g n (s, A) := by rw [← hx, jet_smul]
  intro z
  have hf : Continuous (fun s : ℝ => jet f n (s, z.2)) :=
    (jet_continuous f n).comp (continuous_id.prodMk continuous_const)
  have hg : Continuous (fun s : ℝ => jet g n (s, z.2)) :=
    (jet_continuous g n).comp (continuous_id.prodMk continuous_const)
  have he := Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hf hg
    (fun s hs => hnonzero s (by simpa only [Set.mem_compl_iff,
      Set.mem_singleton_iff] using hs) z.2)
  exact congrFun he z.1

end YM.Integration.ActualJointJetDetermination
end
