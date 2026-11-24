import YM.RGComparison.Core16.Germ
import YM.PertExtension.PTBills
/-!
# The path conditional Gaussian is nondegenerate

Includes tag-independent jets and positivity though `d=Descent.nil` (empty integration) or no
color directions. A period-independent ℓ∞ gap constant (for the same patch parameters / finite
number of steps). Proved on the real germ using the nonlinear bound, not by taking Wick mean as an
axiom.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16.Descent
open Lattice RG Tree Wilson Push.BetaTransport Precision
open Function Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open PertExtension PertExtension.Series Tested Radial
variable {G : Gauge} {n c : Side}

def phase (G : Gauge) (d : Descent n c) (t : d.Tags) : Coordinates G d → ℝ :=
  d.action t 1 ∘ d.tablePath

instance tagNonempty (d : Descent n c) : Nonempty d.Tags := by
  induction d with
  | nil => exact ⟨()⟩
  | push S T d ih =>
    obtain ⟨x⟩ := ih
    exact ⟨(Classical.arbitrary S.Choices, x)⟩

variable {d : Descent n c} (h : d.OK G) (t u : d.Tags)
include h
lemma phase_zero : d.phase G t 0 = 0 := by simp [phase,tablePath_zero,action, account_flat h]

lemma account_smooth (β : ℕ → ℝ) :
    ContDiffAt ℝ ω (fun x : Coordinates G d => d.account β t 1 (d.tablePath x)) 0 := by
  simpa only [link_one] using branch_smooth (v := fun x : Coordinates G d => x) (Bg := fun _ => 0)
    h contDiffAt_id rfl contDiffAt_const rfl t β

lemma stationary : Stationary (d.phase G t) := by
  have hs : ContDiffAt ℝ ∞ (d.phase G t) 0 := (account_smooth h t 1).of_le le_top
  refine ⟨hs, phase_zero h t, fun x => ?_⟩
  rw [homogeneous_derivative _ _ _ (hs.of_le (by simp)),iteratedDeriv_one]
  have hp : IsLocalMin (fun r : ℝ => d.phase G t (r • x)) 0 := Eventually.of_forall (fun a => by
    dsimp only; rw [zero_smul,phase_zero h]; exact action_nonneg ..)
  rw [hp.deriv_eq_zero, mul_zero]

lemma phase_branch : d.phase G t =ᶠ[𝓝 0] d.phase G u := by
  have he := branch_independent (v := fun x : Coordinates G d => x) (Bg := fun _ => 0) h contDiffAt_id rfl t u 1
  simp only [link_one] at he; exact he

lemma phase_jet (k : ℕ) : jet (d.phase G t) k = jet (d.phase G u) k := by
  funext x; unfold jet; rw [((phase_branch h t u).iteratedFDeriv ℝ k).eq_of_nhds]

lemma prob_flat_tangent : ∀ᶠ v : Coordinates G d in 𝓝 0,
    d.probability t (d.tablePath v) = (Fintype.card d.Tags : ℝ)⁻¹ :=
  branch_uniform h (v := id) contDiffAt_id rfl t
lemma apices (v : Coordinates G d) : Tendsto (fun r : ℝ => (r⁻¹)^2*d.phase G t (r • v))
    Tested.germ (𝓝 (jet (d.phase G t) 2 v)) := by
  let φ := d.phase G t; have hF := stationary h t; let f := fun r : ℝ => φ (r • v)
  have hv := directions hF.smooth v
  have hx (i) (hi : i < 2) : jet φ i v = 0 := by
    interval_cases i
    · rw [jet_zero]; exact hF.base0
    exact hF.base1 v
  exact (hv.shift hx).tendsto_first

lemma jet_nonneg (x : Coordinates G d) : 0 ≤ jet (d.phase G t) 2 x := by
  exact ge_of_tendsto (apices h t x) (Eventually.of_forall fun r => mul_nonneg (sq_nonneg _) (action_nonneg ..))

omit h
private lemma in_color (v : G.Color) :
    Tendsto (fun r : ℝ => ‖r‖⁻¹ * G.chord (G.lieExp (r • v))) (𝓝[≠] 0) (𝓝 ‖v‖) := by
  apply Work.F01.chord_limit (G := G) (U := fun r : ℝ => G.lieExp (r • v)) _ _
  · rw [zero_smul]; exact G.mat_lieExp_zero
  have h : HasFDerivAt (fun x => G.mat (G.lieExp x)) (G.colorMat.toContinuousLinearMap) ((0:ℝ) • v) := by rw [zero_smul]; exact G.expDiff_zero
  have he : HasDerivAt (fun r : ℝ => r • v) v 0 := by simpa using! (hasDerivAt_id' (0:ℝ)).smul_const v
  exact h.comp_hasDerivAt (0:ℝ) he

private lemma scaled_bound (h : d.Room G) (t : d.Tags) (j : d.Links) (x : Coordinates G d) :
    ‖x j‖^2 ≤ (d.edgeBill G)^2 * jet (d.phase G t) 2 x := by
  have hz := room_ok d h
  have he : Tested.germ ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun r hr => ne_of_gt (show 0<r from hr))
  apply le_of_tendsto_of_tendsto ((in_color (x j)).pow 2 |>.mono_left he)
    ((apices hz t x).const_mul ((d.edgeBill G)^2))
  · -- all tags on this very trajectory are positive near the flat path
    have hx : Tendsto (fun r : ℝ => r • x) Tested.germ (𝓝 0) := by
      simpa only [zero_smul] using (((show Continuous fun r : ℝ => r • x from by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds)
    filter_upwards [hx.eventually (prob_flat_tangent hz t), Tested.eventually_pos] with r hr hp
    let a := d.tablePath (r • x); have he : 0 < d.probability t a := by
      unfold a; rw [hr]; exact inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr inferInstance))
    have hf := pow_le_pow_left₀ (G.chord_nonneg _) (from_flat h he j) 2
    rw [mul_pow, Real.sq_sqrt (action_nonneg ..)] at hf
    rw [mul_pow]; have hi := mul_le_mul_of_nonneg_left hf (sq_nonneg (r⁻¹))
    change ‖r‖⁻¹ ^ 2 * G.chord (a j)^2 ≤ (d.edgeBill G)^2 * ((r⁻¹)^2 * d.action t 1 a)
    rw [Real.norm_eq_abs, abs_of_pos hp]; exact hi.trans_eq (mul_left_comm ..)


/-- Native kernel quadratic jet. Quantitative mass of an off-flat history fluctuation. -/
lemma coercive_charge (h : d.Room G) (x : Coordinates G d) :
    (1 + d.edgeBill G)⁻¹ ^ 2 * ‖x‖^2 ≤ jet (d.phase G t) 2 x := by
  let M := jet (d.phase G t) 2 x
  let E := d.edgeBill G; have hp := jet_nonneg (room_ok d h) t x; have hb := edgeBill_nonneg G d
  have hv : ‖x‖ ≤ E * Real.sqrt M := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hb (Real.sqrt_nonneg _))).mpr; intro i
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hb (Real.sqrt_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hp]; exact scaled_bound h t i x
  let Z := 1+E; have h₁ : E ≤ Z := by unfold Z; linarith
  have h₂ : 0 < Z := by unfold Z E; linarith
  have hf : ‖x‖^2 ≤ (Z*Real.sqrt M)^2 := pow_le_pow_left₀ (norm_nonneg _) (hv.trans (by gcongr)) 2
  rw [mul_pow, Real.sq_sqrt hp] at hf
  change Z⁻¹^2 * _ ≤ M
  rw [inv_pow]; exact (mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ (Z^2)⁻¹)).trans_eq (inv_mul_cancel_left₀ (pow_pos h₂ 2).ne' _)

end YM.RGComparison.Core16.Descent
