import YM.Integration.LocalComparisonConstantFactor
import YM.Integration.JointSignedInitialization

/-! The complete field-constant caption factor commutes with the actual
linear push and every subsequent push of the same history. Integrability
of the full density transfers to its native residual by the exact inverse
caption. These identities do not identify a selected carrier with a history
row presentation, or license multiplicativity of any signed readout. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison
open Function MeasureTheory Lattice Wilson RG Marker MergeProof
open MergeProof.Accent RG3.Script.Picnic
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

private def captionMap (c : Poly R) : Poly R →L[ℂ] Poly R :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun z => c * z
       map_add' := fun x y => mul_add c x y
       map_smul' := fun a z => mul_smul_comm a c z } :
      Poly R →ₗ[ℂ] Poly R)

omit [Fintype V] in
private theorem push_caption {n k : Side} {S : StepData k n} {β : ℝ}
    (hS : S.IsKernel β G) (F : Config G n → Poly R)
    (hF : Integrable F (prior G n)) (c : Poly R) (U : Config G k) :
    S.push β (fun W => c * F W) U = c * S.push β F U := by
  have he := ((captionMap c).restrictScalars ℝ).integral_comp_comm
    (StepData.push_slice hS U F hF)
  change (∫ W, c * (S.density β W U • F W) ∂prior G n) =
    c * (∫ W, S.density β W U • F W ∂prior G n) at he
  simpa only [StepData.push, mul_smul_comm] using he

omit [Fintype V] in
private theorem gust_caption (H : History G) (N period : ℕ)
    (F : Config G (H.S.side N period) → Poly R)
    (hF : Integrable F (prior G (H.S.side N period))) (c : Poly R)
    {m : ℕ} (hm : m ≤ N) :
    gust H N period N (fun W => c * F W) m hm =
      fun U => c * gust H N period N F m hm U := by
  induction hm using Nat.decreasingInduction with
  | self => simp only [gust_base]
  | of_succ i hi ih =>
      rw [gust_step H N period N _ hi, ih]
      funext U
      rw [gust_step H N period N _ hi]
      exact push_caption
        (H.levels.transition_mass i period (H.β N period (i + 1)))
        _ (gust_live H N period N F hF hi) c U

variable {n : Side} {X : Type*} {P : Rep G n}
    {o : V → Site n} {T : Taste X o P R}
    {p : BudgetPoint} {w cost : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- The inverse of the complete constant caption transfers the genuine
full-density L1 receipt to the native residual, with the same full gas. -/
theorem RelativeBudget.nativeResidual_integrable
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (hI : Integrable (T.leaf x).density (prior G n)) :
    Integrable (nativeResidual T x) (prior G n) := by
  have he : nativeResidual T x = fun U =>
      Poly.pass (-(constantLog T x)) * (T.leaf x).density U := by
    funext U
    rw [h.density_constant_factor hc ht x U, ← mul_assoc,
      Next.Rank.Exponential.pass_neg _ (h.constantLog_quiet hc ht x), one_mul]
  rw [he]
  exact ((captionMap (Poly.pass (-(constantLog T x)))).restrictScalars ℝ).integrable_comp hI

/-- Every caption remains outside the actual transition integral as one
fixed polynomial factor. The complete residual is integrated first. -/
theorem RelativeBudget.density_push_constant_factor
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P.p.threshold)
    (x : X) (hI : Integrable (T.leaf x).density (prior G n))
    {k : Side} {S : StepData k n} {β : ℝ} (hS : S.IsKernel β G)
    (U : Config G k) :
    S.push β (T.leaf x).density U =
      Poly.pass (constantLog T x) * S.push β (nativeResidual T x) U := by
  have he : (T.leaf x).density =
      fun W => Poly.pass (constantLog T x) * nativeResidual T x W :=
    funext (h.density_constant_factor hc ht x)
  rw [he]
  exact push_caption hS _ (h.nativeResidual_integrable hc ht x hI) _ U

/-- The same complete caption commutes through every later push of this
history. No equality between the selected and historical row layouts is
inferred: the input is the literal supplied full density. -/
theorem RelativeBudget.density_gust_constant_factor
    (H : History G) (N period : ℕ)
    {P₀ : Rep G (H.S.side N period)}
    {o₀ : V → Site (H.S.side N period)} {T₀ : Taste X o₀ P₀ R}
    (h : RelativeBudget p T₀ w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hc : ∀ v, 0 < cost v) (ht : p.threshold = P₀.p.threshold)
    (x : X) (hI : Integrable (T₀.leaf x).density (prior G (H.S.side N period)))
    {m : ℕ} (hm : m ≤ N) :
    gust H N period N (T₀.leaf x).density m hm =
      fun U => Poly.pass (constantLog T₀ x) *
        gust H N period N (nativeResidual T₀ x) m hm U := by
  have he : (T₀.leaf x).density =
      fun W => Poly.pass (constantLog T₀ x) * nativeResidual T₀ x W :=
    funext (h.density_constant_factor hc ht x)
  rw [he]
  exact gust_caption H N period _ (h.nativeResidual_integrable hc ht x hI) _ hm

end YM.Integration.LocalComparison
end
