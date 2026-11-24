import YM.Integration.LocalComparisonInterface
import YM.Integration.ActualSignedCore

/-!
Exact normalization of a full represented qlocal output on the original
history. The source family and both represented layouts precede every test.
The chosen qlocal model factor is retained inside the additive error before
any linear signed compression. No equality to an older bank model is used.

These are transport identities, not an independent qlocal estimate. Actual
input preparation and the qlocal output supply the displayed exact step and
source/factorization equalities. The original Makes receipt supplies every
vacuum cancellation; no extra positivity or denominator bound is assumed.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualQlocalSignedTransport
open Function MeasureTheory Lattice Wilson RG Marker MergeProof MergeProof.Accent
open Extra.Trajectories OPE.Therm LocalComparison
open RG3.Script.Picnic
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {V : Type} [Fintype V] [DecidableEq V]
    {Γ : Census V} {N p j m : ℕ} {X : Type*}
    {Q : Carrier C N p (m + 1)} {Q' : Carrier C N p m}
    {o : V → Site (C.side (m + 1) p)} {o' : V → Site (C.side m p)}
    {input : Taste X o Q.rep Γ} {output : Taste X o' Q'.rep Γ}
    (step : ExactStep Q Q' o o' input output)

include step in
/-- One exact represented step preserves the complete original numerator,
including its quiet coefficient and all mixed marked coefficients. -/
theorem density_gust (hm : m < j)
    (source : X → Config G (C.side j p) → Poly Γ)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm) (x : X) :
    (output.leaf x).density = gust C.path N p j (source x) m hm.le := by
  calc
    (output.leaf x).density = actualPush C N p m ((input.leaf x).density) :=
      (step.density x).symm
    _ = actualPush C N p m (gust C.path N p j (source x) (m + 1) hm) :=
      congrArg (actualPush C N p m) (hInput x)
    _ = gust C.path N p j (source x) m hm.le :=
      (gust_step C.path N p j (source x) hm).symm

include step in
/-- The full actual numerator is divided by the very same coarse vacuum
as the represented output. The incoming fine vacuum is cancelled once. -/
theorem normalized_output (hC : C.Makes) (hj : j ≤ N) (hm : m < j)
    (source : X → Config G (C.side j p) → Poly Γ)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm) (x : X)
    (U : Config G (C.side m p)) :
    actualSignedTransport C (N := N) (source x) hm.le U =
      (Q'.rep.eval U)⁻¹ • (output.leaf x).density U := by
  rw [actualSignedTransport_eq C hC hj,
    density_gust step hm source hInput x, Q'.vacuum]

include step in
/-- Genuine original-law integrability follows from the original source,
without a global bound on the reciprocal vacuum. -/
theorem normalized_integrable (hC : C.Makes) (hj : j ≤ N) (hm : m < j)
    (source : X → Config G (C.side j p) → Poly Γ)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm)
    (x : X) (hSource : Integrable (source x) (prior G _)) :
    Integrable (fun U => (Q'.rep.eval U)⁻¹ • (output.leaf x).density U)
      (scene C.path N p m) := by
  have heq : actualSignedTransport C (N := N) (source x) hm.le =
      fun U => (Q'.rep.eval U)⁻¹ • (output.leaf x).density U :=
    funext (normalized_output step hC hj hm source hInput x)
  rw [← heq]
  exact actualSignedTransport_integrable C hC hj hSource hm.le

include step in
/-- Every marked coefficient has the original cutoff partition, even
when the qlocal representation is selected at an intermediate level. -/
theorem coefficient_mean (hC : C.Makes) (hj : j ≤ N) (hm : m < j)
    (source : X → Config G (C.side j p) → Poly Γ)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm)
    (x : X) (hSource : Integrable (source x) (prior G _)) (q : Γ.Mode) :
    (∫ U, ((Q'.rep.eval U)⁻¹ • (output.leaf x).density U).part q
      ∂scene C.path N p m) =
      (partition G (C.side N p) (C.path.β N p N))⁻¹ •
        ∫ U, (source x U).part q ∂prior G _ := by
  simp_rw [← normalized_output step hC hj hm source hInput x]
  exact actualSignedTransport_coefficient_mean C hC hj hSource hm.le q

/-- This is the full model-stripped residual, including its regular
logarithmic part and the entire forced gas. -/
def residualError (residual : Taste X o' Q'.rep Γ) (x : X)
    (U : Config G (C.side m p)) : Poly Γ :=
  (Q'.rep.eval U)⁻¹ • (residual.leaf x).density U - 1

include step in
/-- The additive transport defect keeps the chosen qlocal model factor.
The model-stripped residual alone is not the additive error. -/
theorem additive_defect (hC : C.Makes) (hj : j ≤ N) (hm : m < j)
    (source : X → Config G (C.side j p) → Poly Γ)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm)
    (residual : Taste X o' Q'.rep Γ)
    (model : X → Config G (C.side m p) → Poly Γ)
    (hFull : ∀ x U, (output.leaf x).density U =
      model x U * (residual.leaf x).density U)
    (x : X) (U : Config G (C.side m p)) :
    actualSignedTransport C (N := N) (source x) hm.le U - model x U =
      model x U * residualError residual x U := by
  rw [normalized_output step hC hj hm source hInput x U, hFull x U]
  simp only [residualError, mul_sub, mul_smul_comm, mul_one]

include step in
/-- Apply signed compression only to the complete polynomial. Any
remaining chosen-model versus prescribed-candidate difference is explicit;
no multiplicativity of the compression is asserted. -/
theorem linear_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hC : C.Makes) (hj : j ≤ N) (hm : m < j)
    (source : X → Config G (C.side j p) → Poly Γ)
    (hInput : ∀ x, (input.leaf x).density =
      gust C.path N p j (source x) (m + 1) hm)
    (residual : Taste X o' Q'.rep Γ)
    (model : X → Config G (C.side m p) → Poly Γ)
    (hFull : ∀ x U, (output.leaf x).density U =
      model x U * (residual.leaf x).density U)
    (L : Poly Γ →L[ℝ] E) (candidate : X → Config G (C.side m p) → E)
    (x : X) (U : Config G (C.side m p)) :
    L (actualSignedTransport C (N := N) (source x) hm.le U) - candidate x U =
      L (model x U * residualError residual x U) +
        (L (model x U) - candidate x U) := by
  have h := congrArg L (additive_defect step hC hj hm source hInput residual model hFull x U)
  rw [map_sub] at h
  rw [← h]
  abel


omit [Fintype V] in
/-- A genuine model numerator contains the original fine vacuum exactly
once. Its normalized signed transport is the actual Markov transport. -/
theorem model_transport {k : ℕ} (hC : C.Makes) (hj : j ≤ N)
    (model : Config G (C.side j p) → Poly Γ) (hk : k ≤ j) :
    actualSignedTransport C (N := N)
      (fun U => (C.path.rep N p j).eval U • model U) hk =
      actualTransport C (N := N) model hk := by
  funext U
  exact actualSignedTransport_eq C hC hj _ hk U

include step in
/-- Exact local additive error used by a finite transport telescope. The
input is the genuine model on the original full fine vacuum. All regular
and forced terms in the selected output residual remain in its error. -/
theorem model_step_defect (hC : C.Makes) (hm : m < N)
    (fineModel : X → Config G (C.side (m + 1) p) → Poly Γ)
    (hInput : ∀ x, (input.leaf x).density =
      fun U => Q.rep.eval U • fineModel x U)
    (residual : Taste X o' Q'.rep Γ)
    (model : X → Config G (C.side m p) → Poly Γ)
    (hFull : ∀ x U, (output.leaf x).density U =
      model x U * (residual.leaf x).density U)
    (x : X) (U : Config G (C.side m p)) :
    actualTransport C (N := N) (fineModel x) (Nat.le_succ m) U - model x U =
      model x U * residualError residual x U := by
  let source (x : X) (W : Config G (C.side (m + 1) p)) : Poly Γ :=
    (C.path.rep N p (m + 1)).eval W • fineModel x W
  have hSource : ∀ x, (input.leaf x).density =
      gust C.path N p (m + 1) (source x) (m + 1) (Nat.lt_succ_self m) := by
    intro x
    rw [gust_base]
    rw [hInput x]
    funext W
    rw [Q.vacuum]
  have h := additive_defect step hC hm (Nat.lt_succ_self m)
    source hSource residual model hFull x U
  change actualSignedTransport C (N := N)
    (fun W => (C.path.rep N p (m + 1)).eval W • fineModel x W)
    (Nat.le_succ m) U - model x U = _ at h
  rw [model_transport hC hm (fineModel x)] at h
  exact h

end YM.Integration.ActualQlocalSignedTransport
end
