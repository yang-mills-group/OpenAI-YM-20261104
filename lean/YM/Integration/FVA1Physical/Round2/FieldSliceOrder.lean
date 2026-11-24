import YM.Integration.FVA1Physical.Round2.FieldChartOrder

/-! Restricting to the bonds in one derivative test leaves every other bond
at its true base value. Translating the test point incurs no derivative cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson MSbar MSbar.Rolling MSbar.Bulk
open MSbar.Midpoint MSbar.Wave Push.Local Push.Uniform AnalyticBridge.SectorAffine.Offset
open scoped Classical Topology ContDiff
variable {σ : Type} [Fintype σ] {G : Gauge} {c f : Side}

theorem projection_contract (K : Finset σ) : ‖coordinateProjection K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  by_cases h:i∈K
  · simpa [coordinateProjection,h] using norm_le_pi_norm w i
  · simp [coordinateProjection,h]

theorem projection_held (K : Finset (Primary c G)) (w : Positions (Primary c G))
    (e : Edge (Site c)) (off : e∉K.image physicalBond) : panel G c (coordinateProjection K w) e = 0 := by
  ext a
  have h : primary e a ∉ K := fun inside=>off (physicalBond_primary e a ▸ mem_image_of_mem physicalBond inside)
  change (coordinateProjection K w) (primary e a)=0
  simp [coordinateProjection,h]

theorem translate_through {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} {f : E→ℝ} {z : E} {B : ℝ} (h : Through k (fun y=>f (z+y)) 0 B) :
    Through k f z B := by
  have hz : ContDiffAt ℝ k (fun y=>f (z+y)) (z-z) := by simpa only [sub_self] using h.smooth
  have smooth:=hz.comp (f:=fun y:E=>y-z) z (contDiffAt_id.sub contDiffAt_const)
  have eqn : (fun y=>f (z+y)) ∘ (fun y:E=>y-z) = f := funext fun y=> by
    change f (z+(y-z))=f y
    rw [add_comm z,sub_add_cancel]
  refine ⟨eqn ▸ smooth,fun i hi=>?_⟩
  simpa only [iteratedFDeriv_comp_add_left,add_zero] using h.pay i hi

theorem affine_chart_bound {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ} {F : E→ℝ} (P : X→L[ℝ] E)
    (thin : ‖P‖≤1) (b : E) (z : X) {B : ℝ} (paid : Through k F (b+P z) B) :
    Through k (fun w=>F (b+P w)) z B := by
  let h:=fun t=>F (b+t)
  have sm : ContDiffAt ℝ k h (P z) := paid.smooth.comp _ (contDiffAt_const.add contDiffAt_id)
  refine ⟨sm.comp z P.contDiff.contDiffAt,fun i hi=>?_⟩
  change ‖iteratedFDeriv ℝ i (h ∘ P) z‖≤B
  rw [iter_lin_at (sm.of_le (Nat.cast_le.mpr hi))]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  apply (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) thin)).trans
  simpa only [h,iteratedFDeriv_comp_add_left] using paid.pay i hi

theorem physical_slice_at (S : StepData c f) (R : Rep G f) (φ : Config G f → ℝ)
    (branch : S.patch.Branches S.kernel G) (vac : Envelope R.eval) (pos : ∀ U, 0<R.eval U)
    (field : Envelope φ) {a : ℝ} (cap : ∀ U, |φ U|≤a) (K : Finset (Primary c G))
    (g : ℝ) (unit : |g|≤1) (b z : Positions (Primary c G))
    (hz : ‖g•(b+coordinateProjection K z)‖≤1) (k : ℕ) :
    Through k (fun w=>expect S R (postcard G c g (b+coordinateProjection K w)) φ) z
      (chartOrderPrice G (R.beta*S.kernel.penalty) k (K.image physicalBond).card a) := by
  let P:=coordinateProjection K
  let X:=K.image physicalBond
  have atZero:=reading_chart_order S R φ branch vac pos field cap X P (projection_contract K)
    (projection_held K) g unit (b+P z) hz k
  apply translate_through
  simpa only [map_add,add_assoc] using atZero

end YM.Integration.FVA1Physical.Round2.Curvature
