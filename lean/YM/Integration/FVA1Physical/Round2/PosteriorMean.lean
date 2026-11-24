import YM.Integration.FVA1Physical.Marked.PosteriorFlag
import YM.Integration.FVA1Physical.Round2.MeasuredMeanJets

/-! The physical mass of a nonuniform incoming error is conserved by the
posterior averaging of its norm. This gives a contraction for genuine
complex mixed-source errors on the selected interacting history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open MeasureTheory Filter Lattice RG YM.Wilson OPE.Therm
open scoped BigOperators Classical
variable {G : Gauge} (A : History G) (sel : A.Selected) {N n m : ℕ} (hm : m < N)
local notation "Fine" => Config G (A.S.side (m+1) n)
local notation "Coarse" => Config G (A.S.side m n)
local notation "op" => A.levels.clock.op m n
local notation "β" => A.β N n (m+1)
local notation "inD" => RG.Rep.eval (A.rep N n (m+1))
local notation "outD" => RG.Rep.eval (A.rep N n m)

include sel hm in
theorem posterior_mean (f : Fine → ℝ) (hf : Envelope f) :
    (∫ v, conditionalPush A N n m f v ∂scene A N n m) =
      ∫ u, f u ∂scene A N n (m+1) := by
  let Z := partition G (A.S.side N n) (A.β N n N)
  have integr := (((A.rep N n (m+1)).envelope (sel.represents N n (m+1) hm).good).mul hf).integrable
    (prior G (A.S.side (m+1) n))
  have clear (v : Coarse) : outD v * conditionalPush A N n m f v =
      (op).push β (fun u => inD u*f u) v := by
    unfold conditionalPush
    simp only [smul_eq_mul,←mul_assoc,mul_inv_cancel₀ (SectorNext.Vacuum.strictly A sel N n m hm.le v).ne',one_mul]
  calc
    _ = (∫ v, outD v * conditionalPush A N n m f v ∂prior G (A.S.side m n))/Z := scenery sel hm.le _
    _ = (∫ u, inD u*f u ∂prior G (A.S.side (m+1) n))/Z := by
      simp_rw [clear]
      rw [StepData.push_integral (A.levels.transition_mass m n β) _ integr]
    _ = _ := (scenery sel hm f).symm

private theorem norm_envelope {X : Type*} [MeasurableSpace X] {F : X → ℂ} (h : Envelope F) :
    Envelope (fun u=>‖F u‖) :=
  ⟨h.meas.norm,by obtain ⟨C,hC⟩ := h.cost; exact ⟨C,fun u=>by simpa using hC u⟩⟩

include sel hm in
theorem posterior_envelope_complex (F : Fine→ℂ) (hF : Envelope F) :
    Envelope (conditionalPush A N n m F) := by
  have K := A.levels.transition_mass m n β
  have w := (A.rep N n (m+1)).envelope (sel.represents N n (m+1) hm).good
  have z := (A.rep N n m).envelope (sel.represents N n m hm.le).good
  have joint : Measurable (fun v : Fine × Coarse => (op).density β v.1 v.2 • (inD v.1 • F v.1)) :=
    K.meas.smul ((w.meas.smul hF.meas).comp measurable_fst)
  obtain ⟨C,hC⟩ := hF.cost
  exact ⟨z.meas.inv.smul joint.stronglyMeasurable.integral_prod_left'.measurable,
    C,conditionalPush_bound A sel N n m hm F C hC⟩

include sel hm in
theorem posterior_envelope_real (f : Fine→ℝ) (hf : Envelope f) :
    Envelope (conditionalPush A N n m f) := by
  have K := A.levels.transition_mass m n β
  have w := (A.rep N n (m+1)).envelope (sel.represents N n (m+1) hm).good
  have z := (A.rep N n m).envelope (sel.represents N n m hm.le).good
  have joint : Measurable (fun v : Fine × Coarse => (op).density β v.1 v.2 * (inD v.1 * f v.1)) :=
    K.meas.mul ((w.meas.mul hf.meas).comp measurable_fst)
  obtain ⟨C,hC⟩ := hf.cost
  exact ⟨z.meas.inv.mul joint.stronglyMeasurable.integral_prod_left'.measurable,
    C,conditionalPush_bound A sel N n m hm f C hC⟩

include sel hm in
theorem posterior_L1 (F : Fine → ℂ) (hf : Envelope F) :
    (∫ v, ‖conditionalPush A N n m F v‖ ∂scene A N n m) ≤
      ∫ u, ‖F u‖ ∂scene A N n (m+1) := by
  haveI : IsProbabilityMeasure (scene A N n m) := probability sel hm.le
  rw [←posterior_mean A sel hm _ (norm_envelope hf)]
  apply integral_mono ((norm_envelope (posterior_envelope_complex A sel hm F hf)).integrable _)
    ((posterior_envelope_real A sel hm _ (norm_envelope hf)).integrable _)
  exact Marked.conditional_mean_norm A sel hm F

end YM.Integration.FVA1Physical.Round2
