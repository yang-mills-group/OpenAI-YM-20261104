import YM.Trace.Physicalv2.Germ
import YM.Push.LOCAL_SPLITTING.Comparison

/-! The finite probes of the captured field on the vacuum which carries it. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryReading
open Function Filter Labels Lattice Wilson RG Source Next.Foundations
open ProjectorNext.Equivariance Push.Local Trace.Physical.Germ
open scoped Topology Classical

variable {G : Gauge} {d : ℕ} {n : Side} {F : Labels.Frame G d} {A : Hol G}
variable {R : Rep G n} {o : Site n} {B : SectionData F}

def reading (B : SectionData F) (R : Rep G n) (o : Site n) (q : Coefficient F n)
    (U : Config G n) : ℂ := q.density o B R U / (R.eval U : ℂ)

theorem on_clear (hb : B.Sound A) (q : Coefficient F n) {U : Config G n}
    (clear : flags R.p.threshold U = ∅) :
    reading B R o q U = B.places (F.scaled R.p.threshold⁻¹ q.x) o U + ∑' i, q.regular i U := by
  rw [reading,noFlagCharge q o B hb clear,mul_div_cancel_left₀ _ (noFlagEval clear)]

theorem flat (hb : B.Sound A) {q : Coefficient F n} (hq : q.Format o A R) :
    reading B R o q 1 = B.places (F.scaled R.p.threshold⁻¹ q.x) o 1 := by
  rw [on_clear hb q ((offFlags R.p.threshold R.p.threshold_pos).self_of_nhds)]
  simp only [hq.identity_null,tsum_zero,add_zero]

theorem probe (hb : B.Sound A)
    (size : ∀ x ∈ B.stencil, ∀ i : Axis, 20*((x i).natAbs+1) ≤ n.val)
    (order : d ≤ R.p.order) (power : d ≤ R.p.power)
    (section_smooth : ∀ v, HasOrderAt (B.places v o) 1 d) {q : Coefficient F n}
    (hq : q.Format o A R) {κ price : ℝ} (paid : q.remBound o R κ price)
    (smooth : HasOrderAt (reading B R o q) 1 d) (p : Probe G d) :
    runProbe F p (projection F A R.p.threshold o q) =
      jet A p R.p.threshold o (reading B R o q) := by
  let θ := R.p.threshold
  let core := B.places (F.scaled θ⁻¹ q.x) o
  let f := reading B R o q
  have coreTest : JetTest A o (F.coords.symm (F.scaled θ⁻¹ q.x)) core := by
    simpa only [Reads, if_pos (nonwrapping_placement B o size)]
      using placed_reads B o size hb (F.scaled θ⁻¹ q.x)
  have corePaid : runProbe F p q.x = jet A p θ o core := by
    simpa only [F.coords.apply_symm_apply,F.scaled_inv (show θ ≠ 0 from R.p.threshold_pos.ne')]
      using charged F A θ coreTest p
  have vec := vector_summable F A hq paid order power
  obtain ⟨_,_,_,_,_,_,⟨E,hmass,he⟩,_⟩ := paid
  have hsum : Summable E := hmass.2.1.of_nonneg_of_le (fun i => (he i).1)
    (fun i => R.p.loMass _ _ (he i).1)
  have readSum : f - core =ᶠ[𝓝 1] fun U => ∑' i, q.regular i U := by
    filter_upwards [offFlags θ R.p.threshold_pos] with U hU
    change reading B R o q U - core U = _
    rw [on_clear hb q hU]
    exact add_sub_cancel_left (core U) _
  have all := jet_sum hq.smooth he hsum readSum d (smooth.sub (section_smooth _)) order A
    (θ • p.1) p.2 (Nat.le_of_lt_succ p.2.isLt)
  have forms := vec.hasSum.mapL (runProbe F p)
  have aligns (i : ℕ) : runProbe F p (vector F A θ o (q.regular i)) =
      jet A p θ o (q.regular i) := charged F A θ (computed A (hq.smooth i) o order) p
  change HasSum (fun i => runProbe F p (vector F A θ o (q.regular i))) _ at forms
  simp only [aligns] at forms
  change HasSum (fun i => jet A p θ o (q.regular i)) (jet A p θ o (f-core)) at all
  have h₀ : ContDiffAt ℝ d (f ∘ A.testLinks d o (θ • p.1)) 0 := by
    apply ContDiffAt.congr_of_eventuallyEq _ ((increment_testLog ..).fun_comp f)
    change ContDiffAt ℝ d ((f ∘ increment 1) ∘ testLog A d o (θ • p.1)) 0
    apply ContDiffAt.comp 0 (g:=f ∘ increment 1) _ ((testLog_diff A d o (θ • p.1)).of_le le_top)
    rw [testLog_zero]
    exact smooth
  have heq := forms.unique all
  rw [show jet A p θ o (f-core) = jet A p θ o f - jet A p θ o core from
    iteratedDeriv_fun_sub (h₀.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt)))
      ((coreTest (θ • p.1)).1.of_le (Nat.cast_le.mpr (Nat.le_of_lt_succ p.2.isLt)))] at heq
  rw [projection,map_add,heq,corePaid,add_sub_cancel]

end YM.Integration.WilsonCapturedPrimaryReading
