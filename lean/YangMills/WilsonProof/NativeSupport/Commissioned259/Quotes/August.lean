import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Trial
/-! # On the ratio interval (price). All orders costs, later used at each Quote
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh O.Read Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ}
    (N : WilsonPrescription G) (ν:ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "W" => Scale.Measure.adjust N.scheme N.criterion
local notation "Zf" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "ψ" => GroupS.ψ N.criterion M ν

variable {r T u g : I→ℝ} (hr:Tendsto r L late) (ht:∀ᶠ i in L,T i∈ Icc 1 2)
abbrev post (T: I→ℝ)(i:I):ℝ := -Real.log (T i)
-- genuine radius-cost bound from scales
include ht hr
lemma later_G (hG : G.Simple) : Tendsto (fun i=>r i*T i) L late ∧
    (fun i=> g0 G (r i * T i))=O[L] (g0 G ∘ r) := by
  have hp : ∀ᶠ i in L, permit G 2 0 (r i) (r i*T i) 1 := by
    filter_upwards [hr.eventually self_mem_nhdsWithin,ht] with i hr ht; refine ⟨le_mul_of_one_le_right (show 0 ≤ r i from le_of_lt hr) ht.1, le_rfl,?_⟩
    rw [mul_one,neg_zero,Real.rpow_zero,mul_one]; exact mul_le_mul_of_nonneg_left ht.2 (le_of_lt hr)
  have he:= corridor hG hr hp; exact ⟨he.1,he.2.1⟩
omit hr
lemma placed_post : ∀ᶠ i in L, post T i ∈ Icc (-Real.log 2) 0 := by
  filter_upwards [ht] with i ⟨h,g⟩; refine ⟨ neg_le_neg (Real.log_le_log (by linarith) g), neg_nonpos.mpr (Real.log_nonneg h) ⟩
lemma local_fare {Q:Set ℝ} {η:I→ℝ} {f:ℝ→ℂ} (e:IsCompact Q)(h: ContinuousOn f Q)(hp:∀ᶠ i in L, η i∈Q) : Fare Pose.home L home (f∘η) := by
  obtain ⟨C,H⟩:=e.exists_bound_of_continuousOn h
  exact Fare.cent (hp.mono fun i hi=>H _ hi)
-- spare comp cutoff (allows arbitrary hs later)
omit ht
lemma one_paid (L : Filter I) : ∀ᶠ i in L,1 ≤ Pose.home i := Eventually.of_forall fun _=>le_refl _
lemma rhythm_sublime {f:ℝ→ℂ} (h:Rhythm f): Continuous f := by
  obtain ⟨p,rfl⟩ := Rhythm.from_poly.mp h
  fun_prop

variable {η:I→ℝ}
local notation "Hπ" => (post T)
include ht H
lemma ratio_tune : Tunes home L home (ψ ∘ post T) := fun p=>
    local_fare ht isCompact_Icc (rhythm_sublime (Rhythm.unit.mpr ((H.dilation ν).check.smooth p)) |>.continuousOn ) (placed_post ht)
lemma ungrown (d:ℕ) : Uniform home L home (fun i=>Zf (post T i) d) := fun a b p=> by
  simp_rw [prose,coeff_mk]; exact local_fare ht isCompact_Icc ((rhythm_sublime ((H.dilation ν).check.proper d p (theory b) (coord a))).continuousOn) (placed_post ht)
omit H
lemma unfed {Q:Set ℝ} (hp : ∀ᶠ i in L, η i∈ Q)(h:IsCompact Q) : Uniform home L home (fun i=> C (Level.Dial (G:=G) d (η i))) := by
  intro a b p; simp_rw [prose,coeff_mk,coeff_C]; by_cases he:p=0;
  · simp_rw [if_pos he]; refine local_fare (f:=fun t=>engine G d t a b) ht h ?_ hp; change ContinuousOn (fun t=>engine G d t a b) Q
    simp_rw [gear_cost]; by_cases e:b=a <;> simp [e] <;> fun_prop
  simp_rw [if_neg he]; exact Fare.constant _
lemma eng_down : (fun i=>stiffness (engine G d (post T i)))=O[L] Pose.home := by
  refine matrixPay.mpr fun a b=>?_ ; have hp:= homebound (unfed ht (placed_post ht) isCompact_Icc (d:=d) (G:=G) a b 0); simp_rw [prose,coeff_mk,coeff_C, if_true] at hp; exact hp
lemma eng_up : (fun i=>stiffness (engine G d (-(post T i))))=O[L] Pose.home := by
  have hh:∀ᶠ i in L,-post T i∈Icc 0 (Real.log 2) := (placed_post ht).mono (fun i ⟨l,r⟩=>⟨neg_nonneg.mpr r,neg_le.mpr l⟩)
  refine matrixPay.mpr fun a b=>?_ ; have hp:= homebound (unfed ht hh isCompact_Icc (d:=d) (G:=G) a b 0); simp_rw [prose,coeff_mk,coeff_C, if_true] at hp; exact hp
include H
lemma delivered : Uniform Pose.home L home (fun i=>guardTrial N ν M (post T i) d) := by
  let L (i : I):= Zf (post T i) d; unfold guardTrial conversion; have hp (i:I):MS.Book.Program.Rooted (ψ (post T i)):= ((H.dilation ν).check.led ..).start
  have h:= Uniform.switched (P:=fun _=>mirror (W d)) (one_paid _) hp (ratio_tune N ν M H ht) (Notes.compact_constant _)
  -- simplify home weights: pointwise 1
  have he:= Uniform.product (one_paid _) (Uniform.product (one_paid _) (unfed ht (placed_post ht) isCompact_Icc) (ungrown N ν M H ht d)) h
  intro a b n; exact (he a b n).extend (Eventually.of_forall fun i=>by unfold Pose.home; ring)

-- next meter ψ crop. Need real! price maybe paid from underlying μ Law .CoreR.
def rumor (s t:ℝ) (q:ℕ) : ℝ := (crop q t (ψ s)).re
omit ht
lemma realized_r (s t:ℝ)(q:ℕ) : crop q t (ψ s)=(rumor N ν M s t q:ℂ) := by
  let F:= (((H.dilation ν).check).led s).real
  have h := Reg.Unique.coinR F; have he : star (crop q t (ψ s))=crop q t (ψ s) := by
    simp_rw [crop_apply,star_sum,star_mul',star_pow,Complex.star_def, Complex.conj_ofReal]
    simp only [← Complex.star_def,h]
  refine Complex.ext ?_ ((Complex.conj_eq_iff_im.mp he).trans (?_ : _ )) <;> rfl
include ht
lemma rumor_stamp (u:I→ℝ)(q:ℕ) : Coin L Pose.home u g q home (fun i=> (↑(rumor N ν M (post T i) (u i) q):ℂ)) (fun i=> ψ (post T i)) := by
  simp_rw [←realized_r N ν M H]; exact Coin.already (ratio_tune N ν M H ht)
lemma trend (hc:Tendsto u L (𝓝 0))(q:ℕ) : Tendsto (fun i=>rumor N ν M (post T i) (u i) q) L (𝓝 0) := by
  have hp : ∀ᶠ i in L, |u i| ≤ 1 := hc.abs.eventually (ge_mem_nhds (by simp))
  have he:= homebound (Tunes.excess (one_paid _) hp (isBigO_refl u L) q 0 (Nat.zero_le _) (ratio_tune N ν M H ht))
  simp_rw [Function.comp_def] at he
  let t (i:I) := ψ (post T i)
  have h (i:I) : crop 0 (u i) (ψ (post T i))=0:=by rw [crop_apply, Finset.sum_range_succ,Finset.sum_range_zero, zero_add, ((H.dilation ν).check.led ..).start, mul_zero]
  simp_rw [h,sub_zero] at he
  obtain hx:= (he.congr_right (g₂:=u) (fun i=>by simp [Pose.home])).trans_tendsto hc
  exact (show Tendsto _ _ _ from Complex.continuous_re.tendsto 0).comp hx
end YM.FVA2.GradedFar259.Quotes
