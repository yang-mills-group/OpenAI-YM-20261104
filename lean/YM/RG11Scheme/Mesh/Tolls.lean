import YM.RG11Scheme.Mesh.Round
import YM.Pert.Triangle.Price

/-! Near and exterior ranges for integrated vertices. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Mesh
open Lattice Function Filter Set MeasureTheory Pert Pert.Full Metric
open scoped Topology BigOperators Classical
variable {n : Side}
private def fare (C:ℝ) (x:E4) := C / (1+‖x‖)^5
private lemma fare_int (C) : Integrable (fare C) := by
   have hi : Integrable (fun x:E4=> (1+‖x‖)^(-(5:ℕ):ℝ)) := integrable_one_add_norm (by norm_num)
   unfold fare; simp_rw [div_eq_mul_inv]; simpa only [Pert.Triangle.inv_power] using hi.const_mul C
private def stall (C R:ℝ) := (ball (0:E4) R).indicator (fun z=> C/‖z‖^3)
private lemma stall_int (C R) : Integrable (stall C R) := by
   apply (integrable_indicator_iff measurableSet_ball).2
   rw [show (fun z:E4=>C/‖z‖^3)=fun z:E4=>C*(‖z‖^3)⁻¹ from funext fun _=> div_eq_mul_inv ..]
   apply Integrable.const_mul (f:=fun z:E4=>(‖z‖^3)⁻¹) (μ:=volume.restrict _) _
   apply integrableOn_ball_of_norm_le_rpow (by simp : 1≤Module.finrank ℝ E4) (α:=3) (by norm_num) (C:=1) (Eventually.of_forall fun q:E4=> by rw [Real.rpow_neg (norm_nonneg q),show (3:ℝ)=((3:ℕ):ℝ) from by norm_num,Real.rpow_natCast,Real.norm_of_nonneg (by positivity)]; exact (one_mul _).symm.le) (by fun_prop)
lemma flight : Summable (fun p:Cover=> (wide p^5)⁻¹) := by
   apply payment (h:=1) (by norm_num) (E:=ℝ)
   refine (fare_int (7^5)).mono' (pad_strong (by norm_num) _) (Eventually.of_forall fun x:E4=>?_)
   have he : 1+‖x‖ ≤ 7*wide (pad 1 x) := by linarith only [coin (by norm_num : (1:ℝ)>0) x,wide_one (pad 1 x)]
   change ‖(wide _^_)⁻¹‖ ≤ 7^5/(1+‖x‖)^5
   have hp:=wide_pos (pad 1 x)
   rw [Real.norm_of_nonneg (by positivity), ←one_div]
   exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by rw [one_mul,←mul_pow];gcongr)

variable {E:Type*} [NormedAddCommGroup E]

def FarPrice (T:Align.Itinerary) (f:ℕ→ Cover→E) : Prop := ∃ C≥0, ∀ᶠ i:ℕ in atTop,∀ p, ‖f i p‖ ≤ C / (1 + T.gap i * wide p)^5
def AtPrice (T:Align.Itinerary) (f:ℕ→ Cover→E) : Prop := ∃ C≥0,∃ R≥0,∀ᶠ i:ℕ in atTop,∀ p, ‖f i p‖ ≤ C/(T.gap i * wide p)^3 ∧ (f i p ≠ 0 → T.gap i * wide p ≤ R)
structure FeeList (T:Align.Itinerary) (f:ℕ→ Cover→E) : Prop where
  receipt : ∃ B : E4→ℝ, Integrable B ∧ ∀ᶠ i:ℕ in atTop, ∀ z:E4,z≠0→ ‖f i (pad (T.gap i) z)‖ ≤ B z

variable {T:Align.Itinerary} {f:ℕ→ Cover→E} {F:E4→E}
lemma FarPrice.fees (p : FarPrice T f) : FeeList T f := by
   obtain ⟨C,hc,H⟩:=p
   refine ⟨fare (C*6^5),fare_int _,H.mono (fun i hi z _=>(hi _).trans ?_)⟩
   have h:=T.positive i
   have he:=coin h z
   have hz:1+‖z‖ ≤ 6*(1+T.gap i* wide (pad (T.gap i) z)) := by linarith
   have hp:=wide_pos (pad (T.gap i) z)
   apply (div_le_div_iff₀ (by positivity) (show 0<(1+‖z‖)^5 by positivity)).mpr -- rhs
   rw [mul_assoc,←mul_pow]; gcongr
lemma AtPrice.fees (p : AtPrice T f) : FeeList T f := by
   obtain ⟨C,hc,R,hR,H⟩:=p
   refine ⟨stall (C*6^3) (6*R+1),stall_int ..,H.mono (fun i hi z hz=> ?_)⟩
   let x:=pad (T.gap i) z;have h := T.positive i; have hu:=coin h z
   by_cases he : f i x=0
   · exact (le_of_eq (by rw [he,norm_zero] : ‖f i x‖=0)).trans (indicator_nonneg (fun _ _=> by positivity) z)
   have hk := (hi x).2 he
   have ht : z ∈ ball (0:E4) (6*R+1) := mem_ball.mpr (by rw [dist_zero_right]; linarith only [hu,hk])
   have hw : 0<‖z‖ := norm_pos_iff.mpr hz
   have hr:=wide_pos x
   unfold stall; rw [indicator_of_mem ht]; apply (hi x).1.trans
   apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr; rw [mul_assoc,←mul_pow]; gcongr; linarith only [hu]

variable [NormedSpace ℝ E] [CompleteSpace E]
def cover_read (T:Align.Itinerary) (f:ℕ→ Cover→E) (i:ℕ) : E := T.gap i ^ 4 • ∑' p:Cover, f i p
lemma paying (h:FeeList T f) (hp:∀ z:E4,z≠0→∀ p:ℕ→ Cover,Tendsto (fun j=> incVec (T.gap j) (p j)) atTop (𝓝 z)→Tendsto (fun j=> f j (p j)) atTop (𝓝 (F z))) : Integrable F ∧ Tendsto (cover_read T f) atTop (𝓝 (∫ z,F z)) := by
   obtain ⟨B,hB,hv⟩:=h.receipt
   let v i:= f i ∘ pad (T.gap i)
   have hl : ∀ᵐ z ∂(volume:Measure E4), Tendsto (fun i=>v i z) atTop (𝓝 (F z)) := (volume.ae_ne 0).mono fun z hz=> hp z hz (fun i=>pad (T.gap i) z) (plots T z)
   have hr i : AEStronglyMeasurable (v i) volume := pad_strong (T.positive _) _
   have he : ∀ᵐ z ∂volume, ‖F z‖ ≤ B z := (hl.and (volume.ae_ne 0)).mono (fun z hz=> le_of_tendsto hz.1.norm (hv.mono fun i hi=>hi z hz.2))
   have hb : ∀ᶠ i in atTop,∀ᵐ z ∂volume, ‖v i z‖ ≤ B z := hv.mono (fun i hi=>(volume.ae_ne 0).mono hi)
   refine ⟨hB.mono' (aestronglyMeasurable_of_tendsto_ae atTop hr hl) he,(tendsto_integral_filter_of_dominated_convergence _ (Eventually.of_forall hr) hb hB hl).congr' (hb.mono fun i hi=>?_)⟩
   have he:=hB.mono' (hr i) hi
   exact (throughput (T.positive i) he).unique ((payment (T.positive i) he).hasSum.const_smul _)
end YM.RG11Scheme.Mesh
