import YM.GradedFar.Stair
/-!
# Full compact η version of G.1

Already did entire growing version & compact [-log 2,+log2]. Folklore compact interval
extension also verified; includes *both signs* directions. No trading downward length
with g at the wrong end.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor.Lounge
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar YM.FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (J:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ) (h p:ℕ)
local notation "g"=> strength G
local notation "γ" => fun (T:ℝ)=> -Real.log T
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "U'" => fun (r s:ℝ)=> LinearEquiv.toLinearMap (relative J r s h)
local notation "D'" => stretching G h
local notation "op" => stamp G h
variable {t:ℝ→ℝ} {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "B'" => fare Z M ν h p
local notation "J'" => ticker Z M ν p
local notation "Θ" => Error J Z M ν h p t

-- compact of signed scale. get all [2^-k,2^k].
abbrev Fits (K:ℝ) (t:ℝ):Prop:= t∈ Icc K⁻¹ K
lemma Fits_pos {K t:ℝ} (hK:0<K)(he:Fits K t):0<t:= lt_of_lt_of_le (inv_pos.mpr hK) he.1
lemma fits_turn {K T:ℝ}(hK:0<K)(ht:Fits K T): Fits K T⁻¹ :=
    have hp:= Fits_pos hK ht; ⟨inv_anti₀ hp ht.2,(inv_le_of_inv_le₀ hK ht.1)⟩ -- name
lemma log_box {K T:ℝ}(hK:0<K)(ht:Fits K T):|γ T|≤ Real.log K:=by
 rw [abs_neg]; apply abs_le.mpr; constructor -- via abs_le
 · obtain hS:= Real.log_le_log (inv_pos.mpr hK) ht.1; rw [Real.log_inv] at hS; exact hS
 exact Real.log_le_log (Fits_pos hK ht) ht.2
lemma two_box (t:ℝ)(K:ℝ)(h:2≤K)(hp:Fits 2 t): Fits K t:= ⟨(inv_anti₀ (zero_lt_two' ℝ) h).trans hp.1,hp.2.trans h⟩
lemma box_cost (K:ℝ)(hK:1≤K) (x:ℝ)(hp:Fits K x): ‖D' (γ x)‖≤K^h:=by
 rcases le_total 1 x with h|h'
 · exact (stretch_up G _ h).trans (pow_le_pow_left₀ (zero_le_one.trans h) hp.2 _)
 dsimp only; rw [← Real.log_inv]; have he:= Fits_pos (zero_lt_one.trans_le hK) hp; exact (stretch_down G _
    ((one_le_inv₀ he).mpr h')).trans (one_le_pow₀ hK)
include H
lemma local_cost (hf:Stamp J Z M ν t h 1): ∀ᶠ r in trail,∀ x,Fits 2 x → ‖op (U' r (r*x))‖≤2^h+1:=by
 obtain ⟨b,hb,hv⟩:= hf
 have he: Tendsto (fun r=> b*(g r)^2) trail (𝓝 0):=by simpa using ((Coupling.conforms hG (strength_coupling hG)).pow (2:ℕ)).const_mul b
 filter_upwards [hv, he.eventually_le_const zero_lt_one] with r hr H' x hx
 specialize hr x (by simpa only [one_div] using hx); rw [first_crop Z M ν H,opstamp,map_sub (stamp G h)] at hr
 change ‖op (U' r (r*x)) - stretching G h (-Real.log x)‖ ≤ _ at hr
 simpa only [add_comm (1:ℝ),sub_add_cancel] using (norm_add_le (op (U' r (r*x))-(D' (γ x))) (D' (γ x))).trans
   (add_le_add (hr.trans H') (box_cost h (G:=G) 2 one_le_two x hx))
variable {K:ℝ} (hK:2≤K)
include hK
omit H

lemma threshold (L:ℝ→Prop)(u:∀ᶠ r in trail,L r): ∀ᶠ r in trail,∀ x,Fits K x → L (r*x) := by
 have hk:0<K:=zero_lt_two.trans_le hK; obtain ⟨a,ha,A⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp u
 filter_upwards [(show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin), (ge_mem_nhds (div_pos ha hk)).filter_mono nhdsWithin_le_nhds] with r hr hp x hx
 exact A ⟨mul_pos hr (Fits_pos hk hx), (mul_le_mul_of_nonneg_left hx.2 hr.le).trans ((le_div_iff₀ hk).mp hp)⟩
include H
omit H hK
include hG
lemma two_step {h:ℕ}(h1:Stamp J Z M ν t h p)(hc:DialStamp Z M ν t p): ∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail, ∀ T,Fits 2 T → Error J Z M ν h p t (b*(g r)^(p+1)) r T:=by
 obtain ⟨c,hc,Hc⟩:= hc; obtain ⟨d,hd,Hd⟩:= h1; refine ⟨max ((2:ℝ)^h*d) c,(mul_nonneg (pow_nonneg (by norm_num) _) hd).trans (le_max_left ..),?_⟩
 filter_upwards [Hc,Hd,strength_positive hG] with r hc hd hp T hT
 have H₁: T∈ Icc (1/2:ℝ) 2:= by simpa [one_div] using hT
 specialize hd T H₁; specialize hc T H₁; refine ⟨?_, ?_⟩ -- ticker eq
 · rw [opstamp,map_sub (stamp G h), used] at hd
   let D:= stretching G h; let u:= stamp G h ((relative J r (r*T) h).toLinearMap)
   let v:=fare Z M ν h p (γ T) (t r); change ‖D (Real.log T)*u-v‖ ≤ _
   rw [show D (Real.log T)*u-v=D (Real.log T)*(u-D (γ T)*v) from by rw [mul_sub, ← mul_assoc, show D (Real.log T)*D (γ T)=1 from (by unfold D; dsimp only; rw [stretch_mul,add_neg_cancel, flat]), one_mul]]
   have hx: ‖D (Real.log T)‖≤ (2:ℝ)^h:= by
      obtain hv:=box_cost h (G:=G) 2 one_le_two T⁻¹ (fits_turn zero_lt_two hT); dsimp only at hv; rw [Real.log_inv,neg_neg] at hv; exact hv
   exact (norm_mul_le ..).trans ((mul_le_mul hx hd (norm_nonneg _) (by positivity)).trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)))
 rw [op_crop] at hc; exact hc.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
end YM.Integration.GradedFar.Neighbor.Lounge
