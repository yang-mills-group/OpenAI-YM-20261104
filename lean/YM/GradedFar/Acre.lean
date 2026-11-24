import YM.GradedFar.Caravan
/-!
# QScale report across each compact; both towers of bounds now issued
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor.Lounge
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar YM.FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
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
local notation "Θ" => Error J Z M ν h p t
-- window cost for clock | ≤ t' uniform
include hG in
private lemma almost {K:ℝ}(hK:2≤K): ∀ᶠ r in trail,∀ T,Fits K T→ 0<g (r*T) ∧ g (r*T) ≤ 2*g r:=by
 obtain hp:=show 0<K from zero_lt_two.trans_le hK
 have hv : ∀ᶠ r in trail,K≤ K*g r^(-(1:ℝ)):= by
    filter_upwards [strength_positive hG,(Coupling.conforms hG (strength_coupling hG)).eventually_le_const zero_lt_one] with r hr he
    rw [Real.rpow_neg_one]; exact le_mul_of_one_le_right hp.le ((one_le_inv₀ hr).2 he)
 filter_upwards [ hv,(fund_up (hG:=hG) hp zero_lt_one), (funded_mono (hG:=hG)),(show ∀ᶠ r in trail,0<r from self_mem_nhdsWithin),strength_positive hG]
    with r hi hx hq hr h₀ T h
 rcases le_total 1 T with H|H'
 · exact hx T ⟨H,h.2.trans hi⟩
 obtain ⟨he,H⟩:= hq (r*T) ⟨mul_pos hr (Fits_pos hp h), mul_le_of_le_one_right hr.le H'⟩; exact ⟨he,H.trans (by linarith)⟩

private lemma factors {K T:ℝ}(hK:2≤K)(hT:Fits (K*2) T):∃ T' x:ℝ, Fits K T' ∧ Fits 2 x ∧ T=T'*x:=by
 by_cases hx: T>K
 · refine ⟨T/2,2,⟨le_trans (by exact (inv_le_one₀ (zero_lt_two.trans_le hK)).2 (one_le_two.trans hK)) (by linarith),by linarith only [hT.2]⟩,by constructor <;> norm_num,by ring⟩
 by_cases hv: T<K⁻¹
 · have hp:=show 0<K from zero_lt_two.trans_le hK; refine ⟨T*2,(1/2:ℝ),⟨?_,?_⟩,by constructor <;> norm_num,by ring⟩
   · calc _= ((K*2)⁻¹)*2:=by field_simp
          _≤ _:= mul_le_mul_of_nonneg_right hT.1 (by norm_num)
   have ht:K⁻¹ ≤ 1:= (inv_le_one₀ hp).2 (one_le_two.trans hK); linarith
 exact ⟨T,1,⟨le_of_not_gt hv,le_of_not_gt hx⟩,by constructor <;> norm_num,by rw [mul_one]⟩

private def Steam (t:ℝ→ℝ) (K:ℝ): Prop:= ∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail, ∀ T,Fits K T→ Error J Z M ν h p t (b*(g r)^(p+1)) r T
variable (hs:Stamp J Z M ν t h 1)(hu:Stamp J Z M ν t h p)(hc:DialStamp Z M ν t p)(ht: Coupling G t) (hp:1≤p)
include H ht hp hs hu hc
private lemma doubles {K:ℝ}(hK:2≤K)(H₀:Steam J Z M ν h p t K): Steam J Z M ν h p t (K*2):=by
 obtain ⟨c,Hc,C⟩:= always Z M ν h p H hK ht hp; obtain ⟨b,Hb,B⟩:= H₀; obtain ⟨d,Hd,hD⟩:= two_step J Z M ν p (hG:=hG) hu hc
 refine ⟨(2^h*(2^h+1)+3)*b+c+ 2*d*2^(p+1),by positivity,?_⟩
 filter_upwards [C,B,threshold hK _ (hD.and (local_cost J Z M ν h H hs)),almost (hG:=hG) hK] with r hp' hr hf hR T Ht
 obtain ⟨T,x,hT,hx,rfl⟩:= factors hK Ht; obtain ⟨hs',hv⟩:= hf T hT
 obtain ⟨hU,hV⟩:= hR T hT
 apply (passage J Z M ν h p H (Fits_pos (zero_lt_two.trans_le hK) hT) hx (hr T hT) (hp' T hT) (hs' x hx) (hv x hx)).mono
 refine le_trans ?_ (show _ from le_of_eq (show (2^h*(2^h+1)+3)*(b*g r^(p+1))+c*g r^(p+1)+2*(d*(2*g r)^(p+1))=_ by ring))
 gcongr
private lemma towers (k:ℕ):Steam J Z M ν h p t ((2:ℝ)^(k+1)):=by
 induction k with
 | zero => rw [Nat.zero_add,pow_one]; exact two_step J Z M ν p (hG:=hG) hu hc
 | succ k ih=>
   rw [pow_succ]
   exact doubles J Z M ν h p H hs hu hc ht hp
     (le_trans (b:= (2:ℝ)^1) (le_of_eq (pow_one _).symm) (pow_le_pow_right₀ (by norm_num) (by omega))) ih
private lemma boxes {K:ℝ}(hK:2≤K):Steam J Z M ν h p t K:=by
 obtain ⟨k,h₁,h₂⟩ := exists_nat_pow_near (show 1≤K from one_le_two.trans hK) one_lt_two; obtain ⟨b,hb,B⟩:=towers J Z M ν h p H hs hu hc ht hp k
 refine ⟨b,hb,B.mono fun i h t ht=> ?_⟩
 exact h _ ⟨ (inv_anti₀ (zero_lt_two.trans_le hK) h₂.le).trans ht.1, ht.2.trans h₂.le ⟩

-- all intervals of η compacts (correlation & β projections elsewhere)
def StampScale (t:ℝ→ℝ)(K:Set ℝ):Prop := ∃ b:ℝ,0≤b ∧ ∀ᶠ r in trail,∀ η∈K,
    opField (U' r (r*Real.exp (-η)) - cropK Kt η p (t r) h) ≤ b*(g r)^(p+1) ∧
    ‖(t (r*Real.exp (-η)):ℂ)-appointedH140Crop p (t r) (ϕ η)‖ ≤ b*(g r)^(p+1)
omit H ht hp hs hu hc in
private lemma inverse_budget {K:Set ℝ} (hK:IsCompact K) : ∃ C:ℝ,2≤C ∧ ∀ η∈K, Fits C (Real.exp (-η)):= by
 obtain ⟨b,h⟩:= hK.exists_bound_of_continuousOn (f:=fun x:ℝ=> Real.exp x) Real.continuous_exp.continuousOn
 obtain ⟨c,H⟩:= hK.exists_bound_of_continuousOn (f:=fun x:ℝ=> Real.exp (-x)) (Real.continuous_exp.comp continuous_neg).continuousOn
 refine ⟨max 2 (max b c), le_max_left ..,fun x hx=> ⟨ ?_,?_⟩⟩
 · rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos _) ((le_trans ((le_abs_self _).trans (show |Real.exp x| ≤ b from h _ hx)) (le_max_left ..)).trans (le_max_right ..))
 exact (( (le_abs_self _).trans (show |Real.exp (-x)| ≤ c from H _ hx)).trans (le_max_right ..)).trans (le_max_right ..)
theorem stampScale {K:Set ℝ}(hK:IsCompact K): StampScale J Z M ν h p t K:= by
 obtain ⟨c,hc',hI⟩:= inverse_budget hK; obtain ⟨b,hb,hq⟩:= boxes J Z M ν h p H hs hu hc ht hp hc'
 have hp:1 ≤ c^h:=one_le_pow₀ (one_le_two.trans hc'); have hμ:b ≤ c^h*b:= le_mul_of_one_le_left hb hp
 refine ⟨c^h*b,by positivity,hq.mono fun r hr η hη=>?_ ⟩; obtain ⟨hA,hB⟩:= hr _ (hI η hη)
 let T:=Real.exp (-η); have hv:=hI η hη
 dsimp only at hB hA; rw [Real.log_exp, neg_neg] at hB hA; constructor
 · rw [opstamp, map_sub (stamp G h), used,setting]
   dsimp only; rw [Real.log_exp,neg_neg,← mul_sub]; obtain he:=box_cost h (G:=G) _ (one_le_two.trans hc') T (hI _ hη)
   dsimp only [T] at he; rw [ Real.log_exp,neg_neg] at he; exact (norm_mul_le ..).trans ((mul_le_mul he hA (norm_nonneg _) (zero_le_one.trans hp)).trans_eq (by rw [mul_assoc]))
 rw [op_crop]; apply hB.trans; have hv' : 0≤(g r)^(p+1):=by unfold strength; positivity -- g nonneg global yes sqrt
 exact mul_le_mul_of_nonneg_right hμ hv'
end YM.Integration.GradedFar.Neighbor.Lounge
