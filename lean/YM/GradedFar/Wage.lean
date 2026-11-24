import YM.GradedFar.Feed
/-!
# Funding the center field price with its actual weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Filter Finset Function Set Spec Table Extraction OPE OPE.Orbits OPE.Log
open Trace.Pilot PhysMS XSpace XSpace.Normalize FVA2.GradedFar
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}(F:Final C fo S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (Jp:ℝ→tower S)
    {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ} {A B:Type*}{t:Filter A}{U:A→B→Prop}
    {M δ:ℝ}{P:A→B→Purchase F I J} {s L W:A→B→ℝ}
    (l:Labor M δ t U L s P) (hG:G.Simple) (Ht:LogTrace F R.port)
    (Hw:∀ i,Coat F R Jp (d i))(Hw':∀ i,Coat F R Jp (e i))
    {u:A→B→WholeInput G d}{v:A→B→WholeInput G e}
    (hu:∀ᶠ a in t,∀ z i,U a z → width (u a z i) ≤ 1)
    (hv:∀ᶠ a in t,∀ z i,U a z → width (v a z i) ≤ 1)
local notation "Scene" => Purchase F I J
local notation "gapₗ" => Sold t U L
local notation "Ok" => Safe t U L
local notation "wₗ" => fun a z=> moved Jp (s a z) (v a z)
local notation "u₁" => fun a z=> moved Jp (smallLength P a z) (u a z)
local notation "xₗ" => fun (a:A) (z:B)=> Purchase.head (P a z)
local notation "oₗ" => fun (a:A) (z:B)=> Purchase.center (P a z)
local notation "yₗ" => fun a z=> Purchase.tail (P a z) (s a z)
local notation "Vₗ" => fun a z=> spectator F (Purchase.viewer (P a z))
include l
local notation "tinyₗ" => smallLength P
local notation "leftₗ" => fun a z=> Launch.mk (Purchase.head (P a z)) (Purchase.center (P a z))
omit [Fintype I] [Fintype J] in
lemma Labor.S_s (h:ℕ) : Safe t U L (fun a z=>(s a z^h)⁻¹):= l.properO F
  (l.large.pos.mono fun _ ha z hz=> inv_nonneg.mpr (pow_nonneg (ha z hz|>.le) _))
include hG Hw' hv Ht
lemma paysUpon (h:ℕ)(p:S.Field h) : gapₗ (fun a z=>(s a z^h)⁻¹)
    (fun a z=> upon (Vₗ a z) h (oₗ a z) (yₗ a z) (wₗ a z) p):= by
  refine (present (Φ:=fun a z=>watch F (yₗ a z) (oₗ a z) h (Purchase.viewer (P a z)) p) F R Jp
    l.large Hw' hv (l.S_s F h) ?_).congr (fun a z=> watch_apply F (yₗ a z) _ _ _ p _)
  intro q
  let E := low (d:=e) F R q; let c:= actors (d:=e) F R q; obtain ⟨k,b,hb,H⟩:= parent_cost F E hG Ht l.nonneg l.clearance h p c
  refine ⟨k,b,hb,?_⟩; filter_upwards [l.large.1 _ H,l.large.pos,l.large.2,l.inserted,l.common] with a ha hs hx ht hX z hz
  have hi:=(hX z hz).2; obtain ⟨hl,hk⟩:=hx z hz
  rw [watch_apply]
  have hq:(stars F R q)=fun i:J=> F.sector.derivatives.rise (Cast.costs F R (q i)) (c i) := rfl
  rw [hq,upon_include F (yₗ a z) (oₗ a z) h _ (fun i:J=>Cast.costs F R (q i)) _ c hi];
  have h : (s a z ^ (h+∑ i,E i))⁻¹ = (s a z^h)⁻¹ / s a z^(∑ i,E i) := by rw [pow_add,mul_inv_rev,div_eq_mul_inv,mul_comm]
  refine (ha z hz _ _ (ht z hz) _).trans ?_; rw [one_div,h]; change b * _ * _ ≤ _
  have hs:0<s a z:=hs z hz; gcongr

-- Sales for moving insertions through an actual center (fixed physical basis)
lemma dynamic (h:ℕ){p:A→B→ S.Field h}(Hp:gapₗ W p)(hq:Safe t U L W):
    gapₗ (fun a z=> W a z*(s a z^h)⁻¹) (fun a z=> upon (Vₗ a z) h (oₗ a z) (yₗ a z) (wₗ a z) (p a z)) := by
  let μ(i:Cast F R h):= Cast.judge F R i; let M(i:Cast F R h):= Cast.push F R i
  have hh i:= Sold.smul (l.S_s F h) (paysUpon F R Jp l hG Ht Hw' hv h (M i))
    (fixed (μ i).toContinuousLinearMap Hp)
  apply (Sold.sum (x:=Finset.univ) (hw:=hq.joint (by
       filter_upwards [hq,l.large.pos] with a ha hr z hz; exact mul_nonneg (ha z hz).2 (inv_nonneg.mpr (pow_nonneg (hr z hz|>.le) _))))
       (fun i _=> hh i)).congr
  intro a z
  let D := upon (Vₗ a z) h (oₗ a z) (yₗ a z) (wₗ a z); refine Eq.trans ?_ (congrArg D (Cast.produce F R (p a z)))
  rw [map_sum]; apply Finset.sum_congr rfl; intro i _; exact (map_smul D _ _).symm

lemma homeStable (h:ℕ) (Hh:Coat F R Jp h){ξ:A→B→Sec G h}(hξ:∀ᶠ a in t,∀ z, U a z → width (ξ a z) ≤ 1) :
    gapₗ (fun _ _=>1) (fun a z=> upon (Vₗ a z) h (oₗ a z) (yₗ a z) (wₗ a z) (assign Jp (tinyₗ a z) h (ξ a z))) := by
  let D a z := upon (Vₗ a z) h (oₗ a z) (yₗ a z) (wₗ a z)
  let μ (i:Cast F R h) a z:=coatRead F R Jp (tinyₗ a z) i (ξ a z)
  have H₀ (p : Cast F R h) : gapₗ (fun a z=> (s a z ^ Cast.cost F R p)⁻¹) (fun a z=> D a z (Cast.push F R p)):= by
    apply (paysUpon F R Jp l hG Ht Hw' hv _ (R.actor _ p.snd)).price
    apply l.common.mono; intro a h z hz; apply le_of_eq; apply congrArg norm; exact
      upon_rise F R (Cast.costs F R p) _ (Purchase.viewer (P a z)) (oₗ a z) (yₗ a z) (wₗ a z) (h z hz).2
  have H (p:Cast F R h):= (H₀ p).smul (l.S_s F _) (earnFrom F R Jp l.tiny p Hh hξ)
  have hp (p:Cast F R h) : gapₗ (fun _ _=>1) (fun a z=> μ p a z • D a z (Cast.push F R p)) := by
    apply (H p).more (l.tiny.logs.mono fun a ha z he=>zero_le_one.trans (ha z he))
    refine l.setting.mono ?_; intro a ha z hz; obtain ⟨hr,hs,h,hg⟩:= ha z hz
    rw [← div_eq_mul_inv]; exact (div_le_one (pow_pos (hr.trans_le hs) _)).mpr (pow_le_pow_left₀ hr.le hs _)
  apply (Sold.sum (l.properO F (Eventually.of_forall fun _ _ _=>zero_le_one)) (x:=Finset.univ) (fun i _=>hp i)).congr
  intro a z; refine Eq.trans ?_ (congrArg (D a z) (Cast.produce F R (assign Jp (tinyₗ a z) h (ξ a z))))
  rw [map_sum]; exact Finset.sum_congr rfl (fun i _=> ((D a z).map_smul _ _).symm)

omit [Fintype I] in
lemma phaseStable (h:ℕ) (Hh:Coat F R Jp h){ξ:A→B→Sec G h}(hξ:∀ᶠ a in t,∀ z, U a z → width (ξ a z) ≤ 1) :
    gapₗ s (fun a z=> upon (Vₗ a z) h (oₗ a z) (yₗ a z) (wₗ a z) (assign Jp (tinyₗ a z) h (ξ a z)) -
      upon S h (oₗ a z) (yₗ a z) (wₗ a z) (assign Jp (tinyₗ a z) h (ξ a z))) := by
  let T a z:Purchase F Unit J := {(P a z) with x:=0}
  have ht : Labor M δ t U L s T := ⟨l.tiny,l.large,l.trailbound,l.setting.mono fun a ha z hz=> by
    obtain ⟨hx,hy,H,hq⟩:= ha z hz
    refine ⟨hx,hy,⟨?_,H.zhome,fun i j ne=>(ne (Subsingleton.elim ..)).elim,H.zclear,H.away⟩,hq⟩
    intro i; change ‖(0:E4)‖ ≤ M; rw [norm_zero]; exact l.nonneg,l.nonneg,l.clearance⟩
  apply (phases (d:=fun _:Unit=>h) F R Jp ht hG Ht (fun _=>Hh) Hw' (u:=fun a z i=>ξ a z)
    (hξ.mono fun a ha z _=> ha z) hv).congr
  intro a z; change (_-_) = whole _ _ _ _ _ - whole _ _ _ _ _
  dsimp only; rw [show (T a z).head=sole (oₗ a z) from
    funext fun i=>by change Purchase.center (P a z)+ _ • (0:E4)=_; rw [smul_zero,add_zero]; rfl]; rfl

omit hG Hw' hv
include Hw hu
omit [Fintype J] in
lemma errorBudget (h:ℕ): gapₗ (fun a z=> tinyₗ a z^(h+1)) (fun a z=> LedgerR F d R h (leftₗ a z) (u₁ a z)) := by
  apply present F R Jp l.tiny Hw hu (l.properO F (l.tiny.pos.mono fun a ha z he=> pow_nonneg (ha z he|>.le) _)); intro p
  apply (pullNear l (CostedR F (low F R p) h R l.nonneg l.clearance Ht (actors F R p))
    (wage_ok _ _ _)).congr; intro a z; rw [settlePacket,settlePacket]; symm; let k:=actors (d:=d) F R p
  change R.packet h _ (fun i:I=> F.sector.derivatives.rise (Cast.costs F R (p i)) (k i)) _-_= _
  exact congrArg₂ (·-·) (packet_inclusion F _ _ _ R (fun i=>Cast.costs F R (p i)) k)
    (shadow_inclusion F _ _ _ R.port R.spans (fun i=>Cast.costs F R (p i)) k)

set_option maxHeartbeats 400000 in
omit [Fintype J] in
lemma cap_price (h:ℕ) (Hh:Coat F R Jp h): gapₗ (fun _ _=>1) (fun a z=> columns G h ((assign Jp (tinyₗ a z) h).symm
    (R.packet h (xₗ a z) (u₁ a z) (oₗ a z)))) := by
  let p a z:=R.packet h (xₗ a z) (u₁ a z) (oₗ a z)
  have money (i:Cast F R h): gapₗ (fun a z=>tinyₗ a z^(Cast.cost F R i)) (fun a z=>Cast.judge F R i (p a z)) := by
    apply (present (Φ:=fun a z=> (Cast.judge F R i).compMultilinearMap (packetCost F (xₗ a z) (oₗ a z) h R (d:=d)))
      F R Jp l.tiny Hw hu (l.properO F (l.tiny.pos.mono fun a ha z he=>pow_nonneg (ha z he|>.le) _)) ?_).congr
      (fun a z=> congrArg (Cast.judge F R i) (packetCost_apply (d:=d) F (xₗ a z) (oₗ a z) h R (u₁ a z)))
    intro q; let v:=actors (d:=d) F R q
    apply (pullNear l (CostedC F (low F R q) (Cast.cost F R i) R l.nonneg l.clearance Ht i.snd v)
      (compact_pay ..)).congr; intro a z; symm
    rw [LinearMap.compMultilinearMap_apply,packetCost_apply]; change
      Cast.judge F R i (R.packet h (xₗ a z) (fun i:I=> F.sector.derivatives.rise (Cast.costs F R (q i)) (v i)) _)=_
    rw [packet_inclusion,Cast.packet_judged]; rfl
  have hh (i: Cast F R h):= Sold.smul (l.properO F (l.tiny.pos.mono fun a ha z he=>
        inv_nonneg.mpr (pow_nonneg (ha z he|>.le) _))) (earnBack F R Jp l.tiny i Hh) (money i)
  let T a z:=((columns G h).toLinearMap ∘ₗ (assign Jp (tinyₗ a z) h).symm.toLinearMap)
  apply (Sold.sum (l.properO F (Eventually.of_forall fun _ _ _=>zero_le_one)) (x:=Finset.univ)
    (fun i _=> (hh i).more (l.tiny.logs.mono fun a ha z he=>zero_le_one.trans (ha z he)) (l.tiny.pos.mono
      (fun a ha z he=> (mul_inv_cancel₀ (pow_pos (ha z he) _).ne').le)))).congr
  intro a z; refine Eq.trans ?_ (congrArg (T a z) (Cast.produce F R (p a z))); rw [map_sum]; exact Finset.sum_congr rfl fun i _=>
    (map_smul (T a z) _ _).symm
include hG Hw' hv
lemma projection (h:ℕ): gapₗ (tariff h tinyₗ s) (fun a z=> whole (Vₗ a z) (xₗ a z) (u₁ a z) (yₗ a z) (wₗ a z)-
    upon (Vₗ a z) h (oₗ a z) (yₗ a z) (wₗ a z) (R.packet h (xₗ a z) (u₁ a z) (oₗ a z))) := by
  have hr:= dynamic F R Jp l hG Ht Hw' hv h (errorBudget F R Jp l Ht Hw hu h) (l.properO F (l.tiny.pos.mono
    (fun a ha z he=> pow_nonneg (ha z he|>.le) _)))
  have he:=hr.more (l.tiny.logs.mono fun a ha z he=> zero_le_one.trans (ha z he)) (w:=tariff h tinyₗ s) (by
    filter_upwards [l.setting] with a ha z he; unfold tariff; obtain ⟨hp,ht,_,_⟩:= ha z he;
    change 0<tinyₗ a z at hp; change tinyₗ a z ≤ s a z at ht; have hP:=hp.trans_le ht
    apply le_trans ?_ (le_add_of_nonneg_right (pow_nonneg (div_pos hp hP|>.le) _)); rw [← div_eq_mul_inv]; apply
      (div_le_iff₀ (pow_pos hP _)).mpr; rw [mul_comm (s a z),← pow_succ]; gcongr)
  apply ((shadow_norm F R Jp l hG Ht Hw Hw' hu hv h).sub (l.properT F h) he).congr; intro a z
  rw [settlePacket,map_sub,discrepancy]; abel
end YM.Integration.GradedFar.Fork
