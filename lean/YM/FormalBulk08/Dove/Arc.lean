import YM.FormalBulk08.Dove.Zen

/-! Actual stability through all lengths. Uses floors separately and at zero order supplied metric. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E e r:ℕ}{W:Lab G K X}
namespace Lab
variable (C C':Pin W.scrolls)(u:Use W ρ E) (p:∀ x,C.N x≤ C'.N x)(v:LocalRatio ρ)(hs:G.Simple)(a:hue G)
def raiseD (i:Deck C):Deck C':= ⟨i.toLeaf,le_trans i.cap (p i.a)⟩
include u p v hs
lemma absolute_more (he:e≤ E)(hr:1≤r)(hk:r≤e+2): Cost (sage C) (fun _=> fame _) W.eagle (fun i=> instory ρ a W C'.N i e r):= (absolute a C' u v hs e r he hr hk).links (raiseD C C' p)
lemma final_dust: ∀ e r,e≤ E →1≤r→ r≤e+2 → Totem (sage C) (fun _=> fame _) W.eagle (Degree targetPower) (fun i=> instory ρ a W C.N i e r) (fun i=> instory ρ a W C'.N i e r):=by
   let M:=instory ρ a W (C:=C) C'.N; let U:=instory ρ a W (C:=C) C.N;
   have hA (x:Deck C): FrameV (U x) (pink K.penalty (location (W.V x.a) (C.N x.a) x.b)):= genu _ _ _ _ a v hs x.cap
   have hB (x:Deck C): FrameV (M x) (pink K.penalty (location (W.V x.a) (C'.N x.a) x.b)):= genu _ _ _ _ a v hs (x.cap.trans (p x.a))
   let V1 (x: Deck C) := setkin G (pink K.penalty (location (W.V x.a) (C.N x.a) x.b)); let V2(x:Deck C):= setkin G (pink K.penalty (location (W.V x.a) (C'.N x.a) x.b))
   have hV:Dust (sage C) (fun _=> fame _) W.eagle (Degree targetPower) (fun i=> V1 i-V2 i):= ⟨_,u.structural.reach (fun i:Deck C=>i.toLeaf),fun i=>(W.turn_quota u i.toLeaf).plus.le,fun i=> (W.turn_quota u i.toLeaf).rate _ _ _ _ i.cap (p i.a) rfl⟩
   apply survey; intro e r he hr hk H
   have ha:=absolute a C u v hs _ _ he hr hk; have hb:= absolute_more C C' u p v hs a he hr hk; refine ⟨ha,hb,?_⟩
   by_cases hX:r=1
   · subst r; simp_rw [show ∀ i:Deck C, instory ρ a W C.N i e 1=0 from fun i=>pillar (hA i).toStory _, show ∀ i:Deck C,instory ρ a W C'.N i e 1=0 from fun i=> pillar (hB i).toStory _,sub_self];apply dust_void
   by_cases ht:e=0
   · subst e; obtain rfl:r=2:=by omega
     change Dust _ _ _ _ (fun i=>U i 0 2-M i 0 2);simp_rw [(hA _).ink,(hB _).ink];exact hV
   cases r with
   | zero=>omega
   | succ m=>
      let Z := Turn.ups (C:=C); let P:=U ∘ Z; let T:=M ∘ Z
      have hh(i:Turn C):= hA (Z i); have hT(i):= hB (Z i)
      have hv (i:Turn C): 0≤ bump targetPower i := (bump_pos ..).le
      have hu:floor_dust (tide C) W.stub (bump targetPower) P T e (m+1):=fun j s l hz h=> Totem_lift (g:=Z) (up_age C u.liable) (H j s l hz h)
      obtain ⟨B,c,k,w⟩:= Aster.dusting (Freight_from u C) (flight_dust u C C'.N p) v (fun i=>(W.V i.a).clock.adm i.b) hh (punctual u C C.N (fun _=>le_rfl)) a (Nat.pos_of_ne_zero ht) he (by omega) hk hv hs hT hu (Cost_lift (g:=Z) (up_age C u.liable) ha) (Cost_lift (g:=Z) (up_age C u.liable) hb) (by
          have hx:Dust (tide C) (fun _=> fame _) W.sail (bump targetPower) (fun i=> V1 i.bed - V2 i.bed):= (hV.links (fun i:Turn C=> i.bed)).wanes (fun i=>by
              refine show ratioR (W.V i.a).S (C.N i.a) i.b targetPower ≤ ratioR (W.V i.a).S (C.N i.a) (i.b+1) targetPower from ?_; unfold ratioR; gcongr
              all_goals first|exact targetPower_pos.le|exact Schedule.strictAnti _ (by omega)| exact Schedule.a_pos ..|exact le_of_lt (Schedule.a_pos ..)| exact div_nonneg (Schedule.a_pos ..).le (Schedule.a_pos ..).le | exact StrictAnti.antitone (((W.V i.a).S).strictAnti) (Nat.le_succ _) )
          convert hx using 1; funext i
          unfold V1 V2; change _= setkin G (pink K.penalty (location _ _ i.b))-setkin G (pink K.penalty (location _ _ i.b)); rw [loc_land (W.V i.a) _ _ i.head,loc_land (W.V i.a) _ _ (i.head.trans_le (p _))]; rfl)
      refine vanishing u.liable (show targetPower < (1/2:ℝ) by unfold targetPower;norm_num) (by unfold targetPower;norm_num) ((ha.links (peak C)).minus (hb.links (peak C))) c k ?_
      intro x z hx
      change Bail (fame _) _ (saga ρ a W x.a (C.N x.a) x.b e (m+1) - saga ρ a W x.a (C'.N x.a) x.b e (m+1)) _; unfold saga; rw [through _ _ _ _ _ (C.N x.a) x.b x.head, through _ _ _ _ _ (C'.N x.a) x.b (x.head.trans_le (p _))]; exact w x z hx
end Lab
end YM.FormalBulk08.Dove
