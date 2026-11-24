import YM.LocalLTE.Sail.Rally
import YM.LocalLTE.Sail.Front
import YM.LocalLTE.XPre.Runway
/-! Aperture inlets for the ACTUAL mark comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Sail
open Filter Function Finset Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open GridApprox.Nil Extra.Trajectories Progress.DirectedRecipe MergeProof Menu Accent Push.AbsoluteSums
open Overlay Planned.GuardedAtom Guard LocalLTE.XPhase LocalLTE.Port
open PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V J : Type} [DecidableEq V] [Fintype V] [Fintype J]
variable (B:Census V) {G:Gauge}{n:Side} {P:Rep G n}
omit [Fintype V] in
lemma towers (f:J→ Marker.Poly B)(h:∀ i,rises (f i)): rises (∑ i,f i):=by
   intro k hk; by_contra h'; rw [Poly.part_sum,sum_eq_zero (fun i _=> not_not.mp (mt (h i k) h'))] at hk; exact hk rfl
variable (f:J→Hat B P)
section
set_option quotPrecheck false
local notation "S" => {i:J// 2≤ (f i).s.val.card}
-- torus GUIDE pruning
omit [Fintype V] in
lemma eraseT (q :J→ Marker.Poly B) (hq:∀ i j,j ≠ (f i).s → (q i).part j=0) (ht:rises (∑ i,q i)) : (∑ i:S, q i.val)=∑ i,q i:=by
    ext k; rw [Poly.part_sum]; by_cases h:2 ≤ k.val.card
    · rw [Poly.part_sum, ← show ∑ i∈Finset.univ.image (fun i:S=>i.val),(q i).part k= ∑ i:S,(q i.val).part k from Finset.sum_image (Subtype.val_injective.injOn)]
      refine sum_subset (subset_univ _) fun i _ hi=>?_ ; refine hq i k (fun h'=> ?_); exact hi (Finset.mem_image.mpr ⟨⟨_,show 2 ≤ _ from h' ▸ h⟩,Finset.mem_univ _,rfl⟩)
    rw [not_not.mp (mt (ht k) h)]; exact Finset.sum_eq_zero fun i _=>hq _ _ (fun he=>h (he.symm ▸ i.prop))
omit [Fintype V] in
lemma eraseN (K:Config G n)(i:Box n)(hp:rises (roll f K))(hv:rises (board f i K)): roll (fun j:S=>f j.val) K=roll f K ∧ board (fun j:S=>f j.val) i K=board f i K:=by
    rw [perfumes] at hp; rw [patron] at hv
    simp only [perfumes,patron]
    exact ⟨eraseT B f (fun i=> odour (f i) K) (fun l j hv=> (Poly.part_send ..).trans (if_neg hv)) hp, eraseT B f (fun a=> fragrance (f a) K i) (fun a j hx=> (Poly.part_send ..).trans (if_neg hx)) hv⟩
end
section
variable {m l p:ℕ} {M: Lotus.Leaf P}{κ:ℝ}{g: Config G n→ℝ}
lemma tall_ink (h:Fan.SoloInk M g κ p l)(hp:p ≤ m): Fan.SoloInk M g κ m l:=by
    obtain ⟨i,hi,hx,hV,d,h',j,e,t,hP,hT,hY,k,hk,a,H⟩:= h.health
    exact ⟨h.ink,h.reads,i,hi,hx,hV,d,h'.trans hp,j,e,t,hP,hT,hY,k,hk,a,AnalyticBridge.VerifiedReset.Collection.Price.rp_raise _ H (Nat.succ_le_succ hp)⟩ -- arg order check
lemma from_panel (h: Fan.Mind M g κ p l): Fan.SoloInk M g κ p l:=by
    obtain ⟨i,hi,hx,hV,ha⟩:= h.health; let Q:= (Labels.frames G).level 0
    refine ⟨h.ink,h.reads,i,hi,hx,hV,0,Nat.zero_le _,0,g,false,?_,?_,hx,ha⟩
    · simpa only [Labels.Frame.coeffSize,Pi.zero_apply,norm_zero,sum_const_zero] using! hx.1
    rw [map_zero]; have hp:(Port.scaleQ false) ∘ (0: Config G n→ℂ)=0:= funext fun _=> rfl; rw [hp,add_zero]
end
section
variable (q:Census V)
variable (I A D : Bands B P) (H: Support n→ Config G n→Poly B)(K: Box n→ Config G n→Poly B)
    (hr:Carton I.origins H K P.p.threshold)(hc:∀ U: Config G n, (∑' j,I.ray j U)=∑ i,H i U)(ht:XPhase.lightF B P I=K)
    {a b X Y d ε k y:ℝ} {m l:ℕ} (w:V→ℝ)
    (hA:A.Active)(hD:D.Active)(hP:A.Radial w a b X ε)(hQ:D.Radial w 0 Y d ε)(hX:Fan.Tabs P B I A D)(hE:Port.Shine B A m l k)(hm:HasSlots P.p P.activities)
include hr hc ht hA hD hP hQ hX hE hm
set_option maxHeartbeats 450000 in
lemma tendered (he:1≤y): ∃ (J:Type) (_:Fintype J) (p:J→ Hat B P)(F:J→ Config G n→ℝ)(Q:J→Prop),
    (∀ i,(p i).s.val.image I.origins ⊆ (p i).M.crest)∧ (∀ i,2≤ (p i).s.val.card)∧(∀ i,Q i→Fan.SoloInk (p i).M (F i) k m l∧∀ j,(p i).M.turn=Wing.logKey j→ (P.activities.reg j).support⊆ Animals.neighbors l (P.activities.reg j).site) ∧
     XPre.banks p Q y w ≤ Port.capacity P.p V b Y ε d y l ∧ (∀ U,roll p U=∑ i,H i U) ∧ ∀ i U,board p i U=K i U :=by
    have hy:0 ≤ y:= zero_le_one.trans he
    obtain ⟨p,h₀,_,⟨g,hg⟩,h,hU,hK⟩:= Port.collide A I D w hA hP hE hD hQ hX hm y hy
    let X:= Port.Mosaic A D l; let X':= {i:X// 2 ≤ (p i).s.val.card}; let T:X→_:= Sum.elim g (fun _=> fun _=>0)
    have hx:Menu.board p= XPhase.lightF B P I:= funext fun i=> funext fun U=> hK U i
    have he U i:=eraseN B p U i (show rises (roll p U) from by rw [hU,hc]; exact towers B _ (fun i=> (hr.exp i).2 U)) (show rises (board p i U) from by rw [hx,ht];exact (hr.flag i).2 U)
    refine ⟨X',inferInstance, fun i=> p i.val, T ∘ Subtype.val,(fun i=> Port.star A D i.val),fun i=>h₀ i.val,fun i=>i.prop,?_,?_,fun U=>?_,fun i U=>?_⟩
    · rintro ⟨i|i,hi⟩ hs; exact ⟨from_panel (hg.leads _), fun j h=>hg.price i j h⟩
      exact False.elim (Bool.noConfusion hs)
    · let a(i:X):= (if Port.star A D i then ActT w (p i) else y*ActT w (p i)); have hβ(i): P.p.mass (p i).M.crest (Menu.fare (p i) w)= ActT w (p i):=by unfold ActT Menu.fare BudgetPoint.mass; ring
      unfold XPre.banks; apply le_trans _ h
      calc
        _ = ∑ i:X', a i.val:= by refine Finset.sum_congr rfl fun i _=>?_ ; dsimp only; rw [hβ]; unfold a; split; rw [one_mul];rfl
        _ ≤ _:=by
           let f : X'→X:= Subtype.val
           rw [← show ∑ i∈Finset.univ.image f,a i= ∑ i:X',a i.val from Finset.sum_image Subtype.val_injective.injOn]
           apply Finset.sum_le_sum_of_subset_of_nonneg (f:=a) (Finset.subset_univ _)
           intro i _ _; unfold a; have ht:0≤ ActT w (p i):=(hβ i) ▸ mul_nonneg (Real.exp_nonneg _) (Menu.Crew _ hP.pure); split; exact ht;exact mul_nonneg hy ht
    · exact (he U (∅,∅)|>.1).trans ((hU U).trans (hc U))
    rw [show _ = board p i U from (he U i|>.2),hx,ht]
end
end YM.LocalLTE.Sail
