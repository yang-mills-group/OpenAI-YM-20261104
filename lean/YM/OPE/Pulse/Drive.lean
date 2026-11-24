import YM.OPE.Pulse.Torch
import YM.MergeProof.South.Wakes
/-!
# Supply singleton jobs ready up to their next events

Port of MergeProof/South/Wakes.chapter, with pepper accounting left in place.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J : Type*}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side} {d:ℕ}
variable (H:History G) (A:Hol G){F:Labels.Frame G d}(T:SectionData F)
   (ζ ψ:ℕ→ℝ)(k j N p:ℕ)
set_option quotPrecheck false
local notation "P"=> H.levels.budget
local notation "Γ"=> (fun m=>(H.levels.params m).columns)
local notation "R"=> H.rep N p
local notation "X"=> alto H
variable (a:Motion)(o:∀ m:ℕ, Site (H.S.side m p))(w:ℕ→ℝ)
   (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
open Relay
variable (Z:∀ i:ℕ,Coefficient F (H.S.side i p))(φ:ℕ→ℝ)
local notation "g!"=> liftK H N p a o Z
local notation "f!"=> liftF H T N p a o Z
structure Drive (S:∀ i:ℕ,Lamp G (H.S.side i p)) (δ:j≤N) : Prop where
   drives i:k ≤ i→∀ hi:i<j, Debt H N p (D N p i (hi.trans_le δ)) (w (i+1)) (o (i+1)) (S (i+1)) (S i)
namespace Debt
variable {H N p k D w o}
lemma remap {q : GaugeDoor (H.rep N p (k+1)) (H.rep N p k)}{x:ℝ}{y:Site (H.S.side (k+1) p)}{u v:Lamp G (H.S.side (k+1) p)}{u' v':Lamp G (H.S.side k p)} (h:Debt H N p q x y u u')(ht:H.Selected)(hk:k<N)
    (he:u.watch=v.watch)(hv:u'.watch=v'.watch)(hc:u.rays (R (k+1))=v.rays (R (k+1)))(hh:u'.rays (R k)=v'.rays (R k)) : Debt H N p q x y v v':=by
     obtain ⟨m,v,t,z,hv',hT,hh',hK,hI⟩:=h.votes -- name shadow
     refine ⟨⟨m,v,t,z,hv',he ▸ hc ▸ hh ▸ hT,hh',hK,hI⟩,?_⟩
     -- rewrite disburse
     have hz{n : Side}(u v:Lamp G n)(A':Rep G n){x t:ℝ}(h:A'.activities.Valid A'.p x t)(he:u.watch=v.watch)(hv:u.rays A'=v.rays A'): u.disburse A'=v.disburse A':= by unfold Lamp.disburse; rw [he]; exact coin_port A' v.watch u.lit v.lit hv h
     rw [← hz _ _ _ (ht.represents N p k hk.le).good.labels hv hh, ← hz _ _ _ (ht.represents N p _ hk).good.labels he hc]; exact h.arrives
end Debt
variable {g:∀ i:ℕ,ℕ → Config G (H.S.side i p)→ℂ}
-- costume
structure Captor (δ:j ≤ N) : Prop where
    stocked i:k ≤ i→i ≤ j→ Dominated (g i)
    sways m:k ≤ m→∀ hN:m<j,∃ (μ:Set Wing) (v:ℂ) (s t:ℝ), μ.Finite ∧ 2*w (m+1)*s ≤ 1 ∧ w (m+1)*t ≤1 ∧ w (m+1)*‖v‖≤1 ∧ Tale μ (o (m+1)) (o m) 1 (f! (m+1)) (profile (R (m+1)).activities (g (m+1))) (profile (R m).activities (g m)) v s t (D N p m (hN.trans_le δ))
    feeds m : k ≤ m → m<j → coin (R m) (f! m) (g m)= (H.levels.clock.op m p).push ((R (m+1)).beta) (coin (R (m+1)) (f! (m+1)) (g (m+1)))
lemma driven (h:H.Selected)(he:T.Sound A)(hk:j ≤ N)(hh:Club H A T ζ ψ k (j:=j) N p w D Z φ hk)(hw:∀ m:ℕ,k ≤ m → m≤j → 0 < w m)(hp:∀ m:ℕ,k ≤ m→m<j→w (m+1) ≤ w m)
    (hQ:Fiesta H F ζ ψ k) (hO:∀ m:ℕ,k ≤ m→m<j→ o (m+1)=(H.levels.clock.op m p).ratio.embed (o m))
    (hD:∀ m:ℕ,k ≤ m →∀ hm:m<j, SoundDoor (H.levels.clock.op m p) (D N p m (hm.trans_le hk))) : ∃ g:∀ m:ℕ,ℕ → Config G (H.S.side m p)→ℂ,
        Captor H T k j N p a o w D Z (g:=g) hk ∧ ∀ m:ℕ,k ≤ m→m≤j→profile (R m).activities (g m)= g! m:=by
   choose! g hG hd hx' using fun m:ℕ=> fun hK:k ≤ m=> fun hn:m≤j=> sparkling H A T (Z m) a (o m) (X m d) h 0 (hn.trans hk) he (hh.ticks m hK hn|>.1) (hh.ticks m hK hn|>.2)
   refine ⟨g,⟨hd,?_,?_⟩,fun m he hx=>(hG m he hx).symm⟩
   · intro m hm hm'; let S:= H.levels.clock.op m p; let c:= S.ratio.embed (o m); have hK:= hD m hm hm'; obtain ⟨_,s,hS,hL⟩:=hh.votes m hm hm'; let v:ℂ:=((H.S.block m).val:ℂ)^d
     let τ:= ((H.levels.clock.op m p).ratio.embed (o m)); obtain ⟨z⟩:= (h.represents N p (m+1) (hm'.trans_le hk)).good.labels.moves a.1 (S.ratio.embed (o m)); have hF:= hO m hm hm'
     have hL':= hL.gain hK a (o m) z (show scalar a v=v from by unfold scalar v; split <;> simp) |>.pitch (X (m+1) d) (X m d) (alto_at H m d)
     simp only [← hF, show affine a.1 (o m) 0=o m by simp [affine], show affine a.1 (o (m+1)) 0=o (m+1) by simp [affine]] at hL'
     have hx : k ≤ m+1:= hm.trans m.le_succ ; let c:ℝ:=Γ m; let d':ℝ:= orbitCost F*(ψ m+2*Γ (m+1))
     have hd : 2 ≤ d':=by unfold d'; exact le_trans (by linarith only [hQ.tap m hm,(H.levels.params (m+1)).columns_ge] : (2:ℝ) ≤ ψ m+2*Γ (m+1)) (le_mul_of_one_le_left (add_nonneg (hQ.tap m hm) (mul_nonneg zero_le_two (zero_le_one.trans (H.levels.params (m+1)).columns_ge))) (orbitCost_one_le ..))
     let r:= φ (m+1); have hr: 0≤ r:= rem_nonneg ((hh.ticks _ hx hm').2)
     let x:=(Z (m+1)).x;have hv : weighted H F (ψ m) (m+1) x r ≤ d'*(r+F.coeffSize x):=by
       unfold Relay.weighted; rw [mul_add d']; have he : orbitCost F*F.coeffSize x*(ψ m+2*Γ (m+1))=d'*F.coeffSize x:=by unfold d'; ring
       rw [he,add_comm]; exact add_le_add (mul_le_mul_of_nonneg_right hd hr) le_rfl
     let u':= w m; let t':= w (m+1); let y:=‖alto H m d‖; let y':=‖alto H (m+1) d‖; have hu':0 ≤ u':= (hw _ hm hm'.le).le; have ht':0 ≤ t':= (hw _ hx hm').le
     have hJ:2*t'*(y'*weighted H F (ψ m) (m+1) x r)≤1:=by
       apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (norm_nonneg _)) (mul_nonneg zero_le_two ht'))
       exact le_trans (le_of_eq (b:=2*d'*(t'* y'*(r+F.coeffSize x))) (by ring)) ((mul_le_mul_of_nonneg_left (hh.rates _ hx hm') (show 0 ≤ 2*d' from by linarith only [hd])).trans (le_trans (le_of_eq (by unfold d';ring):_ ≤ 2*orbitCost F*(ψ m+2*Γ (m+1))*ζ (m+1)) (hQ.room m hm)))
     have hI : t'*(y*φ m)≤1:=by
       have hs:0 ≤ φ m:= rem_nonneg ((hh.ticks m hm hm'.le).2); have hζ': u'*y*φ m ≤ ζ m:= le_trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Work.G08.size_nonneg F (Z m).x)) (mul_nonneg hu' (norm_nonneg _))) (hh.rates m hm hm'.le)
       exact le_trans (mul_le_mul_of_nonneg_right (hp m hm hm') (mul_nonneg (norm_nonneg _) hs)) ((le_trans (le_of_eq (Eq.symm (mul_assoc ..))) hζ').trans ((le_mul_of_one_le_right ((mul_nonneg (mul_nonneg hu' (norm_nonneg _)) hs).trans hζ') (H.levels.params _).columns_ge).trans (hQ.coin m hm)))
     refine ⟨_,alto H (m+1) d* scalar a (x 0),_,_, hS.image (Wing.labelRoute z), hJ,hI,?_,?_⟩
     · rw [norm_mul,Motion.norm_scalar,← mul_assoc]; have hu := (mul_le_mul_of_nonneg_left (le_trans (show ‖x 0‖ ≤ F.coeffSize x from single_le_sum (fun i _=> norm_nonneg (x i)) (mem_univ 0)) (le_add_of_nonneg_left hr)) (mul_nonneg ht' (norm_nonneg _))).trans (hh.rates _ hx hm'); exact hu.trans ((le_mul_of_one_le_right ((mul_nonneg (mul_nonneg ht' (norm_nonneg _)) (norm_nonneg _)).trans hu) (H.levels.params _).columns_ge).trans (hQ.coin _ hx))
     simp only [← hG m hm hm'.le, ← hG (m+1) hx hm']; exact hL'
   intro m hm ht; have hy:= hh.ticks (m+1) (hm.trans m.le_succ) ht; let E:= (Z (m+1)); obtain ⟨ha,hP⟩:=hy
   have hK : Integrable (E.density 0 T (R (m+1))) (prior G _):=play_integrable H N h (ht.trans_le hk) ha hP
   simp_rw [liftF,hx' m hm ht.le,hx' (m+1) (hm.trans m.le_succ) ht, hO m hm ht]; exact starship H a (o m) _ _ d (hh.votes m hm ht|>.1) hK _ (alto_at H m d)
lemma beam (h:H.Selected)(he:T.Sound A)(hk:j ≤ N)(hh:Club H A T ζ ψ k (j:=j) N p w D Z φ hk)(hw:∀ m:ℕ,k ≤ m → m≤j → 0 < w m)(hp:∀ m:ℕ,k ≤ m→m<j→w (m+1) ≤ w m)
    (hQ:Fiesta H F ζ ψ k) (hO:∀ m:ℕ,k ≤ m→m<j→ o (m+1)=(H.levels.clock.op m p).ratio.embed (o m))
    (hD:∀ m:ℕ,k ≤ m →∀ hm:m<j, SoundDoor (H.levels.clock.op m p) (D N p m (hm.trans_le hk))) : ∃ S:∀ m:ℕ,Lamp G (H.S.side m p), Drive H k j N p o w D S hk ∧ ∀ m:ℕ,k ≤ m→m≤j→(S m).watch=f! m ∧ (S m).rays (R m)= g! m ∧ Integrable ((S m).disburse (R m)) (prior G _):=by
    obtain ⟨g,hF,hG⟩:=driven H A T ζ ψ k j N p a o w D Z φ h he hk hh hw hp hQ hO hD
    let S m:= if hx:k ≤ m ∧ m≤j then Lamp.mk (f! m) (g m) (hF.stocked m hx.1 hx.2) else default; have hv m (he:k ≤ m)(hf:m≤j): (S m).watch=f! m ∧ (S m).sparks=g m:=by unfold S; simp [he,hf]
    refine ⟨S,⟨fun i hi hN=>?_⟩,fun m he' hf=> ⟨(hv m he' hf).1,by unfold Lamp.rays; rw [(hv _ he' hf).2,hG m he' hf],?_⟩⟩
    · obtain ⟨μ,v,l,t,he,hu,hΨ,hW,hT⟩:= hF.sways i hi hN; have ht:k ≤ i+1:= hi.trans i.le_succ; let T':=H.levels.clock.op i p; have ho:T'.ratio.parent (o (i+1))=o i:=by rw [hO i hi hN]; exact T'.ratio.embed_parent _
      refine ⟨⟨μ,v,l,t,he, ?_, hu,hΨ,hW⟩,?_⟩
      · unfold Lamp.rays; rw [(hv _ ht hN).2, (hv _ hi hN.le).2, (hv _ ht hN).1]; rw [show (H.levels.clock.op i p).ratio.parent (o (i+1))= _ from ho]; exact hT
      unfold Lamp.disburse; rw [(hv _ hi hN.le).1,(hv _ hi hN.le).2,(hv _ ht hN).1,(hv _ ht hN).2,hF.feeds i hi hN]
    obtain ⟨X',hz,hχ,hδ⟩ := sparkling H A T (Z m) a (o m) (X m d) h 0 (hf.trans hk) he (hh.ticks m he' hf).1 (hh.ticks m he' hf).2
    unfold Lamp.disburse; rw [(hv m he' hf).2,(hv m he' hf).1, coin_port _ _ (hF.stocked m he' hf) hχ ((hG _ he' hf).trans hz) ((h.represents _ _ _ (hf.trans hk)).good.labels),liftF,hδ]; exact (tint _ _ _ (play_integrable H N h (hf.trans hk) (hh.ticks m he' hf).1 (hh.ticks m he' hf).2)).smul _
end YM.MergeProof.Ribbons.ManyCopies.Patrol
