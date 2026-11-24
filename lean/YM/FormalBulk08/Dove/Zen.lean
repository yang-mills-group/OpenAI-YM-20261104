import YM.FormalBulk08.Dove.Violet

/-! Recursion from top. NO period arguments. Before extent scalar gates. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X:Type}{G:Gauge}{K:KernelChoices}{E:ℕ}
variable (V: Levels G)(F:∀ i,Lodge (V.clock.op i 0).patch)(h:∀ i,(V.clock.op i 0).patch.Branches K G)(ρ:ChartRatio G)(a:hue G)

def voyage : ℕ→ℕ→Pot G
   | 0,_=>Enter G
   | n+1,i => taxi ρ a (stageHop V i (flying V n (i+1))) (F i) (h i) (voyage n (i+1))
def model (N i:ℕ): Pot G:= voyage V F h ρ a (N-i) i
lemma leaves (N): model V F h ρ a N N= Enter G:= by rw [model,Nat.sub_self,voyage]
lemma through (N i)(he:i<N): model V F h ρ a N i= taxi ρ a (destination V N i) (F i) (h i) (model V F h ρ a N (i+1)):=by
   unfold model; rw [show N-i=N-(i+1)+1 by omega, voyage];rfl
lemma genu (hp:LocalRatio ρ)(hs:G.Simple){N i}(he:i≤N): FrameV (model V F h ρ a N i) (pink K.penalty (location V N i)):= by
    induction he using Nat.decreasingInduction with
    | self=> rw [leaves, loc_top]; exact filing _ _ K.penalty_pos (V.clock.adm _)
                                                 -- insert
    | of_succ i ht ih=>rw [through V F h ρ a N i ht, loc_land V N i ht]; let P:=destination V N i; exact rulecraft_full a _ (creed P _ _ _ _ ih.toStory (V.clock.adm _) hp) K.penalty_pos (V.clock.adm _) hs

-- chunk recurrence induction invokes budgets, t,J move
variable (W:Lab G K X)
namespace Lab
def saga (x:X):= model (W.V x) (W.wood x) (W.toEmpire.bill x) ρ a
-- Lean declaration order check
variable {C:Pin W.scrolls}
abbrev instory (M:X→ℕ)(i: Deck C):= saga ρ a W i.a (M i.a) i.b
abbrev eagle (x: Deck C):= W.windowD x.toLeaf
-- induction on e and reverse distance from maximal val fence
omit W in
lemma survey (P:ℕ→ℕ→Prop)(E:ℕ)(h:∀ e r,e≤E→1≤r→ r≤e+2 →(∀ j m,1≤m→ m≤j+2→ precede e r j m→ P j m)→ P e r) :∀ e r,e≤E→1≤r→ r≤e+2→ P e r:= by
   suffices ∀ e, e≤E→∀ r,1≤r→ r≤e+2 → P e r from fun e r he=>this e he r
   intro e he; induction e using Nat.strong_induction_on with
   | _ e ih=>
     have ht (b:ℕ):∀ r,b+r=e+2→1≤r→ P e r:= by
        induction b using Nat.strong_induction_on with
        | _ b h₁=>
          intro r hu hr; apply h e r he hr (by omega); intro j m hm hz hh; obtain hh|⟨rfl,hR⟩:= hh
          · exact ih j hh (hh.le.trans he) m hm hz
          exact h₁ (j+2-m) (by omega) m (by omega) hm
     exact fun r hr hu=>ht (e+2-r) r (by omega) hr
-- API `hp Cost` all positive r
variable {W ρ}(C:Pin W.scrolls)(u:Use W ρ E)(v:LocalRatio ρ)(hs:G.Simple)
include u v hs
lemma absolute :∀ e r,e≤ E → 1≤ r → r≤ e+2 → Cost (sage C) (fun _=> fame _) (W.eagle) (fun i=>instory ρ a W C.N i e r):= by
    have hf i:= genu (W.V i.a) (W.wood i.a) (W.toEmpire.bill i.a) ρ a v hs (N:=C.N (i:Deck C).a) i.cap
    apply survey; intro e r he hr hk H
    by_cases h1:r=1
    · subst r; simp_rw [show ∀ i:Deck C, instory ρ a W C.N i e 1=0 from fun i=> pillar (hf i).toStory e];apply cost_void
    cases r with
    | zero=>omega
    | succ m=>
      by_cases z:e=0
      · subst e
        obtain rfl:m=1:= by omega
        have hx:= u.structural.reach (fun i:Deck C=> i.toLeaf); exact ⟨_,hx,fun x=> (show Bail (fame _) (W.eagle x) (instory ρ a W C.N x 0 2) _ by rw [show instory ρ a W C.N x 0 2=_ from (hf x).ink]; exact (W.turn_quota u x.toLeaf).seat _)⟩
      let U:=instory (C:=C) ρ a W C.N
      let T(x:Turn C):= U x.ups
      have hx(x): FrameV (T x) (pink K.penalty (W.trail C.N x)):= hf x.ups
      have hX:= up_age C u.liable
      have hp:floor_cost (tide C) W.stub T e (m+1):=fun j i l hz h=> Cost_lift (g:=Turn.ups) hX (H j i l hz h)
      obtain ⟨B,c,hK,Q⟩:= Aster.direct_line (Freight_from u C) (flight_bill u C C.N (fun _=>le_rfl)) v (fun i=>(W.V i.a).clock.adm i.b) hx (punctual u C C.N (fun _=>le_rfl)) a (by omega) he (show 1≤m by omega) hk hp
      refine actuality u.liable (show 0<(1/2:ℝ) by norm_num) ?_ c (fun i b h=> ?_)
      · have hu:=u.structural.reach (fun i:X=> (peak C i).toLeaf); refine ⟨_,hu,fun x=> ?_⟩; change Bail _ _ (saga _ _ _ x (C.N x) (C.N x) e (m+1)) _; rw [saga,leaves];exact (W.turn_quota u (peak C x).toLeaf).seed _ he _ hk
      change Bail (fame _) _ (saga _ _ _ i.a (C.N i.a) i.b e (m+1)) _; unfold saga; rw [through _ _ _ _ _ (C.N i.a) i.b i.head]; exact Q _ _ h
end Lab
end YM.FormalBulk08.Dove
