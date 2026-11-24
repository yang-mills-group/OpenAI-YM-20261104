import YM.FormalBulk08.Sierra.Storm

/-! Core induction. Upper occupancy θ rate. Neither supp W.Profile nor
Θ input width lost over iteration. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Dove Spruce Elm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices} {X I:Type}{E m r u l R:ℕ}{θ α:ℝ}{W:Lab G K X}
variable {Y T:X→Pot G}{ρ:ChartRatio G}
variable (h:Weather W u R E)(hp:Lab.Use W ρ E)(hs:G.Simple)(hv:LocalRatio ρ)(a:hue G)(C P Q:Pin W.scrolls)(o: Trail W C a)
variable {g:X→ℝ}
lemma workup (P:ℕ→ℕ→Prop)(E l:ℕ)(h:∀ e k,e≤E→0<k → k≤ l+e →(∀ j m,precede e k j m→0< m →m ≤ l+j→P j m)→P e k):∀ e k,e≤E → 0<k→ k≤ l+e →P e k:= by
    let Q i j:=0<j→P i j; have hp:∀ e k,e≤E→ k≤ l+e→Q e k:=goyal Q E l (fun i j hi hj he=>fun hb=> h i j hi hb hj fun n m ht ho hv=> he n m ht hv ho); exact fun e k he hk hn=> hp e k he hn hk
variable (hm:∀ i,C.N i≤ P.N i)(hM:∀ i,P.N i≤Q.N i)(hg:∀ i,0≤g i)(ht:∀ i,Ritual (T i) l)(hy:∀ i,Ritual (Y i) l) (hl:l≤R)(he:θ<1/2)
include h hp hs hv hm hg ht hl he
lemma spilt (hz:∀ e≤E,∀ r,0<r → Wake ((sage C).reach (peak C)) u (fun i=>o.rate (peak C i)) (fun i=> o.root (peak C i)) g (fun i=>T i e r)):∀ e≤E,∀ r,0<r → Wake (sage C) u o.rate o.root (fun i=>g i.a*Degree θ i) (fun i=>satCamp ρ l a T C P i e r):= by
    let t i:=satCamp ρ l a T C P i; have hp'(i): Ritual (t i) l:= sandpiper _ _ _ _ _ _ hm hp hv hs ht i
    let U(e k:ℕ):Prop:= Wake (sage C) u o.rate o.root (fun i=>g i.a*Degree θ i) (fun i=> t i e k); have h':θ≤1:= by linarith
    have h0 i k (hz:l+i<k):U i k:= by unfold U; simp_rw [show ∀ j,t j i k=0 from fun j=>Classical.byContradiction fun ht=>not_lt_of_ge ((hp' j).young _ _ ht) hz]; exact bear_void ..
    suffices ∀ i j,i≤ E→0<j→j≤l+i →U i j from fun i hi r hk=> by by_cases hb:r≤l+i; exact this _ _ hi hk hb; exact h0 _ _ (lt_of_not_ge hb)
    apply workup; intro e r hE hb hr ih; have hU i j (hi:precede e r i j)(hv:0<j): U i j:= by by_cases he:j≤l+i; exact ih i j hi hv he; exact h0 _ _ (lt_of_not_ge he)
    apply addendum (α:=1/2) (U:=fun i=>t i e r) hp.liable he h' hg
    · have hG(i:Turn C): 0≤g i.a* Dove.bump θ i:= mul_nonneg (hg _) (ratioR_pos ..).le
      have H0:= noel (h.sails.reach (fun i:Turn C=> i.toLeaf)) (fun i=>o.cap i.bed) (fun i=>o.cap i.ups) o.anchor hb hE hG (budge C P P hm (fun _=>le_rfl) hp hv a hs) (stillW h C P.N hE hb (by omega) hl) (fun i=> hp' i.ups) (fun j k ht he=> wax Turn.ups (up_age C hp.liable) (U:=fun i=> t i j k) (g:=fun i=>g i.a* Degree θ i) (hU j k ht he))
      simp_rw [show ∀ i:Turn C,t i.bed=_ from fun i=>score ρ l a T C P i,o.link];exact H0
    simp_rw [show ∀ i,t (peak C i)=_ from fun i=> at_top ρ l a T C P i]; exact hz e hE r hb

include hy hM
lemma shorn (hz:∀ e≤E,∀ r,0<r → Wit ((sage C).reach (peak C)) u (fun i=>o.rate (peak C i)) (fun i=>o.root (peak C i)) (hill C P hm) g (fun i=> T i e r) (fun i=> Y i e r)) : ∀ e≤E,∀ r,0<r → Wit (sage C) u o.rate o.root (fun i=>hill C P hm i.a) (fun i=>g i.a*Degree θ i)
   (fun i=>satCamp ρ l a T C P i e r) (fun i=> satCamp ρ l a Y C Q i e r):= by
    let t i:=satCamp ρ l a T C P i; let S i:=satCamp ρ l a Y C Q i; let δ:= hill C P hm;let g' i:=δ i*g i; have hG i:0≤g' i:=mul_nonneg (limb_pos ..) (hg i)
    have hp'(i):Ritual (t i) l:=sandpiper _ _ _ _ _ _ hm hp hv hs ht i; have hmk i:=(hm i).trans (hM i);have hq'(i): Ritual (S i) l:= sandpiper _ _ _ _ _ _ hmk hp hv hs hy i
    obtain hT:= spilt h hp hs hv a C P o hm hg ht hl he (fun i hi j hv=>(hz _ hi _ hv).1); obtain hS:= spilt h hp hs hv a C Q o hmk hg hy hl he (fun i hi j hv=>(hz _ hi _ hv).2)
    let b(i:Deck C):=g i.a*Degree θ i; let U(e k:ℕ):Prop:= Wit (sage C) u o.rate o.root (fun i=>δ i.a) b (fun i=> t i e k) (fun i=>S i e k)
    have h0 i k (hz:l+i< k):U i k:= by unfold U; simp_rw [show ∀ j,t j i k=0 from fun j=>Classical.byContradiction fun ht=> not_lt_of_ge ((hp' j).young _ _ ht) hz,show ∀ j,S j i k=0 from fun j=> Classical.byContradiction fun ht=>not_lt_of_ge ((hq' j).young _ _ ht) hz]; exact mates_void ..
    suffices ∀ i j,i≤E→0<j→ j≤l+i→U i j from fun i hi r hk=> by by_cases hb:r≤l+i; exact this _ _ hi hk hb; exact h0 _ _ (lt_of_not_ge hb)
    apply workup;intro e r hE hb hr ih; have hU i j (hi:precede e r i j)(hv:0<j): U i j:= by by_cases he:j≤l+i; exact ih i j hi hv he; exact h0 _ _ (lt_of_not_ge he)
    refine ⟨hT e hE r hb,hS e hE r hb,?_⟩; let P' (i:Deck C) := t i e r-S i e r; have hW: Wake (sage C) u o.rate o.root (fun i=>g' i.a*Degree θ i) P' := by
       apply addendum (α:=1/2) hp.liable he (by linarith) hG
       · have hG (i:Turn C):0≤ g i.a*Dove.bump θ i:=mul_nonneg (hg _) (ratioR_pos ..).le
         have Hp:= tote (h.sails.reach (fun i:Turn C=>i.toLeaf)) (fun i=>o.cap i.bed) (fun i=>o.cap i.ups) o.anchor hb hE hG (budge C P Q hm hM hp hv a hs) (stillW h C P.N hE hb (by omega) hl) (fun i=>hp' i.ups) (fun i=> hq' i.ups) (fun j k hi hv=>waxy Turn.ups (up_age C hp.liable) (g:=b) (U:=fun i=>t i j k) (Q:=fun i=> S i j k) (hU j k hi hv)) (wax Turn.ups (up_age C hp.liable) (U:=fun i=>S i e r) (g:=b) (hS e hE r hb))
         unfold g' P';simp_rw [o.link,show ∀ i:Turn C,t i.bed=_ from fun i=>score ρ l a T C P i,show ∀ i:Turn C,S i.bed= _ from fun i=>score ρ l a Y C Q i, mul_assoc]; exact Hp
       unfold P'; simp_rw [show ∀ i,t (peak C i)=_ from fun i=> at_top ρ l a T C P i,show ∀ i,S (peak C i)=_ from fun i=>at_top ρ l a Y C Q i]; exact rivals (hz e hE r hb)
    unfold Wake Whey g' at hW; simp_rw [mul_assoc] at hW;exact hW
end YM.FormalBulk08.Sierra
