import YM.OPE.Compatible.Assemblage.Stamp
/-!
# Engineering-scaled intervals on the track

Step not always continuing on one alignment. Keep history pricing
separate from eligibility of applying the actual tag mapping next.
Before leaving the exact track pay Blade *without* a constraint on
being migrated for the NEXT step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Stem
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge}{H:History G}{E:Hol G}{V:Type}[Fintype V][DecidableEq V]{N p d k j l:ℕ}
variable (P:Ensemble V){F:Labels.Frame G d}(Z:SectionData F) {O o:Track H V p}
variable {D:∀ N p i:ℕ,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i)} {v:ℕ→ℝ}
set_option quotPrecheck false
variable {Q:∀ i:ℕ, Coefficient F (H.S.side i p)}
-- on-axis motion actually earned in this interval.
structure Guided (Z:SectionData F)(E:Hol G)(H:History G)(N p k j:ℕ)(Q:∀ i:ℕ,Coefficient F (H.S.side i p))(D:∀ N p i:ℕ,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i))(w:ℕ→ℝ) : Prop where
   starts : k ≤ j
   paid : j ≤ N
   aff (i) : k ≤ i→ i ≤ j→ 0 < w i
   fits (i) : k ≤ i→ i ≤ j→ (Q i).Format 0 E (H.rep N p i) ∧ ∃ u:ℝ,(Q i).remBound 0 (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)) u
   spice (i) : k ≤ i→ i ≤ j→ w i * ‖alto H i d * ((Q i).x 0)‖ ≤ 1
   sits (i) : k ≤ i→ i<j → (Q i).density 0 Z (H.rep N p i)= blast H N p i d ((Q (i+1)).density 0 Z (H.rep N p (i+1)))
   waves i : k ≤ i→∀ hi:i<j, ∃ p':Set Wing,p'.Finite∧∃ t a:ℝ, 2*w (i+1)*(‖alto H (i+1) d‖*t) ≤ 1∧w (i+1)*(‖alto H i d‖ * a) ≤ 1 ∧ (Q i).remBound 0 (H.rep N p i) (Real.sqrt (H.levels.clock.forcedAllowance i)) a ∧ Tale p' 0 0 (((H.S.block i).val:ℂ)^d) ((Q (i+1)).exponentialEntry 0 Z (H.rep N p (i+1))) (profile (H.rep N p (i+1)).activities (Q (i+1)).forced) (profile (H.rep N p i).activities (Q i).forced) ((Q (i+1)).x 0) t a (D N p i (hi.trans_le paid)) -- augment if Leaf carol room doesn't rem t? can align t with charge
variable (h:Guided Z E H N p k j Q D v)
variable (hs:H.Selected)(hF:Z.Sound E)(hu :∀ i,k ≤ i→∀ hi:i<N,SoundDoor (H.levels.clock.op i p) (D N p i hi))
include h hs hF hu
lemma impress (hk:k ≤ l) (hl:l ≤ j)
    (X:Travel H V p)(ht:∀ i:ℕ,l ≤ i→ i ≤ j→ Stamp (N:=N) P Z (O i) (Q i) (X i))
    (hP:∀ i:ℕ,l ≤ i→ i ≤ j→ (X i).home=o i)(hm:Migrating H l p j o):Run P D N p l j O o X v:=by
    refine ⟨hl,h.paid,fun i hi hj=> h.aff i (hk.trans hi) hj,fun i hi hj=>(ht i hi hj).homes,hP,fun i hb hq=>?_⟩
    let N':= H.rep N p; have he : i+1 ≤ N:= hq.trans_le h.paid; let c:= alto H (i+1) d; let c':= alto H i d
    have hx : k ≤ i:= hk.trans hb; have he':=h.fits i hx hq.le
    obtain ⟨hf',a,ha⟩:= h.fits (i+1) (hx.trans i.le_succ) hq
    obtain ⟨pX,hC,t,a',hx',hw',hy,hT⟩:=h.waves i hx hq
    have hm':(H.levels.clock.op i p).ratio.embed ∘ (X i).home=(X (i+1)).home:=by rw [hP i hb hq.le,hP (i+1) (hb.trans i.le_succ) hq, hm.mare i hb hq]
    exact ⟨c*((Q (i+1)).x 0),one_hop P Z (Q i) (Q (i+1)) hs he hF hf' ha he'.1 hy (hu i hx he) hT (ht (i+1) (hb.trans i.le_succ) hq) (ht i hb hq.le) hC hm' (h.sits i hx hq) (h.spice (i+1) (hx.trans i.le_succ) hq) hx' hw'⟩
-- construct missing exact stamps from one output (given across all copies) or free entire. initialize. use x'n may collide.
lemma prints (hk:k ≤ l) (hl:l ≤ j)(X:Stem V G (H.S.side j p)) (ht:Stamp (N:=N) P Z (O j) (Q j) X)
    (hP:X.home=o j)(hm:Migrating H l p j o)(hy:∀ i,l ≤ i→ i ≤ j→ ∀ x,x≠P.v→ o i x=affine (P.move x).1 (O i x) (o i P.v)):
    ∃ Y:Travel H V p, Run P D N p l j O o Y v ∧ Y j=X ∧ ∀ i,l ≤ i→ i ≤ j→ Stamp (N:=N) P Z (O i) (Q i) (Y i):=by
   have hV i (hi:l ≤ i) (ht:i ≤ j) := (h.fits i (hk.trans hi) ht)
   let g i:=i ≤ N
   have hu'(i:ℕ)(hi:l ≤ i)(ht:i ≤ j):∃ Y:Stem V G (H.S.side i p),Stamp (N:=N) P Z (O i) (Q i) Y∧Y.home=o i:=by
       obtain ⟨hf,v,hv⟩:= hV i hi ht; exact realize P Z (o i) hs (ht.trans h.paid) (hy i hi ht) hf hv hF
   let Y0 i:= if h:l ≤ i∧ i ≤ j then (hu' i h.1 h.2).choose else Stem.mk (o i) 0 0; let Y:= update Y0 j X; have hx:Y j=X:= update_self ..
   have hv(i:ℕ)(hi:l ≤ i)(hh:i ≤ j): Stamp (N:=N) P Z (O i) (Q i) (Y i)∧ (Y i).home= o i:=by
       by_cases he:i=j; · subst i; exact hx.symm ▸ (show _ ∧ X.home=o j from ⟨ht,hP⟩)
       rw [show Y i= _ from update_of_ne he X Y0]; unfold Y0; rw [dif_pos ⟨hi,hh⟩]; exact (hu' i hi hh).choose_spec
   exact ⟨Y, impress P Z h hs hF hu hk hl Y (fun i hi hh=> (hv i hi hh).1) (fun i hi hh=> (hv i hi hh).2) hm,hx,fun i hi hh=> (hv i hi hh).1⟩
omit hF [Fintype V][DecidableEq V] in
/-- Blade without the offset eligibility. Price = (at most) one
inverse-radius plus constants. Apply also when choosing last point on
an aligned path even if this step will no longer be an aligned one.
Use next-finest purchase even on the very top, not as a propagation
hop there but a property of this authentic representative. -/
lemma root_cut {i:ℕ}(hk:k ≤ i)(hi:i < j)(he:Tunes (D N p i (hi.trans_le h.paid))) {b:V→ Site (H.S.side (i+1) p)} (x:Stem V G (H.S.side (i+1) p))(hx:Stamp (N:=N) P Z b (Q (i+1)) x): Blade (H.rep N p (i+1)) (x.home P.v) (x.oil P.v) (profile (H.rep N p (i+1)).activities (x.gas P.v)) (alto H (i+1) d*((Q (i+1)).x 0)) (1/v (i+1)):=by
    have hp:= hi.trans_le h.paid
    obtain ⟨s,hq,t,t',hV₀,hV₁,-,hy⟩:=h.waves i hk hi; obtain ⟨w,hW,hM⟩:= stamped_hop Z (Q i) (Q (i+1)) hs hp (hu i hk hp) hy hq 0
    have heq:∀ (a:Site (H.S.side (i+1) p)), a=a:= fun _=>rfl
    let R:= H.rep N p (i+1); let a:=alto H (i+1) d; let O:= x.home P.v; let P':= Q (i+1); let F0:= a • P'.exponentialEntry 0 Z R; let F1:= a • profile R.activities P'.forced
    have h': (H.levels.clock.op i p).ratio.embed 0=0:=(H.levels.clock.op i p).ratio.root.map_zero
    have hz: Blade R 0 F0 F1 (a*(P'.x 0)) (2*(‖a‖*t)):=by
       rw [h'] at hM; simp only [radiant,sunny,Ribbons.stepid,Ribbons.floatid] at hM; exact chronicle _ _ hW hM he (hu i hk hp)
    obtain ⟨π⟩:= (hs.represents N p (i+1) hp).good.labels.moves 1 O; have hN := bearer (1,false) O F0 F1 π hz
    have ha:= h.aff _ (hk.trans i.le_succ) hi
    rw [scale_F, scale_K, show affine (1:Signed) O 0=O from by simp [affine]] at hN -- scale_F etc reduc?
    rw [hx.real',hx.price]; apply hN.more; apply (le_div_iff₀ ha).2; linarith only [hV₀]
end YM.MergeProof.Ribbons.ManyCopies.Stem
