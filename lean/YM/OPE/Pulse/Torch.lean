import YM.OPE.Pulse.Lamp
import YM.MergeProof.North.Cabana
/-!
# Patrolling a migrated cluster center: Marsch to the parent chart

`Flex` may describe the live packet with arbitrary offset.
Pay a single energy for returning to horizon coordinates on an aligned step.
Adapted from MergeProof/North/{Lamplit,Elders} with offset added.
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
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
local notation "axis" => ((1,false):Motion)
variable (x: Site n) {P:Rep G n}
lemma rewind (r:Config G n→ℂ) : stepUp axis x (stepUp axis (-x) r)=r:=by
   funext U; change r (pull 1 _ (pull 1 _ U))= _; rw [pull_pull]; simp [affine]
lemma rewind_f (r:Res G n) : floatUp axis x (floatUp axis (-x) r)=r:=by
   have hr (a:Support n): sky axis (-x) (sky axis x a)=a:=by
      rw [shading,shading,image_image]; change a.image (fun i=> affine 1 (-x) (affine 1 x i))=_; simp [affine]
   funext j; obtain ⟨j,rfl⟩:= (puff axis x).surjective j
   unfold floatUp; rw [Equiv.symm_apply_apply,rewind]; congr 1; exact (Equiv.symm_apply_eq _).mpr (Prod.ext (hr _).symm (hr _).symm)
   -- edit
lemma reblade {t:ℝ}{F:Lamp G n}(h:F.Flex P x t)(π:P.activities.Moves ((axis).1) (-x)) : Blade P 0 (stepUp axis (-x) F.watch) (floatUp axis (-x) (F.rays P)) 0 t:=by
   obtain ⟨I,i,M,s,h⟩:=h; let M' i:= Leaf.route π (M i)
   have he : (0:Site n)=affine 1 (-x) x:=by simp [affine]
   refine ⟨I,i,M',s,fun i=>?_,?_,?_,?_⟩
   · rw [he,show (M' i).crest=_ from crestSky axis _ π (M i),shading]; exact mem_image_of_mem (turnSites 1 (-x)) (h.sit i) -- `affine` reducible
   · rw [h.lit]; funext U; change (0:ℂ)+(∑ i,s i • prose (M i)) (pull 1 (-x) U)= 0+(∑ i,s i • prose (M' i)) U; simp_rw [show ∀ i,prose (M' i) = _ from fun i=> climb_p axis _ π (M i), Finset.sum_apply, Pi.smul_apply];rfl
   · rw [h.run]; funext p U; unfold floatUp; simp_rw [show ∀ i,entry (M' i)=_ from fun i=>climb_entry axis _ π (M i), Finset.sum_apply,Pi.smul_apply]; unfold stepUp; rw [Finset.sum_apply]; simp only [Pi.smul_apply]; rfl
   apply le_trans _ h.pay; unfold M'; simp_rw [fareSky axis]; exact le_rfl
-- bridge
variable {A:History G} {k i j N p d:ℕ} {C:Family G}
variable {D:GaugeDoor (A.rep N p (i+1)) (A.rep N p i)} {W b t:ℝ} {o: Site (A.S.side i p)} {X: Lamp G (A.S.side (i+1) p)}
set_option quotPrecheck false
local notation "P'" => A.levels.budget i
local notation "Z" => (A.levels.clock.op i p)
local notation "R0" => A.rep N p i
local notation "R1" => A.rep N p (i+1)
local notation "χ"=> ((A.S.block i).val:ℂ)^d
local notation "Q"=> ((Labels.frames G).level d)
local notation "L"=> Next.Foundations.localSection G d
local notation "e"=> (Z).ratio.embed o
structure Ignite (A:History G) (N p k : ℕ) {G':Labels.Frame G d} (B:Hol G)(U:SectionData G')(P:Coefficient G' (A.S.side k p))(a:ℝ)(t:Site (A.S.side k p))(X:Lamp G (A.S.side k p)) : Prop where
   fuel : P.Format 0 B (A.rep N p k)
   power : P.remBound 0 (A.rep N p k) (kappa A k) a ∧ G'.coeffSize P.x ≤ a
   track : X.watch=radiant (alto A k d) (1,false) t (P.exponentialEntry 0 U (A.rep N p k))
   rays : X.rays (A.rep N p k)=sunny (A.rep N p k) P.forced (1,false) t (alto A k d)
set_option maxHeartbeats 500000 in
lemma ignite_core (h:A.Selected)(hi:i<N)(hz:X.Flex R1 ((A.levels.clock.op i p).ratio.embed o) b)(hD:SoundDoor (A.levels.clock.op i p) D)(hF:Throws A N p i D (Next.Foundations.hol G) (Next.Foundations.localSection G d) t)
    (hw:0≤t) (hp:2*W*(2*b)≤1) (hr:W*(‖((((A.S.block i).val:ℂ)^d)⁻¹)‖*(t*b))≤1) : ∃ Y:Lamp G (A.S.side i p), Debt A N p D W ((Z).ratio.embed o) X Y ∧ ∃ P'':Coefficient Q (A.S.side i p), Ignite A N p i (Next.Foundations.hol G) L P'' (A.S.a (i+1)^d*(t*b)) o Y:=by
    have hx:= h.represents N p (i+1) hi; obtain ⟨π⟩:= hx.good.labels.moves 1 (-e)
    let x' j:= stepUp axis (-e) (X.sparks (π.kp.symm j))
    have ht': Dominated x':= conduits axis _ _ X.lit π
    have hK : profile (R1).activities x'= floatUp axis (-e) (X.rays R1):=by apply roam _ _ π; intro i U; simp [x']
    let f:= stepUp axis (-e) X.watch; have hb: Blade (R1) 0 f (profile (R1).activities x') 0 b:= by rw [hK]; exact reblade _ hz π
    obtain ⟨q,hq,P,hP,hT⟩:= tossing A L (Next.Foundations.hol G) hb ht' h hi hw hD hF; have he' : (1:ℂ)=χ*χ⁻¹:= (mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (A.S.block i).pos.ne'))).symm
    obtain ⟨K,hL,hd,hB⟩:= sparkling A _ L P axis o χ⁻¹ h 0 hi.le (Next.Foundations.sound G d) hP.format hP.bound; let U:= Extra.Histories.stretch (alto A (i+1) d)⁻¹ P; let t':= (alto A (i+1) d)⁻¹; let Y:Lamp G (A.S.side i p):= ⟨radiant χ⁻¹ axis o (P.exponentialEntry 0 L R0), K, hd⟩; have hx': X.watch=stepUp axis e f := (rewind e _).symm
    have hω': X.rays R1= floatUp axis e (profile (R1).activities x'):=by rw [hK,rewind_f]
    have hL': Y.rays R0 = sunny R0 P.forced axis o χ⁻¹:= hL.symm
    obtain ⟨π'⟩:= hx.good.labels.moves 1 e; have hΔ : ((Z).ratio.parent ((Z).ratio.embed o))=o := (Z).ratio.embed_parent _
    have ht : ‖t'‖= A.S.a (i+1)^d:=by unfold t'; rw [norm_inv,alto_norm,inv_inv]
    have he := hP.leadP; rw [sub_zero] at he; have he₀:= hP.bound
    have h₀: X.disburse R1= stepUp axis e (coin R1 f x'):=by unfold Lamp.disburse; rw [hx']; exact opals axis A h hi _ _ π' ht' X.lit hω'
    refine ⟨Y,⟨⟨Set.image (Wing.labelRoute π') q, 0,2*b,‖χ⁻¹‖*(t*b),hq.image _,?_,hp,hr,by simp⟩,?_⟩,U, ?_⟩
    · rw [hΔ,hL']; nth_rw 1 [hx']; rw [hω']; have hs:= (hT.gain hD axis o π' rfl).pitch 1 χ⁻¹ he'; simp only [show affine (axis).1 ((Z).ratio.embed o) 0=e from by simp [affine],show affine (axis).1 o 0=o from by simp [affine],scalar_z,one_mul,norm_one,one_smul] at hs; exact hs
    · change coin R0 (radiant χ⁻¹ axis o (P.exponentialEntry 0 L R0)) K=(Z).push _ (X.disburse R1); rw [hB,h₀]; have hs:= starship A axis o χ⁻¹ _ d hP.agrees (spill_in hb hx.good ht') 1 he'; unfold radiant at hs; rw [one_smul] at hs; exact hs
    have hy: t'*alto A i d=χ⁻¹:=by
       have ht:alto A i d≠0:= inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (A.S.a_pos _).ne')); unfold t'; rw [alto_at, mul_inv_rev, mul_comm _ χ⁻¹, mul_assoc,inv_mul_cancel₀ ht,mul_one]
    let p':=P.exponentialEntry 0 L R0; have hα: U.exponentialEntry 0 L R0= t' • p':=by
       funext v; have hb(j): U.maskedTerm (R0) j v=t'* P.maskedTerm (R0) j v:= Extra.Histories.masked_scale ..
       change Extra.Histories.part L 0 (R0) v (t' • P.x) +∑' j,U.maskedTerm (R0) j v=t'*(Extra.Histories.part L 0 (R0) v P.x+ ∑' j,P.maskedTerm (R0) j v); simp only [map_smul,hb, smul_eq_mul,tsum_mul_left,mul_add]
    rw [← ht]; refine ⟨Extra.Histories.stretch_format _ hP.format, ⟨Extra.Histories.stretch_rem _ he₀,(Size.smul _ t' P.x).trans_le (mul_le_mul_of_nonneg_left ((le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le ..)).trans he) (norm_nonneg _))⟩,?_,?_⟩
    · rw [hα]; funext j; unfold radiant; change χ⁻¹ * _= alto A i d*(t'*_); rw [← mul_assoc,mul_comm _ t',hy]; rfl
    rw [hL']; unfold sunny; rw [show profile (R0).activities U.forced=_ from profile_scale _ P.forced t']; funext p q; change χ⁻¹ * _= alto A i d*(t'*_); rw [← mul_assoc,mul_comm _ t',hy]; rfl
section app
local notation "G*"=> C.path
local notation "Z'"=> (C.path.levels.clock.op i p)
variable {D':GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)} {o : Site (C.side i p)} {X : Lamp G (C.side (i+1) p)}
lemma ignite (h:C.Makes)(hh:Created C) (hi:i<N)(hz:X.Flex (C.path.rep N p (i+1)) (Z'|>.ratio.embed o) b) (hD: SoundDoor (Z') D') (hF:Throws (G*) N p i D' (Next.Foundations.hol G) (Next.Foundations.localSection G d) t)
    (hw:0≤t) (hp:2*W*(2*b)≤1)(hr:W*(‖((((C.S.block i).val:ℂ)^d)⁻¹)‖*(t*b))≤1): ∃ Y:Lamp G (C.side i p), Debt C.path N p D' W ((Z').ratio.embed o) X Y ∧ ∃ P:Coefficient (C.labels.level d) (C.side i p), Ignite C.path N p i C.params (C.localSection d) P (C.S.a (i+1)^d*(t*b)) o Y:=by
    obtain ⟨X',p',F,h'⟩:=hh.uses; subst C; exact ignite_core h.wilson hi hz hD hF hw hp hr
end app
end YM.MergeProof.Ribbons.ManyCopies.Patrol
