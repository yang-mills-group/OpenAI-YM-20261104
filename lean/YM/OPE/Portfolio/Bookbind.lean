import YM.OPE.Portfolio.Anthem
import YM.OPE.Sweep.Camp
/-!
# Throw ticket on arbitrary aligned parent
and acquire a Cup witness of a heading coefficient (the actual Frames will
read it through normalization at level i).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {I J : Type}{G:Gauge}{H:History G}{N p i b d:ℕ}{F:Labels.Frame G d}
local notation "T"=> H.rep N p
set_option quotPrecheck false
local notation "L"=> (↑(H.S.block i).val:ℂ)^d
namespace Studio
variable (B:SectionData F)(w:Motion)
variable {P:Coefficient F (H.S.side i p)}{v:Cup (H.rep N p i)} {o:Site (H.S.side i p)}{C R E:ℝ}
structure Mantle (H:History G)(N p i:ℕ)(B:SectionData F)(w:Motion)(o:Site (H.S.side i p))(P:Coefficient F (H.S.side i p)) (v:Cup (H.rep N p i)): Prop where
    prose:v.home=radiant (alto H i d) w o (P.exponentialEntry 0 B (H.rep N p i))
    key:v.leaves=sunny (H.rep N p i) P.forced w o (alto H i d)
lemma Mantle.obvious (h:H.Selected){A:Source.Hol G}(hm:i≤N)(hs:B.Sound A)(hP:P.Format 0 A (T i))(hv:P.remBound 0 (T i) C E) : ∃ v,Mantle H N p i B w o P v :=by
   obtain ⟨k,hk,hV,hF⟩:=sparkling H A B P w o (alto H i d) h 0 hm hs hP hv; exact ⟨Cup.book (T i) _ k hV,⟨rfl,hk.symm⟩⟩
-- same singleton cup output exact density
lemma Mantle.income (h:H.Selected){A:Source.Hol G}(hm:i≤N)(hs:B.Sound A)(hP:P.Format 0 A (T i))(hv:P.remBound 0 (T i) C E) (hR:Mantle H N p i B w o P v) : v.pays= radiant (alto H i d) w o (P.density 0 B (T i)):=by
   obtain ⟨k,hk,hV,hF⟩:= sparkling H A B P w o (alto H i d) h 0 hm hs hP hv; unfold Cup.pays; rw [hR.prose]; exact (coin_port _ _ v.held hV (v.fitted.symm.trans (hR.key.trans hk)) (h.represents N p i hm|>.good.labels)).trans hF
lemma Mantle.same {v':Cup (H.rep N p i)}(h:Mantle H N p i B w o P v)(hh:Mantle H N p i B w o P v') : v=v':= Cup.same (h.prose.trans hh.prose.symm) (h.key.trans hh.key.symm)
local notation "Y"=> ((1,false):Motion)
-- explicit translation act/inverse for Uncenter(L) input Cup
section Translate
variable {n:Side}
lemma upstairs_unit (f:Config G n→ℂ)(x:Site n) : stepUp Y x (stepUp Y (-x) f)=f:=by
   funext U; change f (pull 1 (-x) (pull 1 x U))=f U; rw [pull_pull]; simp only [affine,Signed.act_one,neg_add_cancel,mul_one]; exact congr_arg f (by rw [pull_one]; show Lattice.translate _ U=U; funext v;simp [Lattice.translate])
lemma sky_back (x:Site n)(p:Support n): sky Y x (sky Y (-x) p)=p:=by
   rw [shading,shading,image_image,show ((⇑(turnSites _ x)) ∘ (⇑(turnSites _ (-x))))=id from ?_,image_id]; funext i; change affine 1 x (affine 1 (-x) i)=_; simp [affine]
lemma downstairs_unit (f:Res G n)(x:Site n): floatUp Y x (floatUp Y (-x) f)=f:=by
   funext i; let g:= puff Y (-x); let h:=puff Y x; obtain ⟨i,rfl⟩:=h.surjective i; obtain ⟨i,rfl⟩:=g.surjective i; have hp : h (g i)=i:=Prod.ext (sky_back _ _) (sky_back ..); change stepUp Y _ (stepUp Y _ (f (g.symm (h.symm (h (g i))))))=_; rw [h.symm_apply_apply,g.symm_apply_apply,upstairs_unit,hp]
lemma moved_blade (x o:Site n){t:ℂ}{Q:Rep G n}{F:Config G n→ℂ}{f:Res G n}(h:Blade Q o F f t E) (π: Q.activities.Moves w.1 x): Blade Q (affine w.1 x o) (stepUp w x F) (floatUp w x f) (scalar w t) E:=by
   obtain ⟨I,b,M,s,h⟩:=h; refine ⟨I,b,Leaf.route π ∘ M,fun i=> scalar w (s i),fun i=> ?_,?_,?_,?_⟩
   · unfold Function.comp; rw [crestSky w x π,shading]; exact Finset.mem_image_of_mem (turnSites w.1 x) (h.sit i)
   · funext U; rw [h.lit]; unfold stepUp; simp_rw [Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,scalar_add,summer, Function.comp_apply,scalar_mul,climb_p w x π]; rfl
   · funext i U; rw [h.run]; unfold floatUp stepUp; simp_rw [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,summer, Function.comp_apply,scalar_mul, climb_entry w x π]; rfl
   simp only [comp_apply,norm_scalar,fareSky w _ π]; exact h.pay
end Translate
-- converted Heading donation
local notation "S"=> H.levels.clock.op i p
local notation "I'"=> (S).ratio
variable {u:Site (H.S.side i p)}{D:GaugeDoor (H.rep N p (i+1)) (H.rep N p i)} {X:Cup (H.rep N p (i+1))}
local notation "A₁"=> Next.Foundations.hol G
local notation "B₁"=> Next.Foundations.localSection G d
set_option maxHeartbeats 600000 in
lemma thrown (d:ℕ)(h:H.Selected)(hn:i<N)(hc:0≤C)(he:SoundDoor S D) (hr:Throws H N p i D (Next.Foundations.hol G) (Next.Foundations.localSection G d) C)
    (hX:Blade (T (i+1)) ((I').embed u) X.home X.leaves 0 E) {a:ℝ} (hw:4*a*E≤1)(hF:a*(C*E)≤ 1)(ha:0<a) : ∃ (P:Coefficient ((Labels.frames G).level d) (H.S.side i p)) (v:Cup (H.rep N p i)), P.Format 0 (Next.Foundations.hol G) (T i)∧ P.remBound 0 (T i) (kappa H i) (H.S.a (i+1)^d*(C*E)) ∧ ((Labels.frames G).level d).coeffSize P.x ≤ H.S.a (i+1)^d*(C*E)∧ Mantle H N p i (Next.Foundations.localSection G d) Y u P v ∧ Cup.Edge S D X v ((I').embed u) u 0 a:=by
   -- use fully explicit B references d new binder not section `d`; trick move header `(d:ℕ) variable include d`
   let P₁:= T (i+1); let B':=Next.Foundations.localSection G d; let k:= (I').embed u; let m(x:Site (H.S.side (i+1) p)):= (h.represents N p (i+1) hn|>.good.labels.moves 1 x).some
   obtain ⟨K,hK,hq⟩:= X.upbeat Y (-k) (m _); let F:= stepUp Y (-k) X.home; have hT: Blade (T (i+1)) 0 F (profile P₁.activities K) 0 E:=by
      rw [← hq]; let F':= moved_blade (E:=E) Y (-k) k hX (m _); have hx: affine ((Y).1) (-k) k=0:=(by simp [affine]); rw [← hx]; exact F' -- tactic rewriting zeros too.Maybe
   obtain ⟨t,ht,Q,hQ,HQ⟩:= tossing H B' (Next.Foundations.hol G) hT hK h hn hc he hr
   let y:= ((H.S.block i).val:ℂ)^d; let z:=(alto H (i+1) d)⁻¹; let Z:=Extra.Histories.stretch z Q; have hz:‖z‖= H.S.a (i+1)^d:=by unfold z;rw [norm_inv,alto_norm,inv_inv]
   have hy : z*alto H i d=y⁻¹:=by have h:alto H i d≠0:=inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (H.S.a_pos _).ne')); unfold z; rw [alto_at,mul_inv_rev,mul_comm _ y⁻¹,mul_assoc,inv_mul_cancel₀ h,mul_one] -- grouping local let
   have hi:= stretch_format z hQ.format; have hv:= stretch_rem z hQ.bound; rw [hz] at hv; obtain ⟨v,hl⟩:= Mantle.obvious (o:=u) B' Y h hn.le (Next.Foundations.sound G d) hi hv
   refine ⟨Z,v,hi,hv,?_,hl,?_⟩
   · rw [← hz]; apply (le_of_eq (Size.smul _ z Q.x)).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); have he:=hQ.leadP; rw [sub_zero] at he; exact (le_mul_of_one_le_left (Work.G08.size_nonneg ..) (orbitCost_one_le ..)).trans he
   have ht' := Float.spill_in hT (h.represents N p (i+1) hn).good hK; let U:= coin (T (i+1)) F K; have he': stepUp Y k U=X.pays:=by
       have h': U=stepUp Y (-k) X.pays:= Float.opals _ _ h hn (-k) _ (m _) X.held hK (hq.symm.trans (congr_arg _ X.fitted)); rw [h',upstairs_unit]
   have hl' : radiant (alto H i d) Y u (Z.density 0 B' (T i))= radiant y⁻¹ Y u (Q.density 0 B' (T i)):=by
       funext j;
       change _ * (Z.density 0 _ _ _)=_*_; change _*(Extra.Histories.stretch z Q|>.density 0 B' _ _)= _; rw [stretch_density]; change _*(z*_)=_; rw [← mul_assoc,mul_comm _ z,hy]; rfl -- spaces
   constructor
   · rw [hl.income B' Y h hn.le (Next.Foundations.sound G d) hi hv, hl']; have hp:y≠0:=pow_ne_zero _ (by exact_mod_cast (H.S.block i).pos.ne'); have ht' := starship H Y u y⁻¹ U d hQ.agrees ht' 1 (show (1:ℂ)=y*y⁻¹ from (mul_inv_cancel₀ hp).symm); rw [ht',radiant,one_smul, he']
   let m':= m k; have hp:y≠0:=pow_ne_zero _ (by exact_mod_cast (H.S.block i).pos.ne'); have hθ:= ((HQ.gain he Y u m' (show scalar Y y=y from rfl))).pitch 1 y⁻¹ (show (1:ℂ)=y*y⁻¹ from (mul_inv_cancel₀ hp).symm);
   have he1:1 ≤ ‖y‖:= by unfold y; rw [norm_pow,Complex.norm_natCast]; exact one_le_pow₀ (le_trans one_le_two (size_enough H i))
   have he2:0 ≤ E:= by obtain ⟨I,i,M,s,h⟩:=hT; exact (sum_nonneg (fun i _=>mul_nonneg (norm_nonneg _) ((M i).profit.trans ((T (_)|>.p).loMass _ _ (M i).profit)))).trans h.pay -- shadow i
   have hu: v.leaves=y⁻¹ • floatUp Y u (profile (T i).activities Q.forced):=by
      rw [hl.key]; unfold sunny; rw [show Z.forced=z • Q.forced from rfl, profile_scale]; funext i V; change _ * (floatUp _ _ (_ • _) _ _) = y⁻¹* (floatUp Y _ _ _ _); simp_rw [floatUp,stepUp,Pi.smul_apply]; change alto H _ _ * (z * _)=_; rw [← mul_assoc, mul_comm _ z,hy]; rfl
   refine ⟨_,2*E,‖y⁻¹‖*(C*E),ht.image (Wing.labelRoute m'),?_ ,?_ ,by simp,?_⟩
   rotate_right
   · simp only [show affine (Y).1 ((I').embed u) 0=((I').embed u) from by simp [affine], show affine (Y).1 u 0=u from by simp [affine], scalar_z,one_mul, norm_one, one_smul] at hθ; rw [show stepUp Y ((I').embed u) F=X.home from upstairs_unit ..,← (show X.leaves=floatUp Y ((I').embed u) (profile P₁.activities K) from by rw [← hq]; exact (downstairs_unit ..).symm),← hu] at hθ; exact hθ
   · linarith only [hw];
   rw [norm_inv]; exact (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (mul_nonneg hc he2) (inv_le_one_of_one_le₀ he1)) ha.le).trans hF
end Studio
end YM.MergeProof.Ribbons.ManyCopies.Cadet
