import YM.OPE.Script.Inject
/-!
# Script chorus: apply an additive column on every copy at once
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Set
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open GridApprox Cells Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {G:Gauge}{n:Side}{I J : Type} [Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    {A:History G}
set_option quotPrecheck false
local notation "K" => Finset
variable {N p i j k : ℕ} {s: i≤N}
local notation "V" => Site (A.S.side j p)
local notation "R" => A.rep N p
local notation "f" => A.S.side N p
local notation "c" => A.S.side i p
local notation "β" => A.β N p N
namespace Script
variable {z: I→Site (A.S.side j p)}{F:I→ Config G (A.S.side N p)→ℂ} {hk:j ≤ i} {hz:i ≤ N} {Q:Config G (A.S.side i p)→ Poly (Bud I)} {d : K I}
def sprinkle (U:I→ Config G n→ℂ)(P:Finset I) (Q:Config G n→ Poly (Bud I)) (x:Config G n):= Q x * ∏ i∈P,(1+Poly.send ((Bud I).fire i) (U i x))
lemma coal (hp:Script A N p hk hz z d Q F)(U:I→ Config G (A.S.side i p)→ℂ)(u:K I)(hc:∀ i∈u,Safe A N p hk (z i) (U i))(ho : ∀ i∈u,∀ j∈d∪u,z j=z i→j=i) :
    Script A N p hk hz z (d∪u) (sprinkle U u Q) (fun i=> if i∈u then F i+backTo A N p hz (U i) else F i):=by
    induction u using Finset.induction_on with
    | empty=> rw [show sprinkle U ∅ Q=Q from funext fun x=>by simp [sprinkle]]; simpa using hp
    | @insert x t hg IH=>
       -- fire last
       let F'(i):= if i∈t then F i+backTo A N p hz (U i) else F i; have he(j)(hj:j∈d∪t) : j∈ d∪insert x t:= (Finset.union_subset_union (subset_refl d) (subset_insert x t)) hj
       have hb:= fired x (IH (fun i hi => hc i (mem_insert_of_mem hi)) (fun i hi j hj=> ho i (mem_insert_of_mem hi) j (he j hj))) (hc x (mem_insert_self ..)) (fun i hi=> ho x (mem_insert_self ..) i (he i hi)); have hQ : jet (sprinkle U t Q) x (U x)=sprinkle U (insert x t) Q:=by funext y; unfold jet sprinkle; rw [prod_insert hg,mul_comm (1+_),mul_assoc]
       have ht : Function.update F' x (F' x+backTo A N p hz (U x))=(fun i=>if i∈insert x t then F i+backTo A N p hz (U i) else F i):=by
          funext i; by_cases he:i=x; subst i; rw [Function.update_self]; simp [hg,F']; rw [Function.update_of_ne he]; simp only [Finset.mem_insert,he,false_or]; rfl
       rw [Finset.union_insert]; rw [← hQ,← ht]; exact hb
lemma fueled (hp:Script A N p hk hz z d Q F)(U:I→ Config G (A.S.side i p)→ℂ)(u:K I)(hc:∀ i∈u,Safe A N p hk (z i) (U i))(ho:∀ i∈u,∀ j∈d∪u,z j=z i→j=i) (ht:∀ i,i∉u→ U i=0) : Script A N p hk hz z (d∪u) (Accent.couple Q U) (fun i=> F i+backTo A N p hz (U i)):=by
    let F'(i):= backTo A N p hz (U i); have hS i (hp:i∉u): F' i=0:= by unfold F'; rw [ht i hp]; exact backTo_const ..
    have hue : (fun i=>if i∈u then F i+F' i else F i)= fun i=>F i+F' i:=funext fun i=>by by_cases h:i∈u; exact if_pos h; rw [if_neg h,hS i h,add_zero]
    rw [← hue,show Accent.couple Q U=sprinkle U u Q from ?_]; exact hp.coal U u hc ho
    funext x; unfold Accent.couple sprinkle Mach; rw [pass_sum _ _ (fun i _=>singleton_nonempty _)]; exact congr_arg (_ * ·) (prod_subset (subset_univ u) (fun i _ hi=>by simp only [ht i hi,Pi.zero_apply,Poly.send_zero,add_zero])).symm
lemma hotter (hp:Script A N p hk hz z d Q F) {d':Finset I}(he:d⊆d'):Script A N p hk hz z d' Q F:=⟨hp.budget,hp.cost, fun a b h U ht=>hp.exists_budget a b (Disjoint.mono_right ((Finset.image_mono _) (Finset.inter_subset_inter_left he)) h) _ ht⟩
lemma played (hp:Script A N p hk hz z d Q F) (a:Finset I): (∫ W,(Q W).part (Fibers.mark a)∂prior G _)=(Wilson.partition G (A.S.side N p) (A.β N p N):ℂ)*moment (A.β N p N) (fineJob F a):=by
   have h:= hp.exists_budget a ∅ (Finset.disjoint_empty_left _) 0 (by simp); simp only [Finset.prod_empty, mul_one] at h
   rw [h,moment_formula β (fineJob F a) ((Envelope.prodC a F (fun i _=>hp.cost _)).integrableC _),mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')]
lemma corps (hp:Script A N p hk hz z d Q F)(X:Extra.Trajectories.Names (Bud J) (Bud I)): Script A N p hk hz (z ∘ X.e) univ (X.restriction ∘ Q) (F ∘ X.e):=by
    refine ⟨MeasureTheory.integrable_pi_iff.mpr (fun i=> part_int hp.budget (X.share i)),fun i=>hp.cost _,fun a b h U ht=>?_⟩
    have hh:Disjoint b (((X.share (Fibers.mark a)).val ∩ d).image z) :=by
       apply Disjoint.mono_right _ h; apply subset_trans ((Finset.image_mono z) (@Finset.inter_subset_left _ _ _ _)); change (a.image _).image _⊆_; rw [Finset.image_image,Finset.inter_univ]
    have hv:= hp.exists_budget (X.share (Fibers.mark a)).val b hh U ht; simp_rw [show ∀ u,fineJob F (X.share (Fibers.mark a)).val u=fineJob (F ∘ X.e) a u from fun u=> prod_image X.e.injective.injOn] at hv; exact hv
end Script
end YM.MergeProof.Ribbons.ManyCopies.Patrol
