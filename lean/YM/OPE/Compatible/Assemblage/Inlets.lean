import YM.OPE.Compatible.Assemblage.Wing
/-!
# Pad active markers immediately prior to an event. Don't propagate
artificially coincident origins all the way to the finer cutoff.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars true
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem Mirror
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n:Side}
    (P:Ensemble V) {E:V→Site n}
section March
variable (V I J)
def inlets : (V×I) ↪ (V×(I⊕J)):= ⟨fun i=> (i.1, Sum.inl i.2),fun _i _j he=> Prod.ext (Prod.mk.inj he).1 (Sum.inl.inj (Prod.mk.inj he|>.2))⟩
end March
local notation "f"=> inlets V I J
lemma hint_left {V I J : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (v:V)(i:I): (inlets V I J) (v,i)=(v, Sum.inl i):=rfl
lemma inlets_rays (b:Equiv.Perm V)(p:Mode (V×I)): drum b (imageM f p)=imageM f (drum b p):=by
   apply Subtype.ext; simp only [drum, pares,imageM,image_image]; rfl
lemma inlets_warm (b:Equiv.Perm V)(p:Mode (V×(I⊕J))) : warm f p↔ warm f (drum b p):=by
    constructor
    · intro he; rw [← show imageM f (invM f p)=p from he, inlets_rays]; exact heat_image ..
    intro he; have hb:= (drum b).symm_apply_apply p; -- drum function not equiv? inspect
    let h:= invM f (drum b p); let q:= (drum b).symm h -- diff type
    have hx: imageM f q=p:= (drum b).injective (by rw [inlets_rays,(drum b).apply_symm_apply]; exact he)
    rw [← hx]; exact heat_image ..
lemma noticed {v:V}{x:Mode (V×(I⊕J))} (h:Focused v x) : Focused v (invM f x):=by
    rw [← district_iff] at h ⊢; intro i hi; exact h ((low_read ..).1 (show i∈_ from hi))
lemma rivet {b: Equiv.Perm V}{v:V}{m:Motion} {p q:Words (V×I)} (h:Harm v b m p q) : Harm v b m (Mirror.rise f p) (Mirror.rise f q):=by
    intro x hx; by_cases hh:warm f x
    · have hp:= h (invM f x) (noticed (J:=J) hx); rw [← show imageM f (invM f x)=x from hh,inlets_rays,Mirror.rises,Mirror.rises]; exact hp
    rw [no_rise f _ _ hh,no_rise f _ _ (fun he=> hh ((inlets_warm ..).2 he)),scalar_z]

lemma not_inside {V I J : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (v:V)(j:J): (v, Sum.inr j) ∉ Set.range (inlets V I J):=fun ⟨_i,h⟩=> Sum.inl_ne_inr (Prod.mk.inj h|>.2)
lemma fire_ex (v:V)(j:J): ¬ warm f ((Bud (V×(I⊕J))).fire (v, Sum.inr j)):=fun he=> not_inside (I:=I) v j ((heat_iff ..).mp he _ (mem_singleton_self _))
lemma speak (C:I→ℂ): Mach (Names V (I⊕J)) (spices P (Sum.elim C (1:J→ℂ))) =
    Mach (Bud (V×(I⊕J))) (Mirror.mark f)+Mirror.rise f (Mach (Names V I) (spices P C)):=by
    -- helper lift isolated function
    let s:Finset (V×(I⊕J)):= univ.image f
    let F:=(spices P (Sum.elim C (0:J→ℂ)))
    have he: Mach (Names V (I⊕J)) F=Mirror.rise f (Mach (Names V I) (spices P C)):=by
       unfold Mach;rw [map_sum,← Finset.sum_subset (subset_univ s) (fun i _ hi=>?_),  show s= univ.image f from rfl,sum_image (inlets V I J).injective.injOn]; refine sum_congr rfl fun j _=> ( (sendH f _ _).trans ?_).symm; rw [heat_fires]; rfl
       rcases i with ⟨v,i|i⟩; exact False.elim (hi (mem_image_of_mem _ (mem_univ (v,i))))
       rw [show F ((v,.inr i))=0 from scalar_z _,Poly.send_zero]
    rw [← he,← Fibers.mach_add]; congr 1; funext i; rcases i with ⟨v,i|i⟩
    · change P.echo (C i) v= Mirror.mark f (v, .inl i)+P.echo (C i) v; rw [show Mirror.mark f (v, .inl i) = 0 from if_pos ⟨(v,i),rfl⟩,zero_add]
    change P.echo 1 v=_+P.echo 0 v; rw [show Mirror.mark f (v, .inr i) = 1 from if_neg (not_inside v i), show P.echo 0 v=0 from scalar_z _,add_zero]; unfold Ensemble.echo Motion.scalar; split <;> simp

section
variable {d u e c t δ v b w α σ θ:ℝ} {Q:Config G n→Words (V×I)}{R:Rep G n}{C:I→ℂ}{X:I→Stem V G n}{W:I→ℝ}
    (Y:J→V→ Site n)(D:J→ℝ)
def placeOn (X:I→ Stem V G n)(Y:J→V→ Site n)(i:I⊕J) : Stem V G n:=Sum.elim X (fun j=> ⟨Y j,1,0⟩) i
lemma registered {V I J : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {G : Gauge} {n : Side} (P : Ensemble V) {E : V → Site n} {R : Rep G n} {X : I → Stem V G n} (Y : J → V → Site n) (h:∀ i,Marked R E P (X i)) (hq:∀ j i,i≠P.v→Y j i=affine (P.move i).1 (E i) (Y j P.v))(j:I⊕J): Marked R E P (placeOn X Y j):=by
    cases j with
    | inl j=> exact h _
    | inr j=>
       refine ⟨fun i hi=> hq j i hi,fun i _=>?_ ,fun i=> pawn0⟩ -- base
       change 1=stepUp _ _ (1:Config G n→ℂ) ∧ profile R.activities 0=floatUp _ _ (profile R.activities 0)
       refine ⟨funext fun i' => ?_,funext fun i'=>funext fun V'=> ?_⟩
       · simp only [stepUp,Pi.one_apply]; unfold scalar;split <;> simp
       unfold floatUp stepUp scalar profile cram; simp
lemma pad_fire (h:Arc R (lights X) (color X) Q P.v P.move E P.perms (tags X) (quota V W) d e t v u (spices P C))
    (h0:0≤u)(hx:R.activities.Valid R.p σ θ)(hT:∀ i U,(Q U).part ((Names V I).fire i)=coin R (lights X i) (color X i) U):
    let S := placeOn X Y
    Arc R (lights S) (color S) (pad f∘Q) P.v P.move E P.perms (tags S) (quota V (Sum.elim W D)) d e t v u (spices P (Sum.elim C 1)) ∧ ∀ i U, (pad f (Q U)).part ((Names V (I⊕J)).fire i)=coin R (lights S i) (color S i) U :=by
    intro S; obtain ⟨F,K,ψ,hψ,hP,hF,hK,hB,hZ,hG,hI,hY,rfl⟩:= h.see
    let M z:= Mach (Names V I) (spices P C)+ ∑ i,F i z
    let ψ'(i:V×(I⊕J)):= Sum.elim (fun j:I=>ψ (i.1,j)) (fun _=>0) i.2
    let F' i:=Mirror.rise f∘F i; let K' i :=Mirror.rise f∘K i
    have ho: tags S ∘ f= tags X:=rfl
    have hc: ∀ U,(M U).part (Names V I).quiet=0:=by intro U; unfold M; simp only [Poly.part_plus,mute,Poly.part_sum,fun i=>(hB i).sil U,sum_const_zero,add_zero]
    constructor
    · refine ⟨F',K',ψ',?_,?_, high_towed f hF rfl, high_towed f hK rfl,(fun i=>buses f (hB i) ho),(fun i=>flows f (hZ i) ho),fun i hi=>⟨(hG i hi).1, fun U=> ⟨fun j=>rivet ((hG i hi).2 U|>.1 j),fun j=>rivet ((hG i hi).2 U|>.2 j)⟩⟩,fun i U=>?_, ?_,?_⟩
      · refine ⟨fun i s=>?_,fun i s=>?_,fun i=>?_⟩
        · rcases i with ⟨v,j|j⟩; exact hψ.yes (v,j) s; exact Attaches.zero _ _
        · rcases i with ⟨v,j|j⟩; exact hψ.tracks (v,j) s; exact fun he=> False.elim (he rfl)
        rcases i with ⟨v,j|j⟩; exact hψ.fee (v,j)
        exact ⟨0, by change ∀ j,0≤(0:ℝ)∧ _; simp [ψ'],by simpa using h0⟩
      · intro i hi j; cases j; next j=> exact hP i hi j
        next=> exact funext fun j=>funext fun U=> (scalar_z _).symm
      · change (Mirror.rise f (K i U)).part (Bud _).quiet=_; rw [← heat_quiet f,Mirror.rises]; exact hI i U
      · rintro i ⟨x,j|j⟩ U
        · change (Mirror.rise f (K i U)).part ((Bud _).fire _)+_= _; rw [← hint_left (J:=J) x j,← heat_fires,Mirror.rises]; exact hY i (x,j) U
        change (Mirror.rise f (K i U)).part ((Bud _).fire (x,.inr j))+hook R.activities R.p.threshold 0 i U=profile R.activities 0 i U
        rw [no_rise _ _ _ (fire_ex x j)];simp [hook,profile,cram]
      funext U; change pad f (play R (Names V I) K M U) = _; rw [installed]; unfold play; rw [map_smul,mul_smul_comm]; refine congr_arg _ ?_ -- edit
      dsimp only; rw [rises_mul,passM (Mirror.rise f) (high_one _) (rises_mul _) _ (hc _) (show _ from by rw [← heat_quiet f,Mirror.rises]; exact hc _), field_map _ (high_one f) (rises_mul _), ← mul_assoc, ← pass_add (mute (Bud _) _) (show (Mirror.rise f (M U)).part (Bud _).quiet=0 from by rw [← heat_quiet f,Mirror.rises]; exact hc _)]
      unfold M; rw [speak,map_add,map_sum,add_assoc]; rfl
    intro i U; rcases i with ⟨v,j|j⟩
    · let e:= (v,Sum.inl (β:=J) j); change (Mirror.pad f (play R (Names V I) K M U)).part ((Bud _).fire e)=_
      change Poly.part (R:=Names V I) (play R _ K M U) (invM f _)=_; rw [show e=f (v,j) from rfl,← heat_fires,tall]; exact hT _ _
    change (play R _ K M U).part (invM _ _)= coin R (fun _=>1) 0 U; have hz: invM f ((Bud _).fire (v, .inr j))=(Bud _).quiet:=by
       apply Subtype.ext; ext1 i; rw [low_read]; simp [Census.fire,Census.quiet,inlets]
    rw [hz,Accent.bronze R _ _ _ _ hx (fun i=>hI ..) (hc U),coin₀]; simp
end
end YM.MergeProof.Ribbons.ManyCopies
