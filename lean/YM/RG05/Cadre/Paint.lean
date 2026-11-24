import YM.RG05.Strand.Pair
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra
/-!
 # Homomorphic encoding of bundles of support markers. Multiplicative
 including when two tags (non-disjoint) describe coincident replicas. Reuses
 MULTISOURCE_TRAJECTORIES `tagged_prod`, `pass_sum`. Also gives projection
 to active subset on a dense spectrum.
 -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.RG05.Strand
open Function Filter Lattice RG Wilson Pressure Finset MeasureTheory
open MergeProof Ribbons.ManyCopies Cadet Muster
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Extra.Trajectories MergeProof.Float OPE.Backup
open scoped Topology BigOperators Classical
variable {I V : Type*}[DecidableEq I][DecidableEq V]
    {Q:Census V} {B:Census I}
abbrev Whole (B:Census I) : Prop:= ∀ s:Finset I,s∈ B.choices
local notation "P"=> Poly B
local notation "U"=> Poly Q
variable (J:I→ Poly Q)(hm:∀ x:I,J x * J x=0)
noncomputable def paints (J:I→ Poly Q)(B:Census I) : Poly B→ₗ[ℂ] Poly Q where
    toFun p:= ∑ i:B.Mode,p.part i • ∏ j∈i.val,J j
    map_add' _ _:= by simp only [Poly.part_plus,add_smul,sum_add_distrib]
    map_smul' z _:= by simp only [Poly.part_smul,RingHom.id_apply,← smul_smul, smul_sum]
local notation "λp"=> paints J B
lemma paint_send (i:B.Mode)(x:ℂ): λp (Poly.send i x)= x • ∏ j∈i.val,J j:= by unfold paints; simp
lemma paint_knot (i:I)(z:ℂ): λp (Poly.send (B.fire i) z)=z • J i:= by rw [paint_send]; simp [Census.fire]
lemma paint_one : λp 1=1:=by rw [show (1:P)=Poly.send B.quiet 1 from rfl,paint_send]; simp [Census.quiet]
include hm
variable (H:Whole B)
include H
private lemma paint_match (x y:B.Mode)(z w:ℂ): let Φ:= paints J B; Φ (Poly.send x z * Poly.send y w)=Φ (Poly.send x z)*Φ (Poly.send y w):=by
    intro Φ; by_cases he: Disjoint x.val y.val
    · let I': B.Mode:=⟨x.val∪y.val,H _⟩; unfold Φ; rw [tagged_mul _ _ I' ⟨he,rfl⟩,paint_send,paint_send,paint_send]
      change (z*w) • (∏ j∈ x.val∪y.val,J j)=_; rw [prod_union he, smul_mul_assoc,mul_smul_comm, ←smul_smul]
    rw [show Poly.send x z * Poly.send y w=0 from (by by_contra h; obtain ⟨i,ha,_⟩:= merges_of_tagged_mul h; exact he ha),map_zero]; obtain ⟨i,hx,hy⟩:= Finset.not_disjoint_iff.mp he; unfold Φ; rw [paint_send,paint_send]; rw [smul_mul_assoc,mul_smul_comm]; rw [← mul_prod_erase _ J hx, ← mul_prod_erase _ J hy]; rw [show J i*_*(J i*∏ j∈y.val.erase i,J j)=(J i*J i)*(∏ j∈x.val.erase i,J j)*(∏ j∈y.val.erase i,J j) from by ring, hm]; simp
lemma paint_mul : ∀ x y:Poly B, λp (x*y)= λp x * λp y:=by
   intro x y; rw [← Poly.studs x,← Poly.studs y]; simp_rw [map_sum,sum_mul,mul_sum,map_sum,paint_match J hm H]
lemma paint_many {I':Type*} (s:Finset I') (x:I'→ Poly B): λp (∏ j∈s,x j)=∏ j∈s,λp (x j):=by induction s using Finset.induction_on with| empty=> rw [prod_empty,prod_empty,paint_one]| insert i s hi ih=> rw [prod_insert hi,prod_insert hi,paint_mul J hm H,ih]
lemma paint_box {n:Side}(p: Support n)(F: Box n→Poly B) : λp (Accent.field F p) = Accent.field (λp ∘ F) p:=by
    unfold Accent.field; rw [map_sum]; refine Finset.sum_congr rfl fun i _=>?_; unfold Accent.grid; split; exact paint_many J hm H ..; exact map_zero _
omit hm H
variable (T:I→ Q.Mode)
omit [DecidableEq I] in
lemma tagsquare (hx:∀ i,(T i).val.Nonempty): ∀ x:I, Poly.send (T x) 1*Poly.send (T x) 1=0:=by intro i; by_contra hd; obtain ⟨z,hz,hp⟩:=merges_of_tagged_mul hd; obtain ⟨j,hj⟩:=hx i; exact Finset.disjoint_left.mp hz hj hj
lemma rain (v:ℂ)(x:Q.Mode): v • Poly.send x 1= Poly.send x v:=by ext i; simp
section
variable {I V : Type} [Fintype I][Fintype V] [DecidableEq V][DecidableEq I]
   {G:Gauge}{n:Side}{R:Rep G n} {Q:Census V}{B:Census I}
variable (tag:I→Q.Mode) (h:∀ i,(tag i).val.Nonempty)
local notation "η"=> (fun i=> Poly.send (tag i) 1)
local notation "U"=> paints η B
variable {X:Config G n → Poly B}{x:I→ Config G n→ℂ}{b:I→Res G n}
variable (HB:Whole B)
omit h
omit [Fintype I] [Fintype V] in
lemma distant (Q':Poly B) (u:Q.Mode) : ((paints (fun i=>Poly.send (tag i) 1) B) Q').part u = ∑ j : B.Mode,if _ : Fits tag j.val ∧ j.val.biUnion (fun i=>(tag i).val)=u.val then Q'.part j else 0:= by
     unfold paints; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [Poly.part_sum]; refine Finset.sum_congr rfl fun j _=>?_; rw [Poly.part_smul]; by_cases ht:Fits tag j.val
     · rw [tagged_prod tag j.val ht (fun _=>1)]; rw [Poly.part_send]; split
       · next h=> rw [dif_pos ⟨ht, h ▸ rfl⟩]; simp
       next h=> rw [dif_neg (fun h'=> h (Subtype.ext h'.2.symm)),mul_zero]
     rw [show (∏ i∈j.val,(Poly.send (tag i) 1))=0 from Classical.byContradiction (fun hz=> ht (fits_of_tagged_prod tag hz)),Poly.part_nil,mul_zero,dif_neg (mt And.left ht)]
include HB h
variable (x b) in
lemma packed_channels (U':Config G n): U (play R B (fun p y=>bar R.activities B y p+Mach B (fun i=>b i p y)) (fun y=>Mach B (fun i=>x i y)) U')= play R Q (fun p y=> bar R.activities Q y p+∑ i,Poly.send (tag i) (b i p y)) (fun y=>∑ i,Poly.send (tag i) (x i y)) U':=by
     have hv:= tagsquare tag h; have hh (f:I→ℂ): U (Mach B f)= ∑ i,Poly.send (tag i) (f i):=by
        unfold Mach; rw [map_sum]; simp_rw [paint_knot, rain]
     have he:∀ f:I → ℂ,U (Poly.pass (Mach B f)) = Poly.pass (U (Mach B f)):=by
          intro f; rw [hh]; unfold Mach; rw [pass_sum (tag:=B.fire),pass_sum (tag:=tag) _ (fun i _=>h i),paint_many _ hv HB]; simp_rw [map_add,paint_one,paint_knot,rain]; exact fun i _=> Finset.singleton_nonempty _
     unfold play; dsimp only; rw [map_smul,paint_mul _ hv HB, he,hh, paint_box _ hv HB]; apply congr_arg; apply congr_arg; apply congr_arg (Accent.field · (_)); funext i; simp only [Function.comp_apply,map_add,hh]; change U (Poly.send B.quiet _) + _=_; rw [paint_send]; unfold bar Poly.bead; simp [Census.quiet]; exact rain _ _
end
-- Projection of a partition. ANY subset. Constant outside alternatives irrelevant.
section
variable {I V : Type} [Fintype I][Fintype V] [DecidableEq V][DecidableEq I]
   {G:Gauge}{n:Side}{R:Rep G n}{Q:Census V} {B:Census I}
variable (T:Finset V) (S:Finset I) (π:I→ V)(h:Set.InjOn π (S:Set I))(he:S.image π=T)
   {z:ℂ} (HB: Whole B)(HQ:Whole Q)
local notation "P"=> Poly B
local notation "U"=> Poly Q
noncomputable def notch (π:I→ V) (Q:Census V)(S:Finset I)(x:I): Poly Q:=if x ∈ S then Poly.send (Q.fire (π x)) 1 else 0
local notation "U'"=> notch π Q S
local notation "μ"=> paints U' B
omit [Fintype V] [Fintype I] in
lemma paint_notch (j:I): μ (Poly.send (B.fire j) z)= if j ∈ S then Poly.send (Q.fire (π j)) z else 0:= by
    rw [paint_knot]; unfold notch; split; exact rain ..; exact smul_zero _
-- visibility & Part identity
omit [Fintype V] [Fintype I] in
lemma every_notch (j:I): U' j * U' j=0:=by
   unfold notch; split
   next he=> exact tagsquare (Q.fire) (fun i=> Finset.singleton_nonempty _) (π j)

   next h=> rw [mul_zero]
local notation "θ"=> (⟨S,HB S⟩:B.Mode)
local notation "q"=>(⟨T,HQ T⟩:Q.Mode)
include h he HB HQ
omit [Fintype V] [Fintype I] in
lemma visible (x:Poly B) : (μ x).part q = x.part θ:=by
    unfold paints; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [Poly.part_sum]; have hv(A:Finset I)(hx:A⊆S) : ∏ i∈A,U' i= Poly.send (show Q.Mode from ⟨A.image π,HQ _⟩) 1:=by
         let f(i:I):= Q.fire (π i); have hx':Fits f A:=⟨?_,HQ _⟩;
         · rw [show (∏ i∈A,U' i)= ∏ i∈A,Poly.send (f i) 1 from Finset.prod_congr rfl fun i hi=> by simp [notch,hx hi,f]]; rw [tagged_prod f A hx' (fun _=>1),prod_const_one]; apply congr_arg (Poly.send · 1); apply Subtype.ext; simp [unionTag,Census.fire,f]; ext i; simp [eq_comm]
         intro i hi j hj hj'; exact disjoint_singleton.mpr (fun w=> hj' (h (hx hi) (hx hj) w))
    simp_rw [Poly.part_smul]; rw [sum_eq_single θ]; rw [hv _ (le_refl S),he]; simp
    · intro j _ hz; by_cases ht:j.val⊆S
      · rw [hv _ ht]; rw [Poly.part_send,if_neg, mul_zero]; intro hh; exact hz (Subtype.ext (Finset.image_injOn_powerset_of_injOn h (mem_powerset.mpr ht) (mem_powerset_self _) ((congr_arg Subtype.val hh).symm.trans he.symm)))
      obtain ⟨i,hi,hz⟩:= Finset.not_subset.mp ht; simp [ Finset.prod_eq_zero hi (show U' i=0 from if_neg hz)]
    simp
noncomputable def vent (x:I→ Config G n→ℂ)(K:I→Res G n) (p:Config G n):= play R B (fun i p=> bar R.activities B p i + Mach B (fun j=>K j i p)) (fun p=> Mach B (fun j=>x j p)) p
variable {x:I→ Config G n→ℂ}{x':V→ Config G n→ℂ}{K:I→ Res G n}{K':V→ Res G n}
    (hx:∀ i∈S,x i= x' (π i))(hh:∀ i∈S,K i= K' (π i))
omit HB HQ [Fintype V] in
private lemma notar {f:I→ℂ}{f':V→ℂ}(hz:∀ i∈S,f i=f' (π i)) : μ (Mach B f) = ∑ i∈T,Poly.send (Q.fire i) (f' i):=by
     subst T; unfold Mach; rw [map_sum,sum_image (by intro i hi j hj; exact h hi hj)]; simp_rw [paint_notch]; rw [sum_ite_mem, univ_inter]; exact sum_congr rfl fun i hi=> by rw [hz i hi]
omit he h HQ in
private lemma note_exp (f:I→ℂ): μ (Poly.pass (Mach B f))= Poly.pass (μ (Mach B f)):=by
    let F(i:I):= if i∈S then f i else 0; let t0(i):= Poly.send (Q.fire (π i)) (F i); have hz(i:I): μ (Poly.send (B.fire i) (f i))=t0 i:=by rw [paint_notch]; dsimp only [t0,F]; split <;> simp
    unfold Mach; rw [pass_sum (tag:=B.fire) _ (fun i _=> singleton_nonempty _),paint_many (H:=HB) _ (every_notch _ _),map_sum]; simp_rw [map_add,paint_one,hz]; exact (pass_sum _ (Q.fire ∘ π) (fun i _=> singleton_nonempty _) F).symm
include hx hh
private lemma restricted_vent (p:Config G n): (vent (R:=R) x K p).part θ= (play R Q (fun i p=>bar R.activities Q p i+ ∑ j∈T, Poly.send (Q.fire j) (K' j i p)) (fun p=>∑ i∈T,Poly.send (Q.fire i) (x' i p)) p).part q:=by
    have hz:= every_notch (Q:=Q) S π
    rw [← visible T S π h he HB HQ]; unfold vent play; refine congr_arg (fun x:Poly Q=> x.part q) ?_; rw [map_smul,paint_mul _ hz HB, note_exp S π HB, paint_box _ hz HB]; apply congr_arg; apply congr_arg₂ (·*·);
    · exact congr_arg Poly.pass (notar T S π h he (fun i hi=> congr_fun (hx i hi) p))
    apply congr_arg (Accent.field · _); funext i; dsimp only [Function.comp_apply]; rw [map_add]; refine congr_arg₂ (·+·) ?_ ?_; · change μ (Poly.send B.quiet _) = Poly.send Q.quiet _; rw [paint_send]; simp [Census.quiet]; exact rain ..
    exact notar T S π h he (fun j hj=>by rw [hh j hj])
lemma rendered_again (p:Config G n): (vent (R:=R) x K p).part θ= (vent (R:=R) x' K' p).part q := by exact (restricted_vent T S π h he HB HQ hx hh p).trans (restricted_vent (I:=V) T T id Function.injective_id.injOn (Finset.image_id) HQ HQ (x:=x') (K:=K') (x':=x') (K':=K') (fun _ _=>rfl) (fun _ _=>rfl) p).symm
end
end YM.RG05.Strand
