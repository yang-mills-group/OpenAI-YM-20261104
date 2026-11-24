import YM.OPE.Compatible.Shore.Grain
/-!
# Orientation of the propagated retraction and the unfolded second
family. Need not choose same secondary permutations in the test:
only the principal requires full Harm. Keep Serves even when the
extension outside the chosen modes is not unique.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Deb
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem Mirror
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J] [Fintype W][DecidableEq W]{G:Gauge}{n : Side} (f:I→J)(c:I→ℂ)
variable {R:Rep G n}{o: V×I→Site n}{o':V×J→Site n}{F: V×I→ Config G n→ℂ}{g: V×I→ Box n→ Config G n→ℂ}{x y w:ℝ}{a: V×I→ℝ}{b: V×J→ℝ}{K : Support n→ Config G n→Words (V×I)}{L: Box n→ Config G n→Words (V×I)}{Y: Config G n→Words (V×I)}
variable (P: Ensemble V){e:V→ Site n}
def atopBy (V:Type) {I J:Type} (f:I→J) (i: V×I): V×J:= (i.1,f i.2)
section
omit [Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J] in
lemma flats {v w:V×I}: (atopBy V f) v = (atopBy V f) w ↔ v.1=w.1∧ f v.2=f w.2:= Prod.mk.injEq ..|>.to_iff
lemma delivered_focus {u:Mode (V×I)}: Focused P.v (landed (atopBy V f) u)↔ Focused P.v u:=by
    unfold Focused homes landed; simp only [image_image]; rfl
lemma rides (x:Mode (V×I))(i:Equiv.Perm V) : landed (atopBy V f) (drum i x)=drum i (landed (atopBy V f) x) := Subtype.ext (by unfold drum; simp only [landed,pares,image_image]; rfl)
omit [Fintype J][DecidableEq J] in
lemma flowers {w:Mode (V×I)}(i:Equiv.Perm V): Flat (atopBy V f) (drum i w)↔ Flat (atopBy V f) w :=by
    let A:= atopBy V f; let u:= nome (slotsZ:=I) i; let v:=nome (slotsZ:=J) i; have hh (j):A (u j)=v (A j):=rfl
    constructor
    · intro h a ha b hb he; exact u.injective (h (mem_image_of_mem u ha) (mem_image_of_mem u hb) ((hh a).trans ((congr_arg v he).trans (hh b).symm))) -- notation
    intro h a ha b hb he; obtain ⟨i,hi,rfl⟩:= mem_image.mp (show a∈ w.val.image u from ha); obtain ⟨j,hj,rfl⟩:= mem_image.mp (show b∈ w.val.image u from hb); exact congr_arg _ (h hi hj (v.injective ((hh _).symm.trans (he.trans (hh j)))))
omit [Fintype J][DecidableEq J] in
lemma orient_pay {u: Mode (V×I)} (v:V)(h:Focused P.v u):
    ∏ j∈ (drum (P.perms v) u).val, spices P c j=scalar (P.move v) (∏ i∈u.val,spices P c i):=by
    rw [drum,pares,prod_image (nome ..|>.injective.injOn)]
    rw [show scalar (P.move v) (∏ i∈u.val,spices P c i)=∏ i∈u.val,scalar (P.move v) (spices P c i) from (by unfold scalar; split_ifs <;> first|exact star_prod ..|rfl)]
    refine Finset.prod_congr rfl (fun ⟨i,j⟩ hi=>?_); have he:i=P.v:=mem_singleton.mp (h (mem_image_of_mem Prod.fst hi)); change P.echo (c j) (P.perms v i)=scalar (P.move v) (P.echo (c j) i); rw [he,P.to_ref,P.origin]; rfl
lemma deliver_harm {p q:Words (V×I)} {v:V}
    (h : Harm P.v (P.perms v) (P.move v) p q) : Harm P.v (P.perms v) (P.move v) (sendAll (atopBy V f) (spices P c) p) (sendAll (atopBy V f) (spices P c) q):=by
    intro i hi; let g:= atopBy V f; let C:= spices P c; let π:= P.perms v
    change (∑ j: Mode (V×I), if Flat g j ∧ landed g j=drum π i then (∏ w∈j.val,C w)*q.part j else 0)= scalar (P.move v) (∑ j: Mode (V×I), ite _ _ _)
    rw [← Equiv.sum_comp (drum (slotsZ:=I) π),← scales]; refine sum_congr rfl fun j _=>?_ ; have hf: (Flat g (drum π j)∧ landed g (drum π j)=drum π i)↔ Flat g j∧ landed g j=i:=⟨fun he=>⟨(flowers f π).1 he.1,(drum π).injective ((rides f j π).symm.trans he.2)⟩,fun he=>⟨(flowers f π).2 he.1,(rides f j π).trans (congr_arg _ he.2)⟩⟩
    by_cases hv:Flat g j∧ landed g j=i
    · have he:Focused P.v j:=(delivered_focus f P).mp (hv.2.symm ▸ hi); rw [if_pos hv,if_pos (hf.2 hv),orient_pay c P v he,scalar_mul,h j he]; -- order defeq
    rw [if_neg hv,if_neg (fun h=>hv (hf.1 h)), scalar_z]
lemma deliver_marked (h:ManyCopies.Serves R F g Y P.v P.move e P.perms o a x y)(hp:o'∘(atopBy V f)=o)(ht:∀ i,0<b i)(hv:∀ i,b (atopBy V f i)*‖spices P c i‖≤ a i): ManyCopies.Serves R (portion (atopBy V f) (spices P c) F) (portion (atopBy V f) (spices P c) g) (sendAll (atopBy V f) (spices P c)∘ Y) P.v P.move e P.perms o' b x y:=by
   obtain ⟨u,v,hx,hQ,hV,hW,rfl⟩:=h; exact ⟨_,_,deliver_pad _ _ hx hp,deliver_tow _ _ hQ ht hv,deliver_tow _ _ hV ht hv,fun i ht=>⟨P.to_ref _,fun U=> ⟨fun v=> deliver_harm f c P ((hW i ht).2 U|>.1 v),fun j=> deliver_harm f c P ((hW i ht).2 U|>.2 j)⟩⟩,deliver_restore _ _ hx⟩
end
end YM.MergeProof.Ribbons.ManyCopies.Deb
