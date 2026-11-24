import YM.OPE.Compatible.Shore.Stores
/-!
# Pump linearly to destination arrays, any seam
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
variable {V I J W X : Type}[Fintype V][DecidableEq V] [Fintype W][DecidableEq W]{G:Gauge}{n : Side}{H:RG.History G} (f:V→W)(c:V→ℂ)
variable {R:Rep G n}{o:V→Site n}{o':W→Site n}{F: V→ Config G n→ℂ}{g: V→ Box n→ Config G n→ℂ}{x y w:ℝ}{a: V→ℝ}{b: W→ℝ}{K : Support n→ Config G n→Words V}{L: Box n→ Config G n→Words V}{Y: Config G n→Words V}
def portion {X:Type}[AddCommMonoid X][Module ℂ X](F:V→X)(q:W):= ∑ i:V, if f i=q then c i • F i else 0
lemma deliver_mach (F:V→ℂ): sendAll f c (Mach (Bud V) F)=Mach (Bud W) (portion f c F):=by
    unfold Mach; rw [map_sum]; simp_rw [delivered, show ∀ i:V, (if Flat f ((Bud V).fire i) then Poly.send (landed f _) ((∏ j∈((Bud V).fire i).val,c j)*F i) else 0)=_ from fun i=> if_pos (show Flat f ((Bud V).fire i) from fun a ha b hb _=> (mem_singleton.mp (show a∈({i}:Finset V) from ha)).trans (mem_singleton.mp (show b∈({i}:Finset V) from hb)|>.symm))] -- `∀ i` can't simp
    ext1 m; rw [Poly.part_sum]; simp_rw [show ∀ i, landed f ((Bud V).fire i) = (Bud W).fire (f i) from fun i=>Subtype.ext (image_singleton ..),Poly.part_send]
    change (∑ i: V, if m=(Bud W).fire (f i) then _ else _)=(∑ i:W,Poly.send _ _).part _
    rw [Poly.part_sum]; unfold portion; simp_rw [Poly.part_send]; by_cases hp:∃ i,m=(Bud W).fire i
    · obtain ⟨i,rfl⟩:= hp
      rw [sum_eq_single i _ (by simp),if_pos rfl]; swap; · intro b _ he; exact if_neg (fun h=> he (singleton_injective (α:=W) (congr_arg Subtype.val h.symm)))
      refine sum_congr rfl fun j _=>?_ ; split_ifs
      next h h' => exact congr_arg (· * F j) (prod_singleton ..)
      next h hh => exact False.elim (hh (singleton_injective (α:=W) (congr_arg Subtype.val h.symm)))
      next h hh => subst i; contradiction
      rfl
    rw [sum_eq_zero (fun i _=> if_neg (fun h=> hp ⟨_,h⟩)),sum_eq_zero (fun i _ => if_neg (fun h=>hp ⟨_,h⟩))]
omit [DecidableEq V][Fintype W] in
lemma port_arg {p:V→ J→ℂ}(q: W)(j:J) : portion f c p q j=portion f c (fun i=>p i j) q:=by
   unfold portion; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=>by split <;> rfl
omit [DecidableEq V][Fintype W] in
lemma port_double {p:V→ J→ X→ℂ}(q: W)(j:J)(k:X): portion f c p q j k=portion f c (fun i=>p i j k) q:=by
   unfold portion; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl fun i _=>by split<;>rfl
lemma basal (A:Activities G n)(U:Config G n)(v:Box n): sendAll f c (bar A (Bud V) U v)= bar A (Bud W) U v:=by
   change sendAll _ _ (Poly.send (Bud V).quiet _)=_; rw [delivered,if_pos (show Flat f (Bud V).quiet from fun i hi=> by simp [Census.quiet] at hi),show landed f (Bud V).quiet = _ from (Subtype.ext (image_empty ..) : _=(Bud W).quiet)]; rw [show ∏ i∈(Bud V).quiet.val,c i=1 from prod_empty,one_mul]; rfl
lemma deliver_restore (hp:Carton o K L R.p.threshold) : sendAll f c ∘ restore R F g K L = restore R (portion f c F) (portion f c g) (fun i=>sendAll f c ∘ K i) (fun i=>sendAll f c ∘ L i):=by
   funext U; unfold restore; rw [Function.comp_apply,map_smul, deliver_mul,deliver_pass,map_add,deliver_mach,map_sum,field_map (sendAll f c) (deliver_one ..) (deliver_mul f c)]; simp_rw [map_add,deliver_mach,basal]; rw [show portion f c (fun i=> F i U)=(fun i=>portion f c F i U) from funext fun i=>(port_arg ..).symm]; simp_rw [show ∀ j,portion f c (fun i=>g i j U)=(fun i=>portion f c g i j U) from fun j=>funext fun i=>(port_double ..).symm]; rfl
   rw [Poly.part_plus,mute,zero_add,Poly.part_sum]; exact sum_eq_zero fun i _=> (hp.exp i).1.sil U
lemma deliver_served (h:Served R F g Y o a x y)(hp:o'∘ f=o)(ht:∀ i,0<b i)(hv:∀ i,b (f i)*‖c i‖ ≤ a i): Served R (portion f c F) (portion f c g) (sendAll f c∘Y) o' b x y:=by
   obtain ⟨E,X,h,hP,hK,rfl⟩:=h; exact ⟨_,_,deliver_pad f c h hp,deliver_tow f c hP ht hv,deliver_tow f c hK ht hv,deliver_restore f c h⟩
lemma deliver_gust {p k j N:ℕ} {y: Config G (H.S.side k p)→ Words V}(h: Integrable y (prior G _)) (ht:j ≤ k):sendAll f c∘ gust H N p k y j ht=gust H N p k (sendAll f c ∘ y) j ht:=by
   induction ht using Nat.decreasingInduction with
   | self=> rw [gust_base,gust_base]
   | of_succ i hi ih=>
      rw [gust_step _ _ _ _ _ hi,gust_step _ _ _ _ _ hi, ← ih]; funext v
      let Z:= (sendAll f c).toContinuousLinearMap.restrictScalars ℝ; change Z (_)=_; unfold StepData.push; have he:= Z.integral_comp_comm (StepData.push_slice (H.levels.transition_mass i p (H.β N p (i+1))) v _ (gust_live _ N _ _ _ h hi)); simp_rw [ContinuousLinearMap.map_smul] at he; exact he.symm
lemma deliver_birth (R:Rep G n)(F:V→ Config G n→ℂ):sendAll f c∘ birth (Bud V) R F=birth (Bud W) R (portion f c F):=by
   funext U; unfold birth; rw [Function.comp_apply,map_smul]; rw [deliver_pass _ _ _ (mute ..),deliver_mach]; rw [show portion f c (fun i=> F i U)=(fun i=>portion f c F i U) from funext fun i=>(port_arg ..).symm]
end YM.MergeProof.Ribbons.ManyCopies.Deb
