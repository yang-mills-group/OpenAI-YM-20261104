import YM.OPE.Compatible.Seas.Deep
/-!
# Far wing transversality
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam.Port
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{z:(i:ℕ)→Site (U.M i)}{d:ℝ}{f g:ℕ→ Cover→ℝ}{k j:ℕ}
def diskS (a:Axis)(f:ℕ→Cover→ℝ):=shutter (-step a) (smear a (smear a f))
lemma diskS_a (x:Cover)(i:ℕ)(a:Axis):diskS a f i x=f i (x+step a)+f i (x-step a)-2*f i x:=by unfold diskS shutter smear numDiff; simp_rw [show stint a=(step a:Cover) from rfl]; rw [← sub_eq_add_neg,sub_add_cancel];ring
def Sach (g:ℕ→Cover→ℝ):Prop:=∀ x:Cover,∀ᶠ i in atTop, g i x=0
lemma mind (hs:Sach f)(a:Axis): Sach (smear a f):=by intro x; filter_upwards [hs (x+step a),hs x] with i hi hx; change f i (x+step a)-_= _; simp only [hi,hx,sub_self]
lemma might (hs:Sach f)(a:Cover): Sach (shutter a f):=fun x=> hs (x+a)
def Hum (g:ℕ→Cover→ℝ):Prop:= Sach (∑ a:Axis,diskS a g)
lemma hum_pass (h:Hum g)(x: Cover): Hum (shutter x g):=by
   unfold Hum; rw [show (∑ a:Axis,diskS a (shutter x g))= shutter x (∑ a:Axis,diskS a g) from ?_]; exact might h _
   funext i p; simp_rw [shutter,Finset.sum_apply, diskS_a]; exact Finset.sum_congr rfl (fun a _=>by unfold shutter; rw [add_right_comm p,sub_add_eq_add_sub])
lemma hum_grad (h:Hum g)(a:Axis): Hum (smear a g):=by
   unfold Hum; rw [show (∑ j:Axis,diskS j (smear a g))= smear a (∑ j:Axis,diskS j g) from ?_]; exact mind h _
   funext i p; simp_rw [Finset.sum_apply]; unfold smear numDiff; simp_rw [Finset.sum_apply, diskS_a]; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _
   rw [add_right_comm p (step j), sub_add_eq_add_sub];ring
lemma leap {E:Type*}(A:Finset E)(t:E→ℕ→Cover→ℝ)(hs:0<d)(hp:∀ i∈A, Port U d k (t i)): Port U d k (∑ i∈A, t i):=by induction A using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact Port.nullC hs
   | insert i A hi ih=> rw [Finset.sum_insert hi]; exact (hp _ (by simp)).glue (ih (fun i h=>hp i (Finset.mem_insert_of_mem h)))
lemma leapE {E:Type*}(A:Finset E)(t:E→ℕ→ Cover→ℝ)(hp:∀ i∈A, Port U d k (t i)): eve U k j (∑ i∈A,t i)=∑ i∈A, eve U k j (t i):=by induction A using Finset.induction_on with
   | empty=>simp [eve_null]
   | insert i A hi ih=>
     have he(p)(ha:p∈A):=hp p (Finset.mem_insert_of_mem ha); have ht:=hp i (Finset.mem_insert_self ..); rw [Finset.sum_insert hi,Finset.sum_insert hi, eve_plus ht (leap A _ ht.lo.inside he),ih he]
lemma glassy (hp:Port U d k g)(hs: Hum g)(j:ℕ):Spherical (eve U k j g) j:=by
   have he:=pureE U k j g; refine ⟨he,?_⟩; cases j with
   | zero=> rw [he.zeroth]; exact lap_zero _
   | succ j=>
     cases j with
     | zero=>
          funext x; unfold Extra.FD.lap; apply Finset.sum_eq_zero; intro a _; have ha:=he.derive a; erw [ha.zeroth]; simp [grad,D]
     | succ j=>
       funext x; simp_rw [Extra.FD.lap,ee_a]; have H(i:Axis): Port U d (k+2) (diskS i g):=((hp.split i).split i).pass _; have hh(i:Axis): eve U (k+1+1) j (smear i (smear i g))=eve U (k+2) j (diskS i g):= (eve_pass ((hp.split i).split i) _).symm
       simp_rw [hh,← Finset.sum_apply, ← leapE Finset.univ (fun i=> diskS i g) (fun i _=> H i)]; rw [zeroEv (leap _ _ hp.lo.inside (fun i _=> H i)) hs]
structure ShiftRay (U:Gloam)(d:ℝ)(k:ℕ)(X:Axis→ℕ→Cover→ℝ):Prop where
     ports (a:Axis):Port U d k (X a)
     glass (a):Hum (X a)
     dull: Sach (∑ a, smear a (X a))
namespace ShiftRay
variable {X:Axis→ℕ→Cover→ℝ}
lemma core (hf:ShiftRay U d k X): ∑ a:Axis, grad a (eve U k (j+1) (X a))=0:=by
   have ht(a:Axis): Port U d (k+1) (smear a (X a)):= (hf.ports _).split _; simp_rw [ee_a]; rw [← leapE _ _ (fun i _=> ht i)]; exact zeroEv (leap _ _ ((ht 0).lo.inside) (fun i _=> ht i)) hf.dull
lemma cloud (hf:ShiftRay U d k X)(j a): Spherical (eve U k j (X a)) j:= glassy (hf.ports a) (hf.glass a) _
end ShiftRay
end YM.OPE.Balsam.Port
