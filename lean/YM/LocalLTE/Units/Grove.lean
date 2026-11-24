import YM.LocalLTE.Frame.Slew
import YM.LocalLTE.Tier.Crest
/-! Root-germ coordinates on native boxes, later MOVE structured.
Use arbitrary monotone parent step; fibres restricted to profile.USE positions ALL
configurations. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.FrameBox
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side} {o q : Site c} {m:ℕ}

def lad (o q : Site c) := ∑ i, (Lattice.lift (q-o) i).natAbs
lemma short (o q : Site c) : lad o q ≤ 4*separation o q:=
  (sum_le_sum (s:=univ) (g:=fun i=> separation o q) (fun i _=> (component_le _ _).trans_eq (separation_comm ..))).trans_eq (by simp [Axis])
lemma root_id (o:Site c):lad o o=0:= by simp [lad,Lattice.lift]
lemma root_pos (o q: Site c)(he:q≠o):0<lad o q:= by
  have ht:Lattice.lift (q-o)≠0:= fun h=>he (sub_eq_zero.mp ((wrap_lift (q-o)).symm.trans (h ▸ map_zero (wrap c))))
  obtain ⟨i,hx⟩:= Function.ne_iff.mp ht
  refine (Int.natAbs_pos.mpr (show _≠0 from hx)).trans_le (single_le_sum (f:=fun i=>(Lattice.lift (q-o) i).natAbs) (fun i _=> Nat.zero_le _) (mem_univ i))
lemma reduce (o q : Site c)(he:q≠o):∃ (r:Site c)(k:Step),r+k.vec=q ∧ lad o r < lad o q ∧ separation o r ≤ separation o q:= by
  let u:= Lattice.lift (q-o)
  have ht:u≠0:= fun h=>he (sub_eq_zero.mp ((wrap_lift (q-o)).symm.trans (congr_arg (wrap c) h|>.trans (map_zero (wrap c)))))
  obtain ⟨i,hx⟩:= Function.ne_iff.mp ht; change u i≠0 at hx
  let k:=if 0<u i then posDir i else negDir i; let r:= q-(k.vec)
  let v:=u - k.vec
  have hz:v i=(if 0<u i then u i-1 else u i+1):= by dsimp only [v,k]; split<;> simp
  have hh j (he:j≠i):v j=u j:= by dsimp only [v,k]; by_cases h:0<u i <;> simp [h,he]
  have hp : Lattice.lift (r-o)=v:= lift_eq_iff.mpr ⟨by unfold v; rw [map_sub, show wrap c u=q-o from wrap_lift .., wrap_vec]; unfold r; abel, fun j=> by
    by_cases h:j=i; swap; · rw [hh _ h]; exact lift_centers _ _
    rw [h,hz]; have hJ: -(c.val:ℤ)<2*u i ∧ 2*u i≤c.val:= lift_centers _ _; have hk:c.val>0:= c.property; split <;> omega⟩
  have hlt : (v i).natAbs < (u i).natAbs:= by rw [hz]; split <;> omega
  refine ⟨r,k,sub_add_cancel ..,?_,?_⟩
  · unfold lad; rw [hp]; refine Finset.sum_lt_sum (fun j _=>?_) ⟨i,mem_univ _,hlt⟩; rcases eq_or_ne j i with h|h; · rw [h]; exact hlt.le
    exact (congr_arg _ (hh _ h)).le
  rw [separation_comm o r,separation_comm o q]; unfold separation pdist; rw [hp]; refine Finset.sup_le fun j hj=>?_ ; apply le_trans _ (component_le (q-o) j); by_cases h:j=i
  · rw [h]; exact hlt.le
  exact (congr_arg _ (hh _ h)).le

-- explicit GROVE data. Determinism for Poly; need under turns may choose transported.
structure Grove (o : Site c) where
  parent : ∀ q:Site c,q≠o → Site c
  link : ∀ q:Site c,q≠o → Step
  stops q h : parent q h+(link q h).vec=q
  shrinks q h : lad o (parent q h) < lad o q
  closer q h : separation o (parent q h) ≤ separation o q

def cane (o:Site c):Grove o:=
  let r q h:= (FrameBox.reduce o q h).choose
  let V q h:= (FrameBox.reduce o q h).choose_spec
  ⟨r,fun q h=>(V q h).choose,fun q h=>(V q h).choose_spec.1,fun q h=>(V q h).choose_spec.2.1,fun q h=>(V q h).choose_spec.2.2⟩

namespace Grove
variable (X:Grove o)
-- choose walks family
def road (q:Site c): Walk:= if h:q≠o then road (X.parent q h) ++ [X.link q h] else []
  termination_by lad o q
  decreasing_by exact X.shrinks q h
lemma term (q : Site c) : stop o (X.road q)=q ∧ (X.road q).length ≤ lad o q∧
    ∀ i ∈ Lattice.visits o (X.road q), separation o i ≤ separation o q := by
  rw [road]; by_cases he:q=o; · simp [he,Lattice.visits,stop]
  rw [dif_pos he]; obtain ⟨hv,hh,hP⟩:= term (X.parent q he)
  refine ⟨?_,?_,?_⟩
  · rw [stop_append,hv]; exact X.stops q he
  · simp only [List.length_append,List.length_cons,List.length_nil]
    exact (Nat.add_le_add_right hh 1).trans (X.shrinks q he)
  intro i hi; have ht (l : Walk)(p: Site c)(k : Step): Lattice.visits p (l++[k])=(Lattice.visits p l)++[stop p l+k.vec]:= by
    induction l generalizing p <;> simp_all [Lattice.visits,stop]
  rw [ht,hv,X.stops] at hi; rcases List.mem_append.mp hi with hi|hi
  · exact (hP i hi).trans (X.closer ..)
  rw [List.mem_singleton.mp hi]
termination_by lad o q
decreasing_by exact X.shrinks _ _

def uplink (U: Config G c) (q:Site c):= travel U o (X.road q)
def fix (U:Config G c):= gauge (X.uplink U) U
lemma painted (z:Site c→G.El)(U:Config G c): X.fix (gauge z U)= gauge (fun _=> z o) (X.fix U):= by
  have he i:X.uplink (gauge z U) i=z o *X.uplink U i* (z i)⁻¹:= by unfold uplink; rw [travel_gauge,(X.term i).1]
  funext i; unfold fix; change X.uplink (gauge z U) i.1 * (z i.1*U i*(z _)⁻¹)*(X.uplink (gauge z U) _)⁻¹= z o*(X.uplink U _*U i*(X.uplink U _)⁻¹)*(z o)⁻¹; rw [he,he]; group
lemma locally {i:Site c}(hi:i∈neighbors m o): LocalOn (neighbors m o) (fun v:Config G c=>X.uplink v i):= fun _ _ h=> travel_local _ _ _ _ (agrees_mono h fun j hj=> (neighbors_mem ..).2 (((X.term i).2.2 j hj).trans ((neighbors_mem ..).1 hi)))
lemma fixes {A B:Config G c} (h:Agrees (neighbors m o:Set (Four (Per c))) A B): Agrees (neighbors m o:Set (Four (Per c))) (X.fix A) (X.fix B):=by
  intro i hi hh; unfold fix Lattice.gauge; rw [show X.uplink A _=X.uplink B _ from X.locally hi _ _ h,show X.uplink A _=X.uplink B _ from X.locally hh _ _ h,h i hi hh]

def Twig (m:ℕ) (i:Bond c):Prop := ∃ q, ∃ h : q≠o,q ∈ neighbors m o ∧ (X.link q h).used (X.parent q h) = i
lemma edge (V : Config G c) (q : Site c) (h:q≠o) : X.fix V ((X.link q h).used (X.parent q h))=1:=by
  let p:= X.parent q h; let t:= X.link q h; have hp:= X.stops q h
  have ht : X.uplink V q=X.uplink V p*t.read V p:= by
    unfold uplink p t; rw [road,dif_pos h,travel_append,(X.term _).1,travel,travel,mul_one] -- mul one
  have hh:t.read (X.fix V) p=1:= by
    rw [fix,Step.gauge_read, show p+t.vec=q from hp,ht,mul_inv_cancel]
  change X.fix V (t.used p)=1; unfold Step.read at hh; split at hh
  · exact inv_eq_one.mp hh
  exact hh
lemma fixed {V:Config G c} (hm:∀ i, X.Twig m i → V i=1) (q:Site c)(he:q∈neighbors m o): X.uplink V q=1:= by
  by_cases hp:q=o
  · rw [uplink,road,dif_neg (not_not_intro hp),travel]
  unfold uplink; rw [road,dif_pos hp,travel_append,show travel V o (X.road (X.parent q hp))=1 from fixed hm (X.parent q hp) ((neighbors_mem ..).2 ((X.closer q hp).trans ((neighbors_mem ..).1 he))), (X.term _).1,travel,travel]
  simp only [Step.read, show V _=1 from hm ((X.link q hp).used (X.parent q hp)) ⟨q,hp,he,rfl⟩,inv_one,ite_self,mul_one];
termination_by lad o q
decreasing_by exact X.shrinks _ _
end Grove
end YM.LocalLTE.FrameBox
