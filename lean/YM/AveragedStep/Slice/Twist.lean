import YM.AveragedStep.Moments.Spokes
import YM.Branch.Covariant
import YM.Tree.Cut
/-! # Integrating in the ROOT pins; no determinant or infinitesimal
FP identity assumed. The change on slice is V dependent, but done in the
conditional integral only (V held). The variable V of any exterior still
reads the exact same physical background. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice Wilson RG Loops Tree MeasureTheory
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)

abbrev TopologyQ (F:Forest S.ratio) (G:Gauge):=F.Slice G × Config G c
def chamber (b:Site c) (x:Board G c f): TopologyQ F G := ((F.seam (G:=G) (Loops.stamped S F b x.1 x.2)).2,x.2)
lemma chamber_meas (b:Site c):Measurable (chamber (G:=G) F b):= (((F.seam (G:=G)).measurable.comp (Loops.stamp_cont S F b).measurable).snd.prodMk measurable_snd)
-- identify gauge moves
lemma trunk_preserves (u : Config G f)(k:Site f→G.El)(h:∀ i,k (S.ratio.embed i)=1):
    Lattice.gauge (F.foldAt (Lattice.gauge k u)) (Lattice.gauge k u) = Lattice.gauge (F.foldAt u) u:= by
 funext e; unfold Lattice.gauge Forest.foldAt
 rw [show (fun e=>k _ * u e * _)=Lattice.gauge k u from rfl,travel_gauge,travel_gauge,F.hike_root,F.hike_root,h,h]
 group
lemma drape_chamber (b:Site c) (p:Board G c f) : F.drape (chamber F b p).1 = stamped S F b p.1 p.2:= by
 let U:=stamped S F b p.1 p.2
 change F.seam.symm _=U
 have he : (F.seam U).1=1:=funext fun i=> stamp_trunk S F b p.1 p.2 i
 calc
   _ = F.seam.symm ((F.seam U).1,(F.seam U).2):=by rw [he];rfl
   _ = U:= F.seam.symm_apply_apply U

set_option maxHeartbeats 140000 in
lemma packed {β:ℝ}(b:Site c)(V:Config G c)(q:TopologyQ F G→ℝ)(h:Envelope q)(hS:S.patch.Branches S.kernel G):
    let X(U:Config G f):ℝ:=S.density β U V * bare β U*q (chamber F b (U,V))
    Integrable X (prior G f) ∧ (∫ U,X U∂prior G f)=∫ z,X (F.drape z)∂F.order G:=by
 intro X
 have hh:Envelope X:= by
    let P(V':Config G f):Board G c f:=(V',V)
    have hp:Measurable P:=measurable_id.prodMk measurable_const
    have he : Envelope fun v: Board G c f=> S.density β v.1 v.2:= by
      exact Envelope.sum Finset.univ _ (weight_env S β hS)
    exact ((env_comp he hp).mul (env_continuous (bare_cont ..))).mul (env_comp h ((chamber_meas F b).comp hp))
 refine ⟨hh.integrable _, F.pack X (hh.integrable _) ?_⟩
 intro k hv U
 have h₁:S.density β (Lattice.gauge k U) V=S.density β U V:=by
   have hu: Lattice.gauge (k∘ S.ratio.embed) V=V := funext fun e=>by simp [Lattice.gauge,hv]
   simpa only [hu] using S.covary hS k β U V
 have h₂ : chamber F b (Lattice.gauge k U,V)=chamber F b (U,V):=by
   let Z:= (strung b V ∘ S.ratio.parent)
   change ((F.seam (Lattice.gauge Z _)).2, V) = ((F.seam (Lattice.gauge Z _)).2,V)
   rw [trunk_preserves F U k hv]
 change S.density β _ V * bare β _ * q _ = _; rw [h₁,bare_gauge, h₂]

-- upper gauge lift; parents at trunk endpoints equal (no claim when using ANY finite neighborhood not the Forest).
def sweep (k:Site c→G.El):MeasurableEquiv (F.Slice G) (F.Slice G) where
  toFun w i:= k (S.ratio.parent i.val.1)* w i*(k (S.ratio.parent (i.val.1+step i.val.2)))⁻¹
  invFun w i:= (k (S.ratio.parent i.val.1))⁻¹* w i*k (S.ratio.parent (i.val.1+step i.val.2))
  left_inv _:= by funext; group
  right_inv _:=by funext; group
  measurable_toFun:=by simp only [Equiv.coe_fn_mk]; fun_prop
  measurable_invFun:=by simp only [Equiv.coe_fn_symm_mk]; fun_prop
lemma sweep_measure (k:Site c→G.El):MeasurePreserving (sweep F k) (F.order G) (F.order G):= measurePreserving_pi _ _ (fun _=> G.preserve_two_sided _ _)
lemma drape_sweep (k:Site c→G.El)(w:F.Slice G):Lattice.gauge (k ∘ S.ratio.parent) (F.drape w) = F.drape (sweep F k w):=by
  funext i; by_cases h:i∈F.trunks
  · rw [show F.drape (sweep F k w) i=1 from F.on_tree _ ⟨i,h⟩]
    unfold Lattice.gauge; rw [show F.drape w i=1 from F.on_tree w ⟨i,h⟩]; simp only [Function.comp_apply]; rw [F.trunk_internal h]; simp
  rw [show F.drape (sweep F k w) i=_ from F.off_tree _ ⟨i,h⟩]; unfold Lattice.gauge sweep; dsimp only [MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,Function.comp_apply] -- check
  rw [show F.drape w i=w ⟨i,h⟩ from F.off_tree _ ⟨i,h⟩]
private lemma fold_flat (w:F.Slice G):F.foldAt (F.drape w)=1:= by
 funext i; apply Eq.trans ?_ (congrFun (show (fun _=> (1:G.El))=(1:Site f→G.El) from rfl) i)
 change (travel (F.drape w) i (F.hike i))⁻¹ = 1
 rw [show travel (F.drape w) i (F.hike i)=1 from ?_,inv_one]
 induction i using Forest.hike.induct F with
 | case1 i hi ih=>
    have he:=F.on_tree w ⟨_,(F.trunk_mem_iff _).mpr ⟨i,hi,rfl⟩⟩
    rw [Forest.hike,dif_pos hi,travel,ih]
    simp [Step.read,he]
 | case2 i hi=>rw [Forest.hike,dif_neg hi,travel]
lemma chamber_drape (b:Site c)(U:F.Slice G)(V:Config G c):chamber F b (F.drape U,V)=(sweep F (strung b V) U,V):=by
 unfold chamber stamped; dsimp only; rw [fold_flat, show Lattice.gauge 1 (F.drape U)=F.drape U from ?_, drape_sweep]
 · -- seam
   exact Prod.ext (congr_arg Prod.snd (F.seam.apply_symm_apply (1,sweep F (strung b V) U))) rfl
 funext; simp [Lattice.gauge]
