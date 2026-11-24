import YM.Integration.WilsonLocalPlaquetteAction
import YM.Integration.WilsonReportingForestRelative

/-! The angular changes are the sampled relative coordinates on the original
reporting forest. Every held pivot and trunk is taken from that same forest. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteForest
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Tree RG16
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonLocalPlaquetteField
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f}

def support (T:Forest S.ratio) (E:Finset T.Free) : Finset (Bonds f) := E.image Subtype.val

def extend {α:Type} (T:Forest S.ratio) (E:Finset T.Free) (w:↥E→α) (a:α) (i:Bonds f) : α :=
  if h:i∈T.trunks then a else if he:(⟨i,h⟩:T.Free)∈E then w ⟨⟨i,h⟩,he⟩ else a

theorem held (T:Forest S.ratio) (E:Finset T.Free) (v:({e:T.Free|e∉E}:Set T.Free)→G.El)
    (w:↥E→G.El) (z:↥E→G.Color) (t:ℝ) :
    filled T E v (fun i=>G.lieExp (t•z i)*w i) =
      field (support T E) (filled T E v w) 1 (extend T E w 1) (extend T E z 0) t := by
  let x (i:↥E):=G.lieExp (t•z i)*w i
  have wet (a:↥E→G.El) (i:↥E) : filled T E v a i.val.val=a i := by
    rw [filled,T.off_tree]
    exact congrFun (congrArg Prod.fst ((cut T E).apply_symm_apply (a,v))) i
  have dry (a:↥E→G.El) (i:({e:T.Free|e∉E}:Set T.Free)) : filled T E v a i.val.val=v i := by
    rw [filled,T.off_tree]
    exact congrFun (congrArg Prod.snd ((cut T E).apply_symm_apply (a,v))) i
  funext i
  by_cases trunk:i∈T.trunks
  · have outside : i∉support T E := by
      rintro h;obtain ⟨j,_,hj⟩:=mem_image.mp h
      exact j.property (hj ▸ trunk)
    rw [field,if_neg outside];exact (T.on_tree _ ⟨i,trunk⟩).trans (T.on_tree _ ⟨i,trunk⟩).symm
  · let e:T.Free:=⟨i,trunk⟩
    by_cases selected:e∈E
    · have he : i∈support T E := mem_image_of_mem Subtype.val selected
      rw [field,if_pos he];change filled T E v x e.val=_
      rw [wet x ⟨e,selected⟩]
      simp [x,extend,trunk,e,selected]
    · have he : i∉support T E := by
        rintro h;obtain ⟨j,hj,hval⟩:=mem_image.mp h
        exact selected ((show j=e from Subtype.ext hval) ▸ hj)
      rw [field,if_neg he]
      exact (dry x ⟨e,selected⟩).trans (dry w ⟨e,selected⟩).symm

theorem entire (T:Forest S.ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (z:↥(moving T B)→G.Color) (t:ℝ) :
    restored T B v (fun i=>G.lieExp (t•z i)) =
    field (support T (moving T B)) (filled T (moving T B) v (background T B v)) 1
      (extend T (moving T B) (background T B v) 1) (extend T (moving T B) z 0) t :=
  held T (moving T B) v (background T B v) z t

theorem paid_room (T:Forest S.ratio) (E:Finset T.Free) (z:↥E→G.Color) (t:ℝ)
    (room:∀i:↥E,t*‖z i‖<1) : ∀i∈support T E,t*‖extend T E z 0 i‖<1 := by
  intro i hi;obtain ⟨j,hj,rfl⟩:=mem_image.mp hi
  simpa [extend,j.property,hj] using room ⟨j,hj⟩

end YM.Integration.WilsonLocalPlaquetteForest
