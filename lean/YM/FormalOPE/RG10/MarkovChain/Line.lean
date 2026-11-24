import YM.FormalOPE.RG10.MultiGauge.Engineered
/-!
 # Headspace at a truss = unconstrained indices of immediate local field

 r(t_i) uses unit root orientation. Top reconstruction uses group or color variables.
 For researching locality of the conditional messages on this hierarchy only (not RG calendar)!.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.MarkovChain
open Function Filter Topology Set MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG GaussianScore
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n f c:Side}
namespace Line
variable {L:Fabric G n} (T:L.loom.Truss)
abbrev Top := { i : Orb.OEdge n // ¬ T.Branch (Sum.inl i) }
abbrev Head:= Direction G (Top T)
 def shelter (u:Top T) : T.Bulk:= ⟨.inl u.val,u.property⟩
 def send : Field T→ₗ[ℝ] Head T:= (Strong.wave (shelter T)).toLinearMap
@[simp] lemma send_eq (u:Field T) (i): send T u i= u (shelter T i):= rfl
 def headline (u: Head T) : LinkFrame G n:= fun i=> if h:¬ T.Branch (Sum.inl i) then G.lieExp (u ⟨i,h⟩) else 1
lemma portrayed (u:Field T): L.principal (T.board (expLinks G T.Bulk u))= headline T (send T u):= by
 ext1 i; unfold headline; split <;> rename_i h
 · exact Loom.Truss.stitch_bulk T (1:T.Tree→G.El) (expLinks G T.Bulk u) (shelter T ⟨i,h⟩)
 exact Loom.Truss.stitch_tree T (1:T.Tree→G.El) (expLinks G T.Bulk u) ⟨Sum.inl i,not_not.mp h⟩

-- b:t memory tied to cloth
section
variable (S:StepData c f)(H:S.patch.Branches S.kernel G)(t:S.Choices)(hf:_root_.Even f.val)(L:Fabric G c)
variable (P:Inside S.ratio)(T:L.loom.Truss)
-- prefer let via notation scoped.L avoided issues.H
local notation "T'"=> P.join T H t hf
local notation "Γ"=> Fabric.layer S H t hf L
local notation "d"=> sector S H t hf L P T

 def fastInd (i:Top T') : Index S P:= ⟨i.val, mt (P.inner_only H t hf T _).mpr i.property⟩
 def holdFast : Cross (G:=G) S P→ₗ[ℝ] Head T':= (Strong.wave (fastInd S H t hf L P T)).toLinearMap
@[simp] lemma first (u :Cross (G:=G) S P)(y:Field T): send T' (d (u,y))=holdFast S H t hf L P T u:= by ext i; rfl -- .symm subtype coe reductions
@[simp] lemma future_eq (x:Cross (G:=G) S P)(y:Field T): future S H t hf L ((T').board (expLinks G ((T').Bulk) (d (x,y))))= T.board (expLinks G T.Bulk y):= by
 ext1 i; by_cases h:T.Branch i
 · have he:= Loom.Truss.stitch_tree (T') (1:(T').Tree→G.El) (expLinks G ((T').Bulk) (d (x,y))) (⟨Sum.inr i,(P.outer_only H t hf T i).mpr h⟩)
   exact he.trans (Loom.Truss.stitch_tree T (1:T.Tree→G.El) (expLinks G T.Bulk y) ⟨i,h⟩).symm
 have he:= Loom.Truss.stitch_bulk (T') (1:(T').Tree→G.El) (expLinks G ((T').Bulk) (d (x,y))) (⟨Sum.inr i,(fun he=> h ((P.outer_only H t hf T i).mp he))⟩); exact he.trans (Loom.Truss.stitch_bulk T (1:T.Tree→G.El) (expLinks G T.Bulk y) ⟨i,h⟩).symm
end
-- section/retraction: can read ANY value of allowed head coords, not only some reconstruction.
 def place (u:Head T) (i:T.Bulk): G.Color:= match i with
 | ⟨Sum.inl x,h⟩=> u ⟨x,h⟩
 | ⟨Sum.inr _,_⟩=>0
@[simp] lemma send_place (u:Head T): send T (place T u)=u:= by ext; rfl
def importTop : Head T→ₗ[ℝ] Field T where
 toFun:=place T
 map_add' x y:=by ext1 i; cases i with | mk v hv=> cases v<;> first|rfl|simp [Line.place] -- Pi maybe
 map_smul' r u:=by ext1 i; cases i with | mk v hv=> cases v<;> first|rfl|simp [Line.place]
end Line
end YM.FormalOPE.RG10.MarkovChain
