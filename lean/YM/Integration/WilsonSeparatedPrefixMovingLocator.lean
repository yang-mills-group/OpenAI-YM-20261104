import YM.Integration.WilsonSeparatedPrefixMovingOldPair
import YM.WilsonCoeffUV.Product.Report.Capture

/-! A zeroth-order locator for a previously deposited near pair. Its
genuine native site is the origin, for every displacement of the captured cell.
This test locates the existing deposit and carries no additional field. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingLocator
open WilsonCoeffUV WilsonCoeffUV.Mer Lattice RG Gauge Bloch Mer Embroider Filter Set Metric Function
open scoped Topology BigOperators Classical ContDiff

def center (y:ℝ)(o:CellR):Point4:= -(y • o.val)

def tent (c:Point4):Phrase 0:=⟨fun x=>max 0 (1-dist x c),by
  change ContDiff ℝ (0:WithTop ℕ∞) _
  rw [contDiff_zero];fun_prop⟩

theorem support (c:Point4):tsupport (tent c).val⊆Metric.closedBall c 1:=by
  apply closure_minimal _ isClosed_closedBall
  intro p hp
  by_contra out
  have gt:1<dist p c:=lt_of_not_ge out
  apply hp
  exact max_eq_left (by linarith only [gt])

theorem size (y:ℝ)(o:CellR):‖center y o‖≤|y|:=by
  unfold center
  rw [norm_neg,norm_smul,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) ((c_norm o).trans (by norm_num))

def booked (y:ℝ)(o:CellR):Rarity 0 where
  ψ:=tent (center y o)
  radius:=1+|y|
  markG:=by linarith only [abs_nonneg y]
  support:=by
    intro x p
    have away:=Metric.mem_closedBall.mp (support _ p)
    have triangle:=dist_triangle x (center y o) 0
    have limit:=size y o
    rw [dist_zero_right (center y o)] at triangle
    exact Metric.mem_closedBall.mpr (by linarith only [away,triangle,limit])

theorem site (x y:ℝ)(o:CellR)(positive:0<x): (0:Cover)∈VisitsT (booked y o) x y o:=by
  apply (visiting positive).2
  intro dead
  have paid:=congrArg (fun v:Volume 0=>FaceM 0 v zeroC) dead
  change FaceM 0 (page 0 (sonal x y o 0 (tent (center y o)))) zeroC=0 at paid
  rw [face_at] at paid
  change max 0 (1-dist (address x y o 0 0) (center y o))=0 at paid
  have ground:address x y o 0 0=center y o:=by
    unfold Mer.address Mer.position center
    have actual:actualW (0:Cover)=0:=by ext; simp [actualW]
    simp [actual]
  rw [ground,dist_self] at paid
  norm_num at paid

theorem paid (x y:ℝ)(o:CellR)(px:0≤x)(small:x≤1):
    radiusH (booked y o) x y ≤ 2+2*|y|:=by unfold radiusH booked;dsimp;rw [abs_of_nonneg px];linarith

theorem separated {D:ℕ}(ψ:Rarity D)(T gap y:ℝ)(o:CellR)
    (far:∀q∈tsupport ψ.ψ.val,T*gap+1+|y|≤‖T • q‖):
    ∀p∈tsupport (booked y o).ψ.val,∀q∈tsupport ψ.ψ.val,T*gap≤dist p (T • q):=by
  intro p hp q hq
  have hp':dist p (0:Point4)≤1+|y|:=Metric.mem_closedBall.mp ((booked y o).support hp)
  have triangle:=dist_triangle (0:Point4) p (T • q)
  rw [dist_zero_left,dist_comm (0:Point4) p] at triangle
  linarith only [triangle,hp',far q hq]

end YM.Integration.WilsonSeparatedPrefixMovingLocator
