import YM.Integration.WilsonPhysicalChiralNonfreeCartanPolarization

/-! Real closed color curvatures measuring each of the three fixed
self-dual components on the true Maxwell quotient. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeCartanColor
open Finset RG Labels Lattice Maxwell Maxwell.Free XSpace XSpace.Chiral
open WilsonPhysicalChiralNonfreeCurvatureTest Tensor Analysis
open scoped Classical BigOperators Topology InnerProductSpace
variable {G:Gauge}

def direction (p:Fin 3)(v:G.Color):PositionX.Tri.PanelL G:=fun b=>
  (q true p (six b) (endr b)/2) • v

def leg (p:Fin 3):PositionX.Tri.PanelL G→ₗ[ℝ] G.Color:=
  ∑ b:PlaqAxes, q true p (six b) (endr b) • LinearMap.proj b

theorem selected (i j:Fin 3)(v:G.Color):leg i (direction j v)=if i=j then v else 0:=by
  change (∑ b:PlaqAxes, q true i (six b) (endr b) • LinearMap.proj b) _=_
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,direction,smul_smul]
  simp_rw [div_eq_mul_inv,←mul_assoc]
  rw [←Finset.sum_smul,←Finset.sum_mul,ortho]
  by_cases h:i=j <;> simp [h]

theorem sourced (T:Maxwell.TaylorTower G)(P:Labels.Taylor G 0)
    (whereAt:gaugeJet (T 0)=P)(i:Fin 3):vₜ i T=leg i (PositionX.Tri.curτ P):=by
  have ha (b:PlaqAxes)(u:G.ColorIndex):
      cell (six b) (endr b) (faceMap 0 (cp (G:=G) u) (T 0))=PositionX.Tri.curτ P b u:=by
    rw [←whereAt]
    change ((T 0).val (six b) (endr b) (fun _=>0)) u=
      (takeCurl (gaugeJet (T 0)) (six b) (endr b) Fin.elim0) u
    rw [match_leg]
    exact congrArg (fun w=>(T 0).val (six b) (endr b) w u) (Subsingleton.elim ..)
  ext1 u
  change Fq true i (faceMap 0 (cp (G:=G) u) (T 0))=_
  simp only [Fq,leg,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.proj_apply,
    WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,ha]

theorem shots (c:Fin 3→G.Color)(S:Finset (Fin 3))(T:Maxwell.TaylorTower G)
    (held:(fun n=>gaugeJet (T n))=PositionX.Tri.chunk (chart (fun j=>direction j (c j)) S))
    (i:Fin 3): vₜ i T=if i∈S then c i else 0:=by
  have hw:gaugeJet (T 0)=chart (fun j=>direction j (c j)) S:=by
    simpa only [PositionX.Tri.chunk,Pi.single_eq_same] using congrFun held 0
  rw [sourced _ _ hw,curvature,map_sum]
  simp_rw [selected]; simp

end YM.Integration.WilsonPhysicalChiralNonfreeCartanColor
