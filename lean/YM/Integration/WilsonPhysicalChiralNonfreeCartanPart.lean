import YM.Integration.WilsonPhysicalChiralNonfreeCartanAnchor

/-! Apply the physical on-shell identification after taking the very
bidegree priced on the true station. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeCartanPart
open Finset RG Labels Wilson Source Lattice Next.Rank Next.Rank.Price Next.Rank.Atlas
open Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot
open WilsonPositionThermometerGradedSource Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame
open Maxwell XSpace XSpace.Normalize Maxwell.Free ProjectorNext.Calibration MvPolynomial
open WilsonPhysicalChiralNonfreeCurvatureTest Tensor Analysis
open scoped Classical BigOperators Topology
variable {G:Gauge}{d:ℕ}

def weight (k:Maxwell.Slot G):ℕ×ℕ:=(k.1+2,1)

theorem passes (m:ℕ×ℕ)(v:Label G d):
    reduceEq (gradePart m v).val=weightedHomogeneousComponent weight m (reduceEq v.val):=
  (Maxwell.Free.commuting Labels.bidegree weight reduceEq (Maxwell.Free.reduce_grade (fun j=>((j+2,1):ℕ×ℕ)))
    v.val m).symm

theorem cubic (G:Gauge):IsWeightedHomogeneous weight (Chiral.B G) (6,3):=by
  unfold Chiral.B
  apply IsWeightedHomogeneous.sum; intro i _
  apply IsWeightedHomogeneous.sum; intro j _
  apply IsWeightedHomogeneous.sum; intro k _
  exact (weightedHomogeneousSubmodule ℂ weight (6,3)).smul_mem _ <|
    ((symbol_hom (Chiral.arm true (G:=G) i) (fun j=>((j+2,1):ℕ×ℕ))).mul
      (symbol_hom (Chiral.arm true (G:=G) j) (fun j=>((j+2,1):ℕ×ℕ)))).mul
        (symbol_hom (Chiral.arm true (G:=G) k) (fun j=>((j+2,1):ℕ×ℕ)))

theorem energy (G:Gauge):IsWeightedHomogeneous weight (Chiral.U G) (4,2):=by
  unfold Chiral.U
  apply (weightedHomogeneousSubmodule ℂ weight (4,2)).smul_mem
  apply IsWeightedHomogeneous.sum; intro i _
  exact (symbol_hom (Chiral.arm false (G:=G) i) (fun j=>((j+2,1):ℕ×ℕ))).mul
    (symbol_hom (Chiral.arm false (G:=G) i) (fun j=>((j+2,1):ℕ×ℕ)))

theorem directions (G:Gauge)(i:Fin 3):
    IsWeightedHomogeneous weight (base G i).val ((grade i).val,(grade i).val/2):=by
  fin_cases i
  · exact (weightedHomogeneousSubmodule ℂ weight (6,3)).smul_mem _ (cubic G)
  · exact (weightedHomogeneousSubmodule ℂ weight (4,2)).smul_mem _ (energy G)
  · exact (weightedHomogeneousSubmodule ℂ weight (4,2)).smul_mem _ (energy G)

theorem nominated (C:Family G)(s:Rose.Badge)(i:Fin 3)(occupied:i∈s):
    let j:=grade i
    let p:=(C.labels.level j).coords.symm (ladder C j (WilsonPositionThermometerGradedSource.source C s i))
    reduceEq (gradePart (j.val,j.val/2) p).val=(base G i).val:=by
  intro j p
  rw [passes,WilsonPhysicalChiralNonfreeCartanAnchor.named,if_pos occupied]
  exact (directions G i).weightedHomogeneousComponent_same

theorem MaxwellTest (C:Family G)(s:Rose.Badge)(i:Fin 3)(occupied:i∈s)(Q:Labels.Taylor G 0):
    let j:=grade i
    let p:=(C.labels.level j).coords.symm (ladder C j (WilsonPositionThermometerGradedSource.source C s i))
    ∃X:Maxwell.TaylorTower G,(fun n=>gaugeJet (X n))=PositionX.Tri.chunk Q ∧
    Labels.read (PositionX.Tri.chunk Q) (gradePart (j.val,j.val/2) p).val=Maxwell.probe X (base G i).val:=by
  intro j p
  obtain ⟨X,h⟩:=WilsonPhysicalChiralNonfreeCartanAnchor.tower Q
  exact ⟨X,h,by rw [←h,←Maxwell.jet_value,nominated C s i occupied]⟩

end YM.Integration.WilsonPhysicalChiralNonfreeCartanPart
