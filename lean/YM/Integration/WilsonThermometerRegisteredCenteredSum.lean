import YM.Integration.WilsonThermometerRegisteredCenteredConnectedTest
/-! Signed connected readings against the original compact test, keeping precisely its nonzero supported microscopic cells. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredSum
open Filter Finset MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox OPE.Therm
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerFiniteConnectedCells WilsonThermometerAlignedCells
open WilsonThermometerCenteredScalar
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (simple:G.Simple)
local notation "J" => Stock.census (Fin 3)
local notation "places" z:max => Fin 3→Site (R.family.side (z:UVIndex).1 z.2)
local notation "ν" z:max i:max => OPE.Therm.scene R.family.path (z:UVIndex).1 z.2 i
local notation "source₀" age:max z:max x:max => WilsonThermometerCourseResidual.table R A simple age
  (placement R z (atOrigin (offsets x)))
local notation "χ" r:max z:max => WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z
local notation "W" φ:max r:max z:max => WilsonSeparatedOriginalThermometerCells.weight φ (χ r z)
local notation "damp" w:max F:max Q:max => WilsonThermometerRegisteredCenteredInvoice.restoration w F Q
local notation "comp" w:max F:max Q:max => WilsonThermometerRegisteredCenteredInvoice.tested w F Q

private theorem support_sum {σ:Type*} [Fintype σ] (w f:σ→ℂ):
    ∑v,w v*f v=∑v:{x:σ//w x≠0},w v.val*f v.val:=by
  classical
  rw [←Fintype.sum_subtype_add_sum_subtype (fun x:σ=>w x≠0) (fun x=>w x*f x)]
  have zero:(∑v:{x:σ//¬ w x≠0},w v.val*f v.val)=0:=Finset.sum_eq_zero fun v _=>by rw [not_ne_iff.mp v.property,zero_mul]
  rw [zero,add_zero]

theorem tested {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (unit:∀j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j)
    (z:UVIndex) (late:A.station.k<z.1) (refs:∀v:Fin 3,R.family.ref (index A (grade v))≤z.1)
    (r:ℝ) (φ:Test 3) (Q:places z→Poly J) (qu:∀x,(Q x).part (J).quiet=1)
    (lower:{x:places z//(W φ r z) x≠0}→ℂ) (charge:{x:places z//(W φ r z) x≠0}→ℝ)
    (record:∀x,‖(read (Extra.Trajectories.connected (measured R A z x.val)) univ-read (Extra.Trajectories.connected (Q x.val)) univ)-lower x‖≤charge x):
    ‖φ.applyTo (WilsonPositionThermometerGradedReading.full r A z)-WilsonThermometerFiniteConnectedCells.reference R z r φ Q-
      ∑x:{x:places z//(W φ r z) x≠0},(W φ r z) x.val*lower x‖≤∑x:{x:places z//(W φ r z) x≠0},‖(W φ r z) x.val‖*charge x:=by
  let value (x:places z):=WilsonPositionThermometerConnected.value (WilsonPositionThermometerGradedReading.row A z x)
  let ref (x:places z):=WilsonPositionThermometerConnected.value (read (Q x))
  have each (x:places z):value x-ref x=
      read (Extra.Trajectories.connected (measured R A z x)) univ-read (Extra.Trajectories.connected (Q x)) univ:=by
    rw [WilsonThermometerCenteredScalar.three _ (WilsonThermometerRegisteredCenteredConnectedTest.measured_unit R A checked unit z late refs x),
      WilsonThermometerCenteredScalar.three _ (qu x)]
    rfl
  have integrate:=WilsonSeparatedOriginalThermometerCells.tested φ (χ r z) (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)
  change ‖φ.applyTo (fun p=>value ((χ r z) p))-φ.applyTo (fun p=>ref ((χ r z) p))-_‖≤_
  rw [integrate value,integrate ref,←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  rw [support_sum (W φ r z) (fun x=>value x-ref x),←Finset.sum_sub_distrib]
  simp_rw [←mul_sub]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _=>?_ )
  rw [norm_mul,each]
  exact mul_le_mul_of_nonneg_left (record x) (norm_nonneg _)

end YM.Integration.WilsonThermometerRegisteredCenteredSum
