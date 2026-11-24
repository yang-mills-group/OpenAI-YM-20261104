import YM.Integration.WilsonPositionProgramFiledGaussianChange

/-! The original quiet cost inside the shifted lower finite Wilson kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramQuietDriver
open Function Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order
open WilsonPositionProgramFiledGaussianChange
open scoped BigOperators Classical
variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  {V:Type}[DecidableEq V][Fintype V]{R:Census V}

def replaced (W Y:Bulk.Colors R G f):Bulk.Colors R G f:={W with vac:=Y.vac}

theorem occupied (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){r:ℕ}(i:Hot (Board R r))
    (h:(Join.left i.val).val.Nonempty):
    drivers K F tag (replaced W Y) A r i=drivers K F tag W A r i:=by
  simp only [drivers,Assembly.generator,dif_pos h];rfl

theorem quiet (W Y:Bulk.Colors R G f)(A:fieldDir G c 1){r:ℕ}(i:Hot (Board R r))
    (h:¬(Join.left i.val).val.Nonempty)(z:Precision.Key F G→ℝ):
    let d:ℕ:=(Join.right i.val).val.card
    let x:=Assembly.translate (Bulk.stage K F A) (Bulk.hinge F) z
    Cloud.paint z (drivers K F tag (replaced W Y) A r i-drivers K F tag W A r i)
      =(d.factorial:ℂ)*((Assembly.vacuumLetter (Bulk.geometric K F tag (replaced W Y)) x d-
        Assembly.vacuumLetter (Bulk.geometric K F tag W) x d:ℝ):ℂ):=by
  dsimp only
  simp only [drivers,Assembly.generator,dif_neg h,map_sub,map_smul,Assembly.readingVacuum,
    smul_eq_mul,Complex.ofReal_sub,mul_sub]

omit [Fintype V] in
theorem cost (W Y:Bulk.Colors R G f)(z:Bulk.Joint S F (G:=G)):
    Bulk.geometric K F tag (replaced W Y) z-Bulk.geometric K F tag W z
      =Y.vac z.1 (Work.F03.live F z.2)-W.vac z.1 (Work.F03.live F z.2):=by
  simp only [Bulk.geometric,Bulk.fee,Bulk.supplement,Bulk.posed,replaced]
  ring

end YM.Integration.WilsonPositionProgramQuietDriver
end
