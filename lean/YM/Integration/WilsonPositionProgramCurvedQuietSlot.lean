import YM.Integration.WilsonPositionProgramQuietDriver
import YM.Integration.WilsonPositionProgramAngularChart

/-! A changed old vacuum in the authentic nonlinear receiving chart, through any filed degree. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramCurvedQuietSlot
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange PertExtension.Series Multi Marker Comparison.RG02
open Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Order Comparison.RG02.Assembly
open WilsonPositionProgramFiledGaussianChange WilsonPositionProgramQuietDriver
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{c f:Side}{S:StepData c f}{p:Clip}{P:PathData G}{O:ChartRatio G}
  (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(tag:S.Choices)
  {V:Type}[DecidableEq V]{R:Census V}

theorem deposited (W Y:Bulk.Colors R G f)(hW:GradeAt 3 (Bulk.projected W.vac))
    (hY:GradeAt 3 (Bulk.projected Y.vac))(k:ℕ)(v:Bulk.SliceDir S F G):
    Assembly.jet (Bulk.geometric K F tag (replaced W Y)) k (1,v)-
      Assembly.jet (Bulk.geometric K F tag W) k (1,v) =
    Assembly.jet (((Bulk.projected Y.vac)-(Bulk.projected W.vac)) ∘
      WilsonPositionProgramAngularChart.chart (Work.F03.axisLog F)) k (1,v):=by
  let C:=replaced W Y
  have ready (D:Bulk.Colors R G f)(h:GradeAt 3 (Bulk.projected D.vac)):
      ContDiffAt ℝ ω (Bulk.geometric K F tag D) 0:=by
    have times:ContDiffAt ℝ ω (Bulk.pillar (S:=S) (F:=F) (G:=G)) 0:=contDiffAt_fst.pow 2
    exact (Bulk.stone_smooth K F tag).add ((times.mul (Bulk.officer_known K F).smooth).add
      (Bulk.joint_receipt S F h).smooth)
  have equal: (Bulk.geometric K F tag C-Bulk.geometric K F tag W)=ᶠ[𝓝 0]
      ((Bulk.projected Y.vac-Bulk.projected W.vac) ∘
      WilsonPositionProgramAngularChart.chart (Work.F03.axisLog F)):=by
    have prior:=continuous_snd.tendsto (0:Bulk.Joint S F (G:=G))
    filter_upwards [prior.eventually (Work.F03.inclusion_works F)] with v hv
    change Bulk.geometric K F tag (replaced W Y) v-Bulk.geometric K F tag W v=_
    rw [cost K F tag W Y]
    change _=Y.vac v.1 (represent (Work.F03.axisLog F v.2))-W.vac v.1 (represent (Work.F03.axisLog F v.2))
    rw [hv]
  unfold Assembly.jet
  rw [←(equal.iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_sub_apply ((ready C hY).of_le le_top) ((ready W hW).of_le le_top)]
  exact (smul_sub _ _ _).symm

theorem centered (W Y:Bulk.Colors R G f)(hW:GradeAt 3 (Bulk.projected W.vac))
    (hY:GradeAt 3 (Bulk.projected Y.vac))(k:ℕ)(v w:Bulk.SliceDir S F G):
    (Assembly.jet (Bulk.geometric K F tag (replaced W Y)) k (1,v)-
       Assembly.jet (Bulk.geometric K F tag W) k (1,v))-
    (Assembly.jet (Bulk.geometric K F tag (replaced W Y)) k (1,w)-
       Assembly.jet (Bulk.geometric K F tag W) k (1,w))=
    WilsonPositionProgramAngularChart.invoice (Work.F03.axisLog F)
      (Bulk.projected Y.vac-Bulk.projected W.vac) k v w:=by
  rw [deposited K F tag W Y hW hY k v,deposited K F tag W Y hW hY k w]
  exact WilsonPositionProgramAngularChart.centered _ (Work.F03.inclusion_smooth F).snd
    (congrArg Prod.snd (Work.F03.inclusion_zero F)) _ (hY.smooth.sub hW.smooth) k v w

variable [Fintype V]
theorem original (W Y:Bulk.Colors R G f)(hW:GradeAt 3 (Bulk.projected W.vac))
    (hY:GradeAt 3 (Bulk.projected Y.vac))(A:fieldDir G c 1){r:ℕ}(i:Hot (Board R r))
    (quiet:¬(Join.left i.val).val.Nonempty)(z z₀:Precision.Key F G→ℝ):
    let d:ℕ:=(Join.right i.val).val.card
    let D:=drivers K F tag (replaced W Y) A r i-drivers K F tag W A r i
    Cloud.paint z D-Cloud.paint z₀ D=
      if d=0 then 0 else -(d.factorial:ℂ)*
        (WilsonPositionProgramAngularChart.invoice (Work.F03.axisLog F)
          (Bulk.projected Y.vac-Bulk.projected W.vac) (d+2)
          (Bulk.translated K F A z).2 (Bulk.translated K F A z₀).2:ℝ):=by
  dsimp only
  rw [WilsonPositionProgramQuietDriver.quiet K F tag W Y A i quiet z,
    WilsonPositionProgramQuietDriver.quiet K F tag W Y A i quiet z₀]
  split_ifs with zero
  · simp [Assembly.vacuumLetter,zero]
  · have formula:=centered K F tag W Y hW hY ((Join.right i.val).val.card+2)
      (Bulk.translated K F A z).2 (Bulk.translated K F A z₀).2
    have footprint (a:Precision.Key F G→ℝ):Assembly.translate (Bulk.stage K F A) (Bulk.hinge F) a=
        ((1:ℝ),(Bulk.translated K F A a).2):=by
      change Bulk.translated K F A a=_
      rw [Bulk.footing]
    simp only [Assembly.vacuumLetter,if_neg zero,footprint,←formula,Complex.ofReal_sub,Complex.ofReal_neg]
    ring

end YM.Integration.WilsonPositionProgramCurvedQuietSlot
end
