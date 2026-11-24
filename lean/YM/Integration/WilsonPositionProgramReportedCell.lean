import YM.Integration.WilsonPositionProgramReportedUnit

/-! The scalar output is the actual center average of the full occupied
coefficient on the chosen mesh. It retains the independent child profiles. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramReportedCell
open Function Lattice RG Exterior Precision Labels Source Source.Drops Next MeasureTheory
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Fountain WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{D a:ℕ}{F:Frame G 0}{Q:Fin (a+1)→SealR G}

theorem unit (i:Alma F)(o:CellR):FaceM D (brow F i D) o=1:=by
  have eq:(notar F i).val=0:=Multiset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (notar F i).property)
  rw [brow,eq,face_at]
  change (∏ j:Axis, o.val j^(Multiset.count j 0)*((Multiset.count j 0).factorial:ℝ)⁻¹)=1
  simp

theorem original (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:0<D)
    (φ:Wilt Q)(X:Herit Q)(m N k e:ℕ)(i:Alma F):
    coeff e (Reports A Ñ T p φ X m m m N k i)=
      ∫o:CellR,(locale o (LodeStar A Ñ φ X m m N 1)).2 e 0 Fin.elim0 ∂dayMeasure := by
  rw [WilsonPositionProgramReportedUnit.original]
  have positive:A.S.a m≠0:=(A.S.a_pos m).ne'
  change HourFace dayMeasure D ((LodeStar A Ñ φ X m m N (paceT A.S m m)).2 e 0 Fin.elim0)
    (brow F i D)=_
  rw [paceT,div_self positive]
  let v: Lounge:=(LodeStar A Ñ φ X m m N 1).2 e 0 Fin.elim0
  change (∫o:CellR,v o*FaceM D (brow F i D) o ∂dayMeasure)=_
  simp_rw [unit i,mul_one]
  rfl

end YM.Integration.WilsonPositionProgramReportedCell
end
