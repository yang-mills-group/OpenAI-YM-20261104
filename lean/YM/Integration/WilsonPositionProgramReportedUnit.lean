import YM.WilsonCoeffUV.Product.Report.ReturnBase

/-! Scalar projection at the actual reporting date.  All other sites and
source names remain in the complete conditional angular coefficient. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramReportedUnit
open Function Lattice RG Exterior Precision Labels Source Source.Drops Next
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Fountain WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open WilsonCoeffUV.Mer PowerSeries
open scoped Classical BigOperators
variable {G:Gauge}{D a:ℕ}{F:Frame G 0}{Q:Fin (a+1)→SealR G}

theorem echo (P:ChamberTen G (Vote D) 0)(i:Alma F):
    echoS F P i = (P Fin.elim0) (brow F i D) := by
  let u : Fin 0→YForest G:=Fin.elim0
  have size:valence F i=0:=Nat.eq_zero_of_le_zero (valence_cap ..)
  have base:sheet F i=0:=by
    by_contra ne
    exact (Nat.ne_of_lt (F.factors_pos _ ne)) size.symm
  have height:weave F i=0:=Nat.eq_zero_of_le_zero (F.bound (sheet F i))
  have one:seedTile (skyline 0 u 0) 0=(1:Pol G):=by
    apply eval_ext
    intro J
    rw [reads_seedTile,map_one]
    simp [WardBin.leading,Fountain.vein,Fountain.latent,Tensor.diagonal,skyline,Tensor.coeff,mite]
  have member:seedTile (skyline 0 u 0) 0∈localFields G 0:=by
    rw [one]; exact (Labels.unit G 0).property
  have detect:Bell F 0 0 (skyline 0 u 0)=F.e0:=by
    rw [detecting F _ 0 member]
    exact (congrArg F.coords (Subtype.ext one)).trans F.coords_unit
  have sum:arret (brow F i D) P 0 0=(P u (brow F i D)) • skyline 0 u 0:=by
    exact tsum_eq_single u (fun v ne=>False.elim (ne (Subsingleton.elim v u)))
  rw [echoS,trellis,height,size,base,sum,map_smul,detect]
  simp [Frame.e0,u]

theorem original (A:Levels G)(Ñ:ChartRatio G)(T:SectionData F)(p:0<D)
    (φ:Wilt Q)(X:Herit Q)(m N k e:ℕ)(i:Alma F):
    coeff e (Reports A Ñ T p φ X m m m N k i)=
      ((AutumnDay A Ñ φ X m m N D).2 e 0 Fin.elim0) (brow F i D) := by
  have size:valence F i=0:=Nat.eq_zero_of_le_zero (valence_cap ..)
  simp only [Reports,pow_zero,one_smul,Nat.sub_self,spools,steep,relativeC,leeB,
    bindingS,steepen,Matrix.one_mulVec,musical,opal,coeff_mk,glean,size]
  simpa using echo ((AutumnDay A Ñ φ X m m N D).2 e 0) i

end YM.Integration.WilsonPositionProgramReportedUnit
end
