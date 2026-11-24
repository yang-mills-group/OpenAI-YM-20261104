import YM.Integration.WilsonThermometerUnitFilingWeakOneVertex

/-! The complete first thermal coefficient on a genuine finite older edge. The conditional expectation acting on the old degree-one mark and the single older vacuum insertion acting on the old degree-zero mark remain separate through the original reset. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakFirstScore
open Filter Finset Function Lattice Laurent RG Precision Wilson Input WilsonCoeffUV
open WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Shard WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open FreeResolvent AnalyticNext.QuarticMatch.Sheets Exterior Next.Free Tree Power Source Source.Drops
open Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm Fountain PathCost Embroider.Canvas
open PowerSeries Org PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge} {U E:Type} [Fintype U] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype U] [NormedSpace ℝ E] in
private theorem split (a:U)(P Q:Gen E U):sever a (P+Q)=sever a P+sever a Q:=by
  funext r x
  change (r+1) • ((prune (P (r+1)) a x)+(prune (Q (r+1)) a x))=_
  rw [nsmul_add];rfl

private theorem pair (C:Matrix U U ℝ)(P Q:Gen E U):ripple C (P+Q)=ripple C P+ripple C Q:=by
  simp only [ripple,split,smul_add,sum_add_distrib]

def feed (C:Matrix U U ℝ)(V:Layers ℝ U)(X:Gen E U) : ℕ→Gen E U
  | 0=>0
  | t+1=>((t+1:ℕ):ℝ)⁻¹ • (ripple C (feed C V X t)+
    (∑j∈antidiagonal t,arbor C (V j.1 1) (iceberg C X j.2))+
    ∑j∈antidiagonal t,arbor C.transpose (V j.1 1) (iceberg C X j.2))

theorem ground (C:Matrix U U ℝ)(V:Layers ℝ U)(Z:ℕ→Gen E U)(virgin:∀t,V t 0=0)(t:ℕ):
    bul C V Z t 0=iceberg C (Z 0) t:=by
  induction t with
  | zero=>rw [bul_zero];rfl
  | succ t ih=>rw [(WilsonThermometerUnitFilingWeakOneVertex.grading C V Z virgin t).1,ih];rfl

theorem first (C:Matrix U U ℝ)(V:Layers ℝ U)(Z:ℕ→Gen E U)(virgin:∀t,V t 0=0)(t:ℕ):
    bul C V Z t 1=iceberg C (Z 1) t+feed C V (Z 0) t:=by
  induction t with
  | zero=>rw [bul_zero,iceberg,feed,add_zero]
  | succ t ih=>
    rw [(WilsonThermometerUnitFilingWeakOneVertex.grading C V Z virgin t).2,ih,pair,iceberg,feed]
    simp_rw [ground C V Z virgin]
    simp only [smul_add]
    abel

theorem original (R:Run G)(N i height:ℕ)(n:Side)(w:Era G E):
    let A:=R.family.path.levels
    let p:=ll A i
    let K:=A.clock.kernel
    let S:=stepAt p K n
    let F:=xree p K n
    let H:=freeForms A N (i+1)
    let Y:=roam A N i n
    let O:=R.metals.O
    let P:=(story A O N (i+1)).1 (n*p.L)
    let C:=fillSlots (Woods G n) (covariance G S F H)
    let V:=xray S F H Y O P
    let Z:=srCold (w.1 (n*p.L)) (extractV G S F Y)
    let B:=ratioHigh A O N i
    let head:=Blue.fade plug (∑t∈range (1+height),iceberg C (Z 0) t)
    let slope:=Blue.fade plug (∑t∈range (1+height+3),(iceberg C (Z 1) t+feed C V (Z 0) t))
    ∀r, (verseI A O i N height w).1 n 1 r =
      coeff 1 ((B⁻¹)^r) • head r + coeff 0 (B*(B⁻¹)^r) • slope r:=by
  intro A p K S F H Y O P C V Z B head slope r
  let old:=w.1 (n*p.L)
  let realField:=reed S F H Y O P height old
  have virgin:∀t,V t 0=0:=bare_abr _ (pack_zero S R.alloy.B.ratio)
  have b₀:realField 0=head:=by
    change fade plug (∑t∈range (1+height+3*0),bul C V Z t 0)=_
    simp only [mul_zero,add_zero,ground C V Z virgin];rfl
  have b₁:realField 1=slope:=by
    change fade plug (∑t∈range (1+height+3*1),bul C V Z t 1)=_
    simp only [mul_one,first C V Z virgin];rfl
  change (Blue.mix B realField 1 r)=_
  simp [Blue.mix,sum_range_succ,b₀,b₁]

end YM.Integration.WilsonThermometerUnitFilingWeakFirstScore
