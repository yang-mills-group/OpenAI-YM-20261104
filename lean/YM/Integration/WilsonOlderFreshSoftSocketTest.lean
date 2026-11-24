import YM.Integration.WilsonOlderFreshSoftSocketGross

/-! Exact homogeneity in the original paid angular hearing and the unconditioned gross of that same receiver. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketTest
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonThermometerDeclaredSeeds (Choice)
open WilsonReceivedFixedDigitHistory
open WilsonOlderFreshSoftOrdinary (material)
open WilsonOlderFreshSoftSocketRestored (stopped coin)
open WilsonIndependentCollarOrdinaryWeak (price)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonIndependentCollarOrdinaryCruise (address)
open WilsonCoeffUV.Winding
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(D d:I→ℕ)(p:ℕ)

open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOriginalStarSceneWords (pole)

theorem linear (S:Finset I)(N K c v:ℕ)(simple:G.Simple)(scheme:LocalRatio R.metals.O)
    (vc:v≤c)(ck:c≤K)(live:K≤N)(cells:Digits R.family.path.levels I)(y:I → Cover)
    (Y:Outerm G D)(law:Wellness d Y)(f:Pen D S→L[ℝ]ℝ)(r:ℝ):
    stopped R d N K c v cells y S (r • f) Y=r • stopped R d N K c v cells y S f Y:=by
  let Q:=levelsO (itinerary R.family.path.levels R.metals.O d N cells (K-c) c Y y) S
  have bank:=sound R.family.path.levels R.metals.O d N cells simple scheme Y law (K-c) c (by omega)
  have active:Auth (mass d S) Q:=placedO _ (bank.level' y) S
  have heard (H:Pen D S→L[ℝ]ℝ):stopped R d N K c v cells y S H Y=
      tuftV H (cruises R.family.path.levels R.metals.O N (mass d S) c v Q):=
    (cruiseT H R.family.path.levels vc simple scheme (ck.trans live) active).symm
  rw [heard,heard]
  apply Prod.ext
  · funext n j a b;rfl
  · funext j a b;rfl

theorem original (S:Finset I)(occupied:S.Nonempty)(V:Realm G (p+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
    (dorm:Dormitory V (mass d S) 0 Credit.leanC)(N K c v:ℕ)(first:V.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)
    (A B:ℝ)(front:PadRank V c K A)(march:PadRank V v c B)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:(i:I)→Choice R d i)
    (cells:Digits V.draws I)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ):
    let P:=stopped R d N K c v (cast (congrArg (fun l=>Digits l I) draw) cells) y S f (start R d κ pt q)
    WilsonReportingAbsoluteInletForecastBooks.mass p (coin P)≤ ‖f‖*gross R D d p S A B:=by
  classical
  let t:ℝ:=‖f‖
  have tn:0≤t:=f.opNorm_nonneg
  let f₀:Pen D S→L[ℝ]ℝ:=t⁻¹ • f
  have restore:t • f₀=f:=by
    by_cases z:f=0
    · simp [z,f₀]
    · have tz:t≠0:=by dsimp only [t];exact (norm_ne_zero_iff (a:=f)).mpr z
      simp [f₀,smul_smul,tz]
  have small:‖f₀‖≤1:=by
    by_cases z:f=0
    · have vanish:f₀=0:=by simp [f₀,z]
      rw [vanish,ContinuousLinearMap.opNorm_zero];norm_num
    · have tz:0<t:=by dsimp only [t];exact (norm_pos_iff (a:=f)).mpr z
      exact (ContinuousLinearMap.opNorm_smul_le _ _).trans (by change |t⁻¹| * t≤1;rw [abs_of_pos (inv_pos.mpr tz),inv_mul_cancel₀ tz.ne'])
  let X:=start R d κ pt q
  have law:Wellness d X:=((WilsonIndependentCollarPointBill.original R D d p (w:=1) zero_lt_one).choose_spec.2 κ pt q).1
  let c₀:=cast (congrArg (fun l=>Digits l I) draw) cells
  let F (a:Pen D S→L[ℝ]ℝ):=stopped R d N K c v c₀ y S a X
  have equation:F f=t • F f₀:=by
    calc F f=F (t • f₀):=congrArg F restore.symm
         _=_:=linear R D d S N K c v V.hG (paid ▸ V.green) vc ck live c₀ y X law f₀ t
  have normed:=WilsonOlderFreshSoftSocketGross.original R D d p S occupied V draw paid dorm N K c v first vc ck live
    A B front march κ pt q cells y f₀ small
  change WilsonReportingAbsoluteInletForecastBooks.mass p (coin (F f))≤t*_
  rw [equation]
  calc _=t*WilsonReportingAbsoluteInletForecastBooks.mass p (coin (F f₀)):=by
        unfold WilsonReportingAbsoluteInletForecastBooks.mass
        rw [mul_sum]
        apply sum_congr rfl
        intro i _
        simp only [coin,WilsonOlderFreshSoftSocketKinetic.reading,coeff_mk]
        change |t*(F f₀).2 i 0 Fin.elim0|=t*|(F f₀).2 i 0 Fin.elim0|
        rw [abs_mul,abs_of_nonneg tn]
       _≤_:=mul_le_mul_of_nonneg_left normed tn

end YM.Integration.WilsonOlderFreshSoftSocketTest
end
