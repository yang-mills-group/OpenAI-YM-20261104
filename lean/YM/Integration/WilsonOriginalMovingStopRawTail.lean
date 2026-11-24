import YM.Integration.WilsonOlderFreshSoftSocketGross

/-! The raw degree tail is read at the elected original moving stop on
the same fixed-child bank at both orders, with the prior scalar retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMovingStopRawTail
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Shard
open WilsonReceivedFixedDigitHistory (Digits)
open WilsonOlderFreshSoftSocketRestored (stopped coin rated)
open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketTotal (normalized)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshHybridClock (flat)
open WilsonReportingAbsoluteInletForecastBooks (mass value)
open WilsonCoeffUV.Winding
open scoped Topology BigOperators Classical

theorem truncated (Q J:ℕ)(h:J≤Q)(g:ℝ)(positive:0≤g)(small:g≤1)(Z:PowerSeries ℝ):
    |value Q Z g-value J Z g|≤g^(J+1)*mass Q Z:=by
  let u:=fun i:ℕ=>g^i*coeff i Z
  change |(∑i∈range (Q+1),u i)-(∑i∈range (J+1),u i)|≤_
  rw [←sum_Ico_eq_sub _ (Nat.succ_le_succ h)]
  calc
    _≤∑i∈Ico (J+1) (Q+1),|u i|:=abs_sum_le_sum_abs _ _
    _≤∑i∈Ico (J+1) (Q+1),g^(J+1)*|coeff i Z|:=by
      apply sum_le_sum
      intro i hi
      rw [show |u i|=g^i*|coeff i Z| by simp [u,abs_mul,abs_of_nonneg positive]]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one positive small (mem_Ico.mp hi).1) (abs_nonneg _)
    _≤∑i∈range (Q+1),g^(J+1)*|coeff i Z|:=sum_le_sum_of_subset_of_nonneg
      (fun i hi=>mem_range.mpr (mem_Ico.mp hi).2) (fun i _ _=>mul_nonneg (pow_nonneg positive _) (abs_nonneg _))
    _=_:=by unfold WilsonReportingAbsoluteInletForecastBooks.mass;rw [mul_sum]

variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I→ℕ)(Q J:ℕ)

theorem original (retained:J≤Q)(S:Finset I)(occupied:S.Nonempty)(V:Realm G (Q+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)(dorm:Dormitory V (WilsonCoeffUV.Wheel.Mark.mass d S) 0 Credit.leanC)
    (N per K c v:ℕ)(first:V.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)
    (A B:ℝ)(front:PadRank V c K A)(march:PadRank V v c B)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
    (cells:Digits V.draws I)(w:(i:I)→R.family.label (d i))(y:I→ Cover)(f:Pen D S→L[ℝ]ℝ)(fn:‖f‖≤1)
    (g:ℝ)(positive:0≤g)(small:g≤1):
    let path:=cast (congrArg (fun l=>Digits l I) draw) cells
    let row:=normalized R d κ pt N per K c v path S w y f
    ‖row Q g-row J g‖≤(∑q:Selection R d S,‖weight R d N per K w S q‖)*
      (g^(J+1)*gross R D d Q S A B):=by
  intro path row
  let bank:=(fun q:Selection R d S=>stopped R d N K c v path y S f (start R d κ pt (fill R d S q)))
  change ‖(∑q:Selection R d S,weight R d N per K w S q*(flat (bank q) Q g:ℂ))-
      ∑q:Selection R d S,weight R d N per K w S q*(flat (bank q) J g:ℂ)‖≤_
  rw [←sum_sub_distrib,sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q _
  rw [←mul_sub,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,rated,rated]
  exact mul_le_mul_of_nonneg_left ((truncated Q J retained g positive small (coin (bank q))).trans
    (mul_le_mul_of_nonneg_left (WilsonOlderFreshSoftSocketGross.original R D d Q S occupied V draw paid dorm
      N K c v first vc ck live A B front march κ pt (fill R d S q) cells y f fn) (pow_nonneg positive _))) (norm_nonneg _)

end YM.Integration.WilsonOriginalMovingStopRawTail
