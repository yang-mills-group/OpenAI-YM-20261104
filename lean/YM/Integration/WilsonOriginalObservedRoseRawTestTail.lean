import YM.Integration.WilsonOriginalMovingStopRawTail
import YM.Integration.WilsonOlderFreshSoftSocketTest

/-! High-order Taylor tail for the entire supported true finite K programme at its actual angular test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseRawTestTail
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

variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I→ℕ)(Q J:ℕ)

theorem original (retained:J≤Q)(S:Finset I)(occupied:S.Nonempty)(V:Realm G (Q+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)(dorm:Dormitory V (WilsonCoeffUV.Wheel.Mark.mass d S) 0 Credit.leanC)
    (N per K c v:ℕ)(first:V.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)
    (A B:ℝ)(front:PadRank V c K A)(march:PadRank V v c B)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
    (cells:Digits V.draws I)(w:(i:I)→R.family.label (d i))(y:I→ Cover)(f:Pen D S→L[ℝ]ℝ)
    (g:ℝ)(positive:0≤g)(small:g≤1):
    let path:=cast (congrArg (fun l=>Digits l I) draw) cells
    let row:=normalized R d κ pt N per K c v path S w y f
    ‖row Q g-row J g‖≤(∑q:Selection R d S,‖weight R d N per K w S q‖)*
      (g^(J+1)*(‖f‖*gross R D d Q S A B)):=by
  intro path row
  let bank:=(fun q:Selection R d S=>stopped R d N K c v path y S f (start R d κ pt (fill R d S q)))
  change ‖(∑q:Selection R d S,weight R d N per K w S q*(flat (bank q) Q g:ℂ))-
      ∑q:Selection R d S,weight R d N per K w S q*(flat (bank q) J g:ℂ)‖≤_
  rw [←sum_sub_distrib,sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q _
  rw [←mul_sub,norm_mul,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,rated,rated]
  exact mul_le_mul_of_nonneg_left ((WilsonOriginalMovingStopRawTail.truncated Q J retained g positive small (coin (bank q))).trans
    (mul_le_mul_of_nonneg_left (WilsonOlderFreshSoftSocketTest.original R D d Q S occupied V draw paid dorm
      N K c v first vc ck live A B front march κ pt (fill R d S q) cells y f) (pow_nonneg positive _))) (norm_nonneg _)

end YM.Integration.WilsonOriginalObservedRoseRawTestTail
end
