import YM.Integration.WilsonOriginalMovingStopRawTail
import YM.Integration.WilsonOlderFreshSoftSocketTest

/-! Absolute size of the actual ordinary physical truncated moment, including its zeroth coefficient, on its own Gaussian and complete original phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseRawAbsolute
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

variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I→ℕ)(Q:ℕ)

private theorem part (count top:ℕ)(kept:count≤top){x:ℝ}(xp:0≤x)(small:x≤1)(F:PowerSeries ℝ):
    |value count F x| ≤ mass top F:=by
  calc
    |value count F x|≤∑i∈range (count+1),|x^i*coeff i F|:=abs_sum_le_sum_abs _ _
    _≤∑i∈range (count+1),|coeff i F|:=by
      apply sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (pow_nonneg xp i)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ xp small)
    _ ≤ mass top F:=sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ kept)) (fun _ _ _=>abs_nonneg _)

theorem original (S:Finset I)(occupied:S.Nonempty)(V:Realm G (Q+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)(dorm:Dormitory V (WilsonCoeffUV.Wheel.Mark.mass d S) 0 Credit.leanC)
    (N per K c v:ℕ)(first:V.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)
    (A B:ℝ)(front:PadRank V c K A)(march:PadRank V v c B)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
    (cells:Digits V.draws I)(w:(i:I)→R.family.label (d i))(y:I→ Cover)(f:Pen D S→L[ℝ]ℝ)
    (g:ℝ)(positive:0≤g)(small:g≤1):
    let path:=cast (congrArg (fun l=>Digits l I) draw) cells
    let row:=normalized R d κ pt N per K c v path S w y f
    ∀j:ℕ,j≤Q → ‖row j g‖≤(∑q:Selection R d S,‖weight R d N per K w S q‖)*(‖f‖*gross R D d Q S A B):=by
  intro path row j kept
  let bank:=(fun q:Selection R d S=>stopped R d N K c v path y S f (start R d κ pt (fill R d S q)))
  change ‖∑q:Selection R d S,weight R d N per K w S q*(flat (bank q) j g:ℂ)‖≤_
  rw [sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro q _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,rated]
  exact mul_le_mul_of_nonneg_left ((part j Q kept positive small (coin (bank q))).trans
    (WilsonOlderFreshSoftSocketTest.original R D d Q S occupied V draw paid dorm
      N K c v first vc ck live A B front march κ pt (fill R d S q) cells y f)) (norm_nonneg _)

end YM.Integration.WilsonOriginalObservedRoseRawAbsolute
end
