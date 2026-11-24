import YM.Integration.WilsonOlderFreshSoftSocketFare

/-! Gross scalar of the entire normalized ordinary face on its filed relative root and old quiet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketNorm
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
variable {G:Gauge}{I:Type}[Fintype I][LinearOrder I](R:Run G)(D d:I→ℕ)(p:ℕ)

open WilsonOlderFreshSoftSocketGross (gross)
open WilsonOlderFreshSoftSocketRestored (degree)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshSoftSocketFaces (fill)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketTotal (figure normalized cost)
open WilsonReportingAbsoluteInletForecastBooks (value)
open ActualRunPhysicalPages Pert.Asymptotics
local notation "g_" => regulatorRun R.family

private theorem evaluated (A:PowerSeries ℝ)(p:ℕ)(θ:ℝ)(small:|θ|≤1):
    |value p A θ|≤WilsonReportingAbsoluteInletForecastBooks.mass p A:=by
  unfold value WilsonReportingAbsoluteInletForecastBooks.mass
  apply (Finset.abs_sum_le_sum_abs ..).trans
  apply Finset.sum_le_sum
  intro a _
  rw [abs_mul,abs_pow]
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) small)

theorem original (S:Finset I)(occupied:S.Nonempty)(V:Realm G (p+1) Credit.leanC)
    (draw:V.draws=R.family.path.levels)(paid:V.paid=R.metals.O)
    (dorm:Dormitory V (mass d S) 0 Credit.leanC)(N per K c v:ℕ)
    (first:V.anchor≤v)(vc:v≤c)(ck:c≤K)(live:K≤N)(narrow:g_ N per K≤1)
    (A B:ℝ)(front:PadRank V c K A)(march:PadRank V v c B)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(w:(i:I)→R.family.label (d i))
    (cells:Digits V.draws I)(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)(θ:ℝ)(low:|θ|≤1):
    let tape:=cast (congrArg (fun l=>Digits l I) draw) cells
    ‖normalized R d κ pt N per K c v tape S w y f p θ‖≤
      (∑b:Columns R (fun i:S=>d i),‖packet R d S w N per K b‖)*
        WilsonOlderFreshSoftSocketCensus.fee R d S*(‖f‖*gross R D d p S A B):=by
  intro tape
  let Z:Selection R d S→Era G ℝ:=fun q=>stopped R d N K c v tape y S f (start R d κ pt (fill R d S q))
  let Due:=‖f‖*gross R D d p S A B
  have funded (q:Selection R d S):WilsonReportingAbsoluteInletForecastBooks.mass p (coin (Z q))≤Due:=
    WilsonOlderFreshSoftSocketTest.original R D d p S occupied V draw paid dorm N K c v first vc ck live
      A B front march κ pt (fill R d S q) cells y f
  have once (q:Selection R d S):|WilsonOlderFreshHybridClock.flat (Z q) p θ|≤Due:=by
    rw [WilsonOlderFreshSoftSocketRestored.rated]
    exact (evaluated _ _ _ low).trans (funded q)
  have good:0≤Due:=(abs_nonneg _).trans (once fun _=>Sum.inl ())
  apply (norm_sum_le ..).trans
  calc (∑q:Selection R d S,‖weight R d N per K w S q * (WilsonOlderFreshHybridClock.flat (Z q) p θ:ℂ)‖) ≤
      ∑q:Selection R d S,‖weight R d N per K w S q‖*Due:=by
        apply sum_le_sum
        intro q _
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (once q) (norm_nonneg _)
    _≤_:=by
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (WilsonOlderFreshSoftSocketCensus.original R d N per K live narrow S w) good

end YM.Integration.WilsonOlderFreshSoftSocketNorm
end
