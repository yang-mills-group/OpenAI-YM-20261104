import YM.Integration.WilsonPhysicalHistoryRetainedSpringRankIncome

/-! All subsets of a prescribed finite occupancy use a single earlier filed
state, with no additional site or period factor in the total coefficient mass. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open LocalComparison Marker Global FullQLocal IterationFour IterationFour.Vacuum
open Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat Push Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Malachite
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoherentMayerHearing WilsonPositionSeparatedProfileMayerWickInputs
open Lattice RG Pressure Pressure.Tube Tree Wilson Finset Precision Exterior Work.F03 Bid
open ConnectedActivityE6 Shell Coat Matter SliceRows Channel Push SectorMeasure Census Control Window RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open WilsonCoherentMayerHearing Dict06.Series PhysicalNext.Repeat.Malachite WilsonPositionSeparatedProfileMayerWickInputs
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato
open Dict06.Series RGLocalTaylor.Insert Work.F03 Bid
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonStartup
open scoped Topology BigOperators Classical
variable {G : Gauge}

def RootedSpringBounds (R : Run G) (m N : ℕ) (Z : SeriesA G) (r d load K : ℕ) (ε η : ℝ) : Prop :=
  ∀ per : ℕ,
    let j:=m+1
    let g:=Pert.Asymptotics.regulatorRun R.family N per j
    ∀ {u : Side} {S : StepData u (R.family.side j per)} {T : Tube G S} {F : Forest S.ratio}
      (X : Coat T F) {ι : Type} (V : Finset ι) (_ : V.card≤load) (x : ι→Site (R.family.side j per)),
      let P:=∏ i∈V,registeredSpring R N per j r Z X (x i) K g
      P.totalDegree≤V.card*(max (d+1) 3+K) ∧ Rise.coin P≤ε*g^(((3*V.card:ℕ):ℝ)-η) ∧
      ∀ z : Air (R.family.side j per) G,Cloud.paint (fun u=>z (tube X u)) P=
        ∏ i∈V,springTaylorAt R N per j r Z (x i) (angularSample F z) K g

private theorem word_scale {g ε η : ℝ} (gp : 0<g) (g1 : g≤1) (hp : 0<η) {b L : ℕ} (le : b≤L)
    (offered : 1≤ε*g^(-(η/2))) :
    (g^((3:ℝ)-η/(2*((L:ℝ)+1))))^b≤ε*g^(((3*b:ℕ):ℝ)-η) := by
  let δ:=η/(2*((L:ℝ)+1))
  have pos : 0<2*((L:ℝ)+1):=by positivity
  have rate : δ*((b:ℝ))≤η/2:=by
    calc _≤δ*((L:ℝ)+1):=mul_le_mul_of_nonneg_left ((Nat.cast_le.mpr le).trans (by linarith)) (div_nonneg hp.le pos.le)
         _=_:=by dsimp only [δ];field_simp
  rw [←Real.rpow_mul_natCast gp.le]
  have rank : ((3*b:ℕ):ℝ)=3*(b:ℝ):=by push_cast;rfl
  rw [rank]
  calc _≤g^(3*(b:ℝ)-η/2):=Real.rpow_le_rpow_of_exponent_ge gp g1 (by dsimp only [δ] at rate;linarith)
       _≤(ε*g^(-(η/2)))*g^(3*(b:ℝ)-η/2):=by
           simpa only [one_mul] using mul_le_mul_of_nonneg_right offered (Real.rpow_nonneg gp.le (3*(b:ℝ)-η/2))
       _=_:=by rw [mul_assoc,←Real.rpow_add gp];congr 2;ring

theorem cofinal_spring_words (R : Run G) (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow R.kit)
    (v : ℕ→Gear G→ℝ) (rows : FundedMarkedCoverRows.prices v R.kit) (credit : Credit) (d M r load K : ℕ)
    {ε η : ℝ} (ep : 0<ε) (hp : 0<η) :
    let V:=R.family.path.levels
    ∀ᶠ m : ℕ in atTop,∀ N : ℕ,m+1<N →
      let C:=credit.buy (zz V (m+1))+zz V (m+1)*V.clock.loopCap (m+1)
      ∀ {σ : ℝ},0<σ → σ⁻¹≤zz V (m+1) →∀ Z : SeriesA G,Draw Z σ C → Z.length≤M →
        (∀a∈Z,3≤a.grade) → (∀a∈Z,a.grade≤d) → RootedSpringBounds R m N Z r d load K ε η := by
  intro V
  let δ:=η/(2*((load:ℝ)+1))
  have pos : 0<δ:=by dsimp only [δ];positivity
  filter_upwards [cofinal_spring_rank R simple slow v rows credit d M r K zero_lt_one pos,
    cofinal_rank_factor R simple 0 1 zero_le_one ep (half_pos hp),
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small simple R.makes 1 zero_lt_one)]
    with m funded constant small
  intro N later C σ hs width Z filed size low high per j g u S T F X ι tags within x P
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N per j later.le
  have g1 : g≤1:=(small N per later.le).le
  have one (i : ι):=(registered_spring R N per j r later.le Z hs filed d high X (x i) K g)
  refine ⟨?_,?_,?_⟩
  · apply (MvPolynomial.totalDegree_finsetProd ..).trans
    calc _≤∑ _i∈tags,(max (d+1) 3+K):=sum_le_sum fun i _=>(one i).1
         _=_:=by simp
  · apply (Rise.purchased 0 zero_le_one _ _).trans
    have each (i : ι) : Rise.coin (registeredSpring R N per j r Z X (x i) K g)≤g^((3:ℝ)-δ):=by
      simpa only [one_mul] using funded N later per hs width Z filed size low high X (x i)
    calc _≤∏ _i∈tags,g^((3:ℝ)-δ):=prod_le_prod (fun i _=>Rise.sign 0 _ zero_le_one) (fun i _=>each i)
         _≤_:=by
           rw [prod_const]
           apply word_scale gp g1 hp within
           simpa only [pow_zero,mul_one] using constant N per (Nat.lt_of_succ_lt later)
  · intro z
    change Cloud.paint _ (∏ i∈tags,_) = _
    rw [map_prod]
    exact prod_congr rfl fun i _=>(one i).2.2 z

end YM.Integration.OriginalMarkedRunAction
