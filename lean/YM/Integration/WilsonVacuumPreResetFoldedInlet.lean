import YM.Integration.WilsonVacuumPreResetTorusFundedMassLimit

/-! The actual corrected Wilson roster and the periodically folded fine
cover vacuum differ by a scalar on each retained coefficient. This can be
assigned to the vacuum divisor before performing the one Gaussian push. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFoldedInlet
open Function Filter Finset Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree MeasureTheory
open ConnectedActivityE6 ConnectedActivityE6.Coat
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure
open Bloch Laurent RG.Supply Extra.Histories GapsLocal.Renew
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Opera
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Physical WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Fk Next.Foundations WilsonLimitConstruction WilsonStartup PowerSeries

open Function Filter Finset Lattice RG Wilson Pressure Precision Tree
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Winding PowerSeries
open AllOrder AllOrder.Ker Primitives.TwoWave Primitives.TwoWave.RealSlice
open Next.Foundations WilsonLimitConstruction WilsonStartup
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}

private theorem scalar (P:Ten ℝ (Woods G n) 0):
    Blue.paint 0 P=MvPolynomial.C (MvPolynomial.eval 0 (Blue.paint 0 P)):=by
  change (∑x:Fin 0→Woods G n,P x • ∏i,MvPolynomial.X (x i))=
    MvPolynomial.C (MvPolynomial.eval 0 (∑x:Fin 0→Woods G n,P x • ∏i,MvPolynomial.X (x i)))
  simp [MvPolynomial.smul_eq_C_mul]

/-- Zero angular rank is the only freedom left by filing all positive
ranks. The equality is an identity of polynomial coefficients, before
specialization to a field or integration. -/
theorem fieldIndependent (P Q:PChart G n)(t:ℕ)(bound:shellK 2 P)
    (matching:∀l,P t (l+1)=Q t (l+1)):
    coeff t (Blue.flash P-Blue.flash Q)=
      MvPolynomial.C (MvPolynomial.eval 0 (coeff t (Blue.flash P-Blue.flash Q))):=by
  have bounded:still (P t) (t+2+1):=fun a ha=>bound t a (by omega)
  have qbound:still (Q t) (t+2+1):=by
    rintro (_|l) h
    · omega
    · rw [←matching]
      exact bounded _ h
  have low:coeff t (Blue.flash P-Blue.flash Q)=Blue.paint 0 (P t 0-Q t 0):=by
    simp only [map_sub,Blue.flash,coeff_mk,Blue.visible bounded,Blue.visible qbound,
      Finset.sum_range_succ',matching,add_sub_add_left_eq_sub]
  rw [low]
  exact scalar (P t 0-Q t 0)

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit)(paths:FundedOriginalVacuumPaths.prices R.kit)
    (e:ℕ):∃ W:Credit,∀ᶠ j:ℕ in atTop,
    let A:=R.family.path.levels
    ∃σ:ℝ,0<σ ∧ σ⁻¹≤zz A j ∧ ∀N:ℕ,j≤N→
      let K:=R.alloy.B.kin.path N j
      let B:=(A.params j).clip
      let covered:=emera (actionW A R.metals.O N j)
      let C:=W.buy (zz A j)+zz A j*A.clock.loopCap j
      ∃Z:SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧
        Z.length ≤ meterPre (3+e) ∧ Draw Z σ C ∧
        ∀t≤2+e,∀c:Side,
          let Δ:=coeff t (Blue.flash (front K B c+sands Z c)-Blue.flash (covered c))
          Δ=MvPolynomial.C (MvPolynomial.eval 0 Δ):=by
  obtain ⟨W,paid⟩:=FundedOriginalVacuumPaths.corrections R simple v rows paths e
  refine ⟨W,?_⟩
  filter_upwards [paid] with j layer
  obtain ⟨h,price,width,production⟩:=layer
  refine ⟨_,price,width,?_⟩
  intro N hj
  obtain ⟨Z,grade,early,size,cash,hits⟩:=production N hj
  refine ⟨Z,grade,early,size,cash,?_⟩
  intro t ht c
  apply fieldIndependent _ _ _ (FundedSpringPeriodGerm.grade c (R.family.path.levels.params j).clip (R.alloy.B.kin.path N j) Z)
  exact (hits t (by omega)).2 c

end YM.Integration.WilsonVacuumPreResetFoldedInlet
