import YM.Integration.WilsonVacuumPreResetTorusFoldedConditional

/-! One elected original path, the whole conditional finite vacuum on each enrolled
forest, and the independently filed folded input with its original covariance. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetTorusFundedConditional
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
open PhysicalNext.Repeat.Legato Exterior FreeResolvent
open scoped Classical BigOperators Topology
variable {G:Gauge}
private def reading {c:Side} (p:Ink (Woods G c))(t:ℕ)(x y:Lawn (Woods G c)):ℝ :=
  MvPolynomial.eval x (coeff t (logOf p))-MvPolynomial.eval y (coeff t (logOf p))

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)
    (rows:FundedMarkedCoverRows.prices v R.kit)(paths:FundedOriginalVacuumPaths.prices R.kit)
    (e:ℕ):∃ W:Credit,∀ᶠ i:ℕ in atTop,
    let A:=R.family.path.levels
    ∃σ:ℝ,0<σ ∧ σ⁻¹≤zz A (i+1) ∧ ∀N:ℕ,i<N→
      let K:=R.alloy.B.kin.path N (i+1)
      let B:=(A.params (i+1)).clip
      let covered:=emera (actionW A R.metals.O N (i+1))
      let C:=W.buy (zz A (i+1))+zz A (i+1)*A.clock.loopCap (i+1)
      ∃Z:SeriesA G,(∀a∈Z,3≤a.grade) ∧ fromBefore Z (3+e) ∧
        Z.length ≤ meterPre (3+e) ∧ Draw Z σ C ∧
        ∀per:ℕ,
          let S:=A.clock.op i per
          let n:=R.family.side (i+1) per
          let P:=front K B n+sands Z n
          let actual:=installed S.ratio (R.alloy.B.M.towers N i).A0
          let forecast:=installed S.ratio (predictionA A N i)
          ∀F:Forest S.ratio,∀ _tag:S.Choices,∀t≤2+e,∀x y,
            reading (inside S F (R.alloy.B.M.H N (i+1)).metric actual R.metals.O P) t x y=
              reading (inside S F (freeForms A N (i+1)) forecast R.metals.O (covered n)) t x y:=by
  obtain ⟨W,paid⟩:=WilsonVacuumPreResetFoldedInlet.original R simple v rows paths e
  obtain ⟨j₀,hj₀⟩:=eventually_atTop.1 paid
  refine ⟨W,eventually_atTop.2 ⟨j₀,?_⟩⟩
  intro i hi A
  obtain ⟨σ,pos,bound,produce⟩:=hj₀ (i+1) (by omega)
  refine ⟨σ,pos,bound,?_⟩
  intro N hN K B covered C
  obtain ⟨Z,grade,start,size,draw,field⟩:=produce N hN
  refine ⟨Z,grade,start,size,draw,?_⟩
  intro per S n P actual forecast F tag t ht x y
  have hf:shellK 2 P:=FundedSpringPeriodGerm.grade n B K Z
  have hd:shellK 2 (covered n):=(emera_far A simple R.alloy.B.ratio hN n).1
  have terms:∀j<3+e,coeff j (Blue.flash P-Blue.flash (covered n))=
      MvPolynomial.C (MvPolynomial.eval 0 (coeff j (Blue.flash P-Blue.flash (covered n)))):=
    fun j h=>field j (by omega) n
  have priced:=WilsonVacuumPreResetTorusFoldedConditional.centered S F
    (R.alloy.B.M.H N (i+1)).metric actual R.metals.O R.alloy.B.ratio
    P (covered n) hf hd terms t (by omega) x y
  change reading _ t x y=reading _ t x y at priced
  apply priced.trans
  apply congrArg (fun q=>reading q t x y)
  exact (WilsonOriginalSignedSamplerChart.original R N i per hN F tag R.metals.O (covered n) (covered n)).2.1

end YM.Integration.WilsonVacuumPreResetTorusFundedConditional
