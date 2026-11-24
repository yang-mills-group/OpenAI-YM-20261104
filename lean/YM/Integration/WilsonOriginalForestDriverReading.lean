import YM.Integration.WilsonOriginalJointForestRay
/-! The exact hot and quiet physical Gaussian driver on an arbitrary occupied source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalForestDriverReading
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series Series.Radial Series.Tested
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos Next.Rank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative credit)
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  {V:Type}[DecidableEq V][Fintype V]{C:Marker.Census V}(Y:Bulk.Colors C G (fine R i per))
local notation "S" => step R i per
local notation "K" => model R N i per hi
local notation "φ" => relative R N i per hi F (covered R N i per)
variable (B:fieldDir G (coarse R i per) 1)


open WilsonOriginalEarnedUnaryDriver (driver)
open PhysicalForestMarkedRay
variable (z:Key F G→ℝ)
theorem original (e:ℕ)(Z:SeriesA G)(well:Bulk.Well Y)(r:ℕ)(s:Hot (Board C r)):
    let j:=(Join.right s.val).val.card
    Cloud.paint z (driver R N i per hi F tag Y B e Z r s) =
      (j.factorial:ℂ) * (if use:(Join.left s.val).val.Nonempty then
        let u:Hot C:=⟨Join.left s.val,use⟩
        readJet (Y.power u+j) (chartMark (S) F (saddle R N i per F) (K) B z Y u)
      else Cloud.paint z (SignedRegisteredMarkedProgram.register F B (coeff j φ))) :=by
  intro j
  by_cases has:(Join.left s.val).val.Nonempty
  · let u:Hot C:=⟨Join.left s.val,has⟩
    unfold driver family generator
    simp only [if_pos has,dif_pos has,map_smul,smul_eq_mul]
    apply congrArg ((j.factorial:ℂ)*·)
    have field:Cloud.paint z (kernelJet (Bulk.stage (K) F B) (Bulk.hinge F)
        (Bulk.markFn (S) F Y u) (Y.power u+j))=readJet (Y.power u+j) (chartMark (S) F (saddle R N i per F) (K) B z Y u):=by
      rw [Assembly.reading]
      exact PhysicalForestMarkedRay.coefficient (S) F _ (K) B z tag Y well u (WilsonOriginalJointForestRay.swept R N i per hi F tag) _
    exact field
  · simp only [driver,if_neg has,dif_neg has,map_smul,smul_eq_mul]
    rfl

end YM.Integration.WilsonOriginalForestDriverReading
