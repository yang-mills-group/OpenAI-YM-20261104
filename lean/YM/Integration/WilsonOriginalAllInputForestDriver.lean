import YM.Integration.WilsonOriginalEarnedUnaryDriver
/-! The quiet grant and its independent constant are common to every genuine
occupied field. Their purchase uses only the charged native vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalAllInputForestDriver
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

private theorem constant_driver (e:ℕ)(Z:SeriesA G)(r:ℕ){σ cash:ℝ}
    (bank:Issued R N (i+1) e Z σ cash)(hr:r≤e+2)(s:Hot (Board C r)):
    family R N i per hi F tag Z Y (e+2) B r s =
      driver R N i per hi F tag Y B e Z r s +
      MvPolynomial.C ((register C r (credit (WilsonVacuumPreResetDepositedRay.filed R N i per Z) (covered R N i per))).part s.val):=by
  let d:=(Join.right s.val).val.card
  let fee:=credit (WilsonVacuumPreResetDepositedRay.filed R N i per Z) (covered R N i per)
  have amount:(register C r fee).part s.val=(d.factorial:ℂ)*(if Join.left s.val=C.quiet then ((coeff d fee:ℝ):ℂ) else 0):=by
    simpa only [Join.pair_reunite] using WilsonVacuumPreResetFiniteRegister.read C r fee (Join.left s.val) (Join.right s.val)
  rw [amount]
  by_cases use:(Join.left s.val).val.Nonempty
  · rw [driver,if_pos use,if_neg ((hot_iff_ne _).1 use),mul_zero,map_zero,add_zero]
  · have hq:Join.left s.val=C.quiet:=of_not_not (mt (hot_iff_ne _).2 use)
    rw [driver,if_neg use,if_pos hq]
    let U:=WilsonVacuumPreResetDepositedRay.filed R N i per Z
    have shifted:=WilsonOriginalRelativeFoldedQuiet.original R N i per hi F e Z bank d
      (by have:=Order.order_limit r (Join.right s.val);dsimp [d];omega)
    have linear: SignedRegisteredMarkedProgram.register F B (coeff d (opened R N i per hi F Z)) =
        SignedRegisteredMarkedProgram.register F B (coeff d φ) + MvPolynomial.C (((coeff d fee):ℝ):ℂ):=by
      rw [map_add] at shifted
      rw [shifted,map_add]
      congr 1
      simp [WilsonCoeffUV.Blue.holdUp,WilsonCoeffUV.Blue.holdUpPoly,soil,
        PowerSeries.coeff_map,SignedRegisteredMarkedProgram.register,fee]
    have quiet:family R N i per hi F tag Z Y (e+2) B r s =
        (d.factorial:ℂ) • SignedRegisteredMarkedProgram.register F B (coeff d (opened R N i per hi F Z)):=by
      unfold family generator
      simp only [dif_neg use]
      apply congrArg (fun p:MvPolynomial (Precision.Key F G) ℂ=>(d.factorial:ℂ) • p)
      apply Valence.Enlist.paint_inj
      intro y
      rw [SignedRegisteredMarkedProgram.reading,WilsonOriginalChargedForestQ.same_axes R i per F B y]
      exact WilsonVacuumPreResetDepositedLetters.original R N i per hi F tag Z (Bulk.Colors.noHole G (fine R i per) C)
        ((levels R).budget (i+1)) (e+2) bank.positive bank.purchase bank.lower
        (fun a ha=>by have g:=bank.upper a ha;omega) B y (Bulk.Colors.no_hole G (fine R i per) C).1 d
    rw [quiet,linear,smul_add]
    congr 1
    rw [map_mul,Algebra.smul_def]
    rfl

theorem original {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}
    (bank:Issued R N (i+1) e (Z (i+1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(r:ℕ)(hr:r≤e+2):
    let B₀':=Stationary.arm G _ 1 B₀
    let raw:=Bulk.Fk K F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) Y) B₀' r
    let full:=Cloud.prescription ((K).covariance F tag) ((K).symm F tag) 0
      (driver R N i per hi F tag Y B₀' e (Z (i+1)) r)
    ratio raw=ratio full ∧ logMarked raw=logMarked full:=by
  intro B₀' raw full
  let f:=family R N i per hi F tag (Z (i+1)) Y (e+2) B₀' r
  have same:raw=Cloud.prescription ((K).covariance F tag) ((K).symm F tag) 0 f:=by
    exact course.course.marked i lo hi per F tag Y B₀ r hr
  let scalar:=credit (WilsonVacuumPreResetDepositedRay.filed R N i per (Z (i+1))) (covered R N i per)
  have eq:ratio raw=ratio full:=by
    rw [same]
    apply WilsonOriginalScalarGaussianFold.normalized _ _ _ f _ (register C r scalar)
    · exact WilsonOriginalRegisteredFoldedDrivers.zero scalar r (WilsonOriginalRegisteredFoldedDrivers.credit_zero ..)
    · exact WilsonOriginalRegisteredFoldedDrivers.vacant scalar r
    · exact constant_driver R N i per hi F tag Y B₀' e (Z (i+1)) r bank hr
  exact ⟨eq,congrArg Extra.Trajectories.connected eq⟩
end YM.Integration.WilsonOriginalAllInputForestDriver
