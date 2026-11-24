import YM.Integration.WilsonCoherentMayerPriorRequests
import YM.Integration.WilsonReportingPrescribedOldFirstCourse
import YM.Comparison.RG02.Algebra.Quotient

/-! The normalized connected complete source at the actual first nonbare successor.
The independent deposited coefficient and the complete incumbent residual are read at
the original measured program's coupling on the same field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorNonbare
open Filter Lattice Wilson RG Source Marker Precision MergeProof.Accent
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open IterationFour.Vacuum FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction AnalyticBridge.VerifiedReset.Averaging
open WilsonLimitConstruction Pert.Asymptotics ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open FullQLocal.PreRun.SuccessiveRequests RG3.Script.Picnic QLocalOriginalQHistory
open WilsonReportingPrescribedOldRawReading
open scoped Topology Classical BigOperators
open Extra.Trajectories WilsonCoherentMayerPriorSource

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] {B : MS.Local.Physical.Deck G}
  (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B)
  (Q : MS.Land.Prescription B) (μ : ℝ) (K₀ : ℕ)
  (J₀ : Request V) (A₀ : NumericSchedule R.family J₀)
local notation "JB" => ActualOriginalQPointSetup.request R u J₀
local notation "AB" => ActualOriginalQInitialInput.schedule R hG u J₀ A₀
local notation "startF" => ActualOriginalQInitialInput.input R hG u J₀ A₀

def Issued (extra : ℕ) (ord : ∀ k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
    (cap₀ : Handoff.OutputCapacities) (K₁ : NumericPrices (AB)) (r₀ : ℕ)
    (A : NumericSchedule R.family (nextRequest (JB) cap₀ r₀)) (K : NumericPrices A)
    (caps : Handoff.OutputCapacities) (degree r e : ℕ) (ε : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ (d₀ : LocalFormal.Datum R.family (Stock.census V)) (date : d₀.level=m+1),
    ∀ (b : ℕ) (fine : b≤d₀.level+1) (parents : V→Site (R.family.side b d₀.period))
      (residues : V→Site (R.family.S.toDepth fine d₀.period).count) (ks : V→ℕ), (∀ i,ks i≤K₀) →
    ∀ (period : (JB).physicalPeriodLower ≤ (R.family.S.period d₀.period).val), d₀.cutoff=d₀.level+1 →
    let sites := fun i=>(R.family.S.toDepth fine d₀.period).assemble (parents i,residues i)
    ∃ first : ActualOriginalQInitialInput.start R hG u J₀ A₀ ord ≤ d₀.level,
    ∃ I₀ : FullPreparedInputAt (startF d₀ Q sites μ ks ord first period) 0,
    Retained.NativeIntake I₀ ∧ I₀.regularPrice=0 ∧ I₀.forcedPrice=0 ∧
    ∀ (M₀ : FundedPhysicalCatalogue.Purchase cap₀ K₁ (startF d₀ Q sites μ ks ord first period))
      (S₀ : FundedRenderedBank.Chosen K₁ I₀ M₀.toCatalogue) (bank : FundedRenderedBank.Canonical S₀)
      (W : Bulk.Colors (Stock.census V) G (R.family.side (m+1) d₀.period))
      (x : Exterior.fieldDir G (R.family.side m d₀.period) 1) (q : ℕ)
      (next : FundedCoverStepPrice.Receipt R M₀ S₀ bank r₀ date A W x q),
      next.analytic.outputRadii = (fun v=>(startF d₀ Q sites μ ks ord first period).outputRadii v/A.radiusLoss m) →
    ∀ (received : FundedCoverFlatStep.Accepted R next),
    let d := ActualNextLocalDatum.descend d₀ date W x
    let J := nextRequest (JB) cap₀ r₀
    ∀ (Y : Bulk.Chain R.family.path) (M : FundedPhysicalCatalogue.Purchase caps K next.analytic),
      FundedCoverKineticMeasurement.Tested R Y next.analytic M hG (fun v=>(0 : (J.tests v).Mood)) →
    ∀ (S : FundedRenderedBank.Chosen K received.input M.toCatalogue) (t : IndependentTests J.tests),
    ∃ t₀ : IndependentTests (JB).tests, HEq (testInclusion J.tests t) (testInclusion _ t₀) ∧
    ∃ live : d.level≤d₀.level+1,

    let n := ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q sites μ ks
    let b := VariableScaling.tests (fun _=>(n:ℂ)) (testInclusion J.tests t)
    let O := S.bank.output
    let coupling := Currency.gain ((plan M.plan (degree+2*e+2+extra)).predict d.level+
      delta (S.vacuum.listing.read S.vacuum.source))
    ∀ U : Config G (R.family.side d.level d.period),
      let physical := WilsonCoherentMayerPriorSource.physical R hG u J₀ Q μ d₀ sites ks t₀ live U
      let model := (onRun R d.cutoff d.period d.level M.model r).read b coupling U
      let old := ((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹ • (O.residual.leaf b).density U
      old.part (Stock.census V).quiet ≠ 0 ∧ ∀ s : (Stock.census V).Mode,
        ‖(massLog physical - (model + massLog old)).part s‖ ≤
          ε * (regulatorRun R.family d.cutoff d.period (m+1))^((degree:ℝ)+1-J.eta)

private theorem exchange (N per j : ℕ) (live : j ≤ N) (e : ℕ) (t : ℝ) :
    let b := R.family.path.levels.clock.hatBeta j
    let g := regulatorRun R.family N per j
    b^e*g^(t+(2*e:ℕ)) ≤ (2:ℝ)^e*g^t := by
  intro b g
  let β:=R.family.path.β N per j
  have hp : 0<β:=Overlay.beta_positive R.makes.wilson live
  have gp : 0<g:=Currency.g_pos R.makes _ _ _ live
  have cp : 0≤b:=(zero_le_one.trans (R.family.path.levels.fits.delayed j).le)
  have prod : β*g^2=1 := by
    change β*(Real.sqrt β)⁻¹^2=1
    rw [inv_pow,Real.sq_sqrt hp.le,mul_inv_cancel₀ hp.ne']
  have lower : b/2≤β:=(R.makes.wilson.represents N per j live).band.1
  have cap : b*g^2≤2:=by nlinarith [mul_le_mul_of_nonneg_right lower (sq_nonneg g)]
  calc b^e*g^(t+(2*e:ℕ)) = (b*g^2)^e*g^t := by
         rw [Real.rpow_add gp,Real.rpow_natCast,mul_pow,pow_mul]
         ring
       _ ≤ (2:ℝ)^e*g^t := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg cp (sq_nonneg g)) cap e) (Real.rpow_nonneg gp.le _)

include hG in
theorem original (T : Campaign R) (attached : ActualRunNativeComponentRecipe.Attached R)
    (readout : RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ extra e : ℕ, ∀ (J₀ : Request V) (A₀ : NumericSchedule R.family J₀)
      (ord : ∀ k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
      (cap₀ : Handoff.OutputCapacities) (K₁ : NumericPrices (ActualOriginalQInitialInput.schedule R hG u J₀ A₀))
      (r₀ : ℕ) (A : NumericSchedule R.family (nextRequest (ActualOriginalQPointSetup.request R u J₀) cap₀ r₀))
      (K : NumericPrices A) (caps : Handoff.OutputCapacities) (p r : ℕ), p+2*e+2+extra≤J₀.order →
    ∀ {ε : ℝ}, 0<ε → Issued R hG u Q μ K₀ J₀ A₀ extra ord cap₀ K₁ r₀ A K caps p r e ε := by
  obtain ⟨extra,base⟩:=WilsonReportingPrescribedOldFirstCourse.original R hG u Q μ K₀ T attached readout
  obtain ⟨e,uniform⟩:=WilsonCoherentMayerPriorRequests.priced R hG u Q μ K₀
  refine ⟨extra,e,?_⟩
  intro J₀ A₀ ord cap₀ K₁ r₀ A K caps degree r
  obtain ⟨c,cp,bounds⟩:=uniform J₀
  obtain ⟨_,_,_,priced⟩:=WilsonCoherentMayerPriorSource.original R hG u J₀ Q μ K₀
  intro allowed ε ep
  let σ:=min (1/2:ℝ) (ε/(c*2^e))
  have positive : 0<σ:=lt_min (by norm_num) (div_pos ep (mul_pos cp (by positivity)))
  have spare : c*2^e*σ≤ε:=by
    rw [mul_comm,← le_div_iff₀ (mul_pos cp (by positivity))]
    exact min_le_right _ _
  have grant:=base J₀ A₀ ord cap₀ K₁ r₀ A K caps (degree+2*e) r allowed positive
  have small:=(tendsto_add_atTop_nat 1).eventually (ManuscriptQLocalKernelTariff.small R.makes hG)
  filter_upwards [grant,(tendsto_add_atTop_nat 1).eventually bounds,
    (tendsto_add_atTop_nat 1).eventually priced,small,eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)]
    with m stock bank capsold weak reference
  intro d₀ date b₀ fine parents residues ks law period cut sites
  obtain ⟨start,I₀,intake,zero,sharp,nextdata⟩:=stock d₀ date b₀ fine parents residues ks law period cut
  refine ⟨start,I₀,intake,zero,sharp,?_⟩
  intro M₀ S₀ bank₀ W x q next chosen received d J Y M contact S t
  obtain ⟨t₀,tag,live,paid⟩:=nextdata M₀ S₀ bank₀ W x q next chosen received Y M contact S t
  refine ⟨t₀,tag,live,?_⟩
  intro n b O coupling U actual model old
  let g:=regulatorRun R.family d₀.cutoff d₀.period (m+1)
  let fee:=σ*g^(((degree+2*e:ℕ):ℝ)+1-J.eta)
  have life : m+1≤d₀.cutoff:=by omega
  have gp : 0<g:=Currency.g_pos R.makes _ _ _ life
  have unit : g≤1:=weak _ _ life
  have power : 0≤((degree+2*e:ℕ):ℝ)+1-J.eta:=by linarith [J.eta_lt_half,Nat.cast_nonneg (α:=ℝ) (degree+2*e)]
  have fp : 0≤fee:=mul_nonneg positive.le (Real.rpow_nonneg gp.le _)
  have half : fee≤1/2:=calc
    _≤σ:=mul_le_of_le_one_right positive.le (Real.rpow_le_one gp.le unit power)
    _≤1/2:=min_le_left _ _
  have age:=ActualOriginalQLayout.reference_le R u (by omega : ActualOriginalQLayout.referenceLevel R u≤d₀.level+1)
  have wallet:=bank d₀ date cut age sites ks law t₀ live U model old
    ((onRun R d.cutoff d.period d.level M.model r).quiet_read b coupling U) (δ:=fee)
  have quiet:= (capsold d₀ date cut age sites ks law t₀ live U).1
  let Δ:=difference R hG u J₀ A₀ caps J A K d next.analytic received.input M S (degree+2*e+2+extra) r
    d₀ rfl live Q sites μ ks t t₀
  have same : Δ U = Poly.pass model*old-actual := by
    dsimp only [Δ,difference,model,old,actual,WilsonCoherentMayerPriorSource.physical,WilsonReportingPrescribedOldHistory.calendar]
    rw [smul_sub,mul_smul_comm,S.bank.same_model]
    rfl
  have each (s : (Stock.census V).Mode) : ‖actual.part s-(Poly.pass model*old).part s‖≤fee:=by
    have hs : ‖(Δ U).part s‖≤fee := (paid s).1 U
    rw [same] at hs
    change ‖(Poly.pass model*old).part s-actual.part s‖≤fee at hs
    exact (norm_sub_rev _ _).le.trans hs
  obtain ⟨mass,charged⟩:=wallet fp half each
  refine ⟨mass,fun s=>?_⟩
  have invoice:=charged s
  change ‖(connected actual-(model+massLog old)).part s‖≤_ at invoice
  rw [massLog,normalizeMass_fixed quiet]
  refine invoice.trans ?_
  have eq : (((degree+2*e:ℕ):ℝ)+1)-J.eta=((degree:ℝ)+1-J.eta)+(2*e:ℕ) :=by push_cast;ring
  have bound:=exchange R d₀.cutoff d₀.period (m+1) life e ((degree:ℝ)+1-J.eta)
  dsimp only [fee]
  rw [eq]
  calc c*R.family.path.levels.clock.hatBeta (m+1)^e *
       (σ*g^(((degree:ℝ)+1-J.eta)+(2*e:ℕ))) =
      c*σ*(R.family.path.levels.clock.hatBeta (m+1)^e*g^(((degree:ℝ)+1-J.eta)+(2*e:ℕ))) := by ring
    _ ≤ c*σ*((2:ℝ)^e*g^((degree:ℝ)+1-J.eta)) := mul_le_mul_of_nonneg_left bound (mul_nonneg cp.le positive.le)
    _ = (c*2^e*σ)*g^((degree:ℝ)+1-J.eta) := by ring
    _ ≤ ε*g^((degree:ℝ)+1-J.eta) := mul_le_mul_of_nonneg_right spare (Real.rpow_nonneg gp.le _)

end YM.Integration.WilsonCoherentMayerPriorNonbare
