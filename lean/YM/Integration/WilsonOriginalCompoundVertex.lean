import YM.Integration.WilsonOriginalCompoundLodge
import YM.Integration.WilsonVacuumPreResetFiniteHeatCourse
import YM.Integration.FundedMarkedCoverRows

/-! Rooted prices of the actual independently filed positive vacuum vertices on the common course. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCompoundVertex
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations WilsonCoeffUV.Bank.Ticket
open WilsonLimitConstruction.FundedCompanySelection FormalBulk08
open scoped Classical BigOperators
universe u
variable {G:Gauge}

def tariff (G:Gauge)(e a k r:ℕ)(ha:a ≤ e+1):Credit:=
  (Fk.export_domain G Credit.leanC (e+1) a k r ha).choose

def Income (R:Run G)(m a k r:ℕ)(s C:ℝ):Prop:=
  let A:=R.family.path.levels
  let O:=R.metals.O
  ∀ N N':ℕ, m ≤ N → N ≤ N' →
    let θ:ℝ:=(A.S.a N/A.S.a m)^((4:ℝ)⁻¹)
    PairA s C θ (actionW A O N m a k) (actionW A O N' m a k) ∧
    PairA s C θ (actionW A O N m a k) (timeless A O m a k) ∧
    (∀ x:YForest G,Trunk (s/2) C θ x (actionW A O N' m a (k+1)) (timeless A O m a (k+1)) r) ∧
    (m < N → PairA s C θ (freshet A O N m a k) (freshet A O N' m a k) ∧
      PairA s C θ (freshet A O N m a k) (eternal A O m a k))

/-- One enrolled realm before every cutoff, one age width before all angular ranks and roots. -/
theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)(e:ℕ):
    ∀ᶠ first:ℕ in atTop,∃Q:Realm G (e+1) Credit.leanC,Q.draws=R.family.path.levels ∧
      Q.paid=R.metals.O ∧ Q.anchor=first ∧ ∀m (hm:Q.anchor ≤ m),
      let s:=(Q.mint m hm).σ
      let z:=Borough.ageZ (R.family.path.levels.clock.hatBeta m)
      0<s ∧ s⁻¹ ≤ z ∧ ∀ a (ha:a ≤ e+1) k r,
        Income R m a k r s ((tariff G e a k r ha).buy z):=by
  filter_upwards [FundedMarkedCoverRows.realm R simple v paid 0 (fun _=>0) (fun _=>1)
    (fun _=>by decide) e 0 0] with first hfirst
  obtain ⟨Q,levels,chart,clock,ancestor,_⟩:=hfirst
  refine ⟨Q,levels,chart,ancestor,?_⟩
  intro m hm s z
  refine ⟨(Q.mint m hm).width,?_,?_⟩
  · simpa only [s,z,clock,zz,Borough.ageZ,Credit.buy,Credit.leanC,one_mul,pow_one] using
      (Q.taxes m hm).width_bill
  intro a ha k r N M date lifted θ
  have reading:=((Fk.export_domain G Credit.leanC (e+1) a k r ha).choose_spec.money Q m hm).2 N M date lifted
  obtain ⟨action,limit,trunk,shelf⟩:=reading
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [s,θ,z,tariff,clock,levels,chart,zz,Borough.ageZ] using action
  · simpa only [s,θ,z,tariff,clock,levels,chart,zz,Borough.ageZ] using limit
  · simpa only [s,θ,z,tariff,clock,levels,chart,zz,Borough.ageZ] using trunk
  intro live
  have cell:=shelf live
  simpa only [s,θ,z,tariff,clock,levels,chart,zz,Borough.ageZ] using And.intro cell.1 cell.2.1

theorem prepared (v:ℕ→Gear G→ℝ):WilsonFundedWindowMenu.AllPrices (@FundedMarkedCoverRows.prices G v):=by
  intro s price R E flags C z bt
  obtain ⟨floor,buy⟩:=FundedMarkedCoverRows.purchase v s price R E (fun i j=>(flags i j).1) C z bt
    (fun i j=>(flags i j).2.2.2.1)
  refine ⟨floor,?_⟩
  intro l hl D w u Z F S _ θ stages P menu V quarter
  obtain ⟨W,raised,issue⟩:=buy l hl D w u Z F S θ stages P V quarter
  refine ⟨W,raised,?_⟩
  intro Y hY bar wait hp B _ _ _
  dsimp only
  intro η q exchange aux rider booth hZ works hm
  exact issue Y hY bar wait hp B η q exchange menu aux rider booth hZ works hm

def Filed:Prediction G:=@FundedMarkedCoverRows.prices G (fun _ _=>0)

/-- Joint election with the actual prelength compound strip and the entire after-length forest loan. -/
theorem funded (Q:WilsonOriginalCompoundStrip.Request G)(cap U:ℕ→ℕ)(mono:Monotone cap)(simple:G.Simple){ε:ℝ}(pos:0<ε):
    WilsonOriginalCourseSupplement.Award (WilsonWindowJointPurchase.Together
      (WilsonWindowJointPurchase.Together (@WilsonOriginalCompoundStrip.Filed G Q) (@WilsonOriginalCompoundLodge.Filed G))
      (@Filed G)) (WilsonEmittedPositionSchool.funded.{u} cap U mono simple pos):=by
  apply WilsonEmittedPositionSchool.withSupplement _ _ cap U mono simple pos
  intro s price
  exact WilsonWindowJointPurchase.joint
    (WilsonWindowJointPurchase.joint
      (WilsonOriginalProfileStrip.prepaid (WilsonOriginalCompoundStrip.programme Q) simple s _)
      (WilsonEmittedDictionaryForecast.prepaid _ s _))
    (prepared (fun _ _=>0) s _)

end YM.Integration.WilsonOriginalCompoundVertex
