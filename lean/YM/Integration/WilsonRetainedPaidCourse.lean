import YM.Integration.WilsonRetainedRequestedBudget
import YM.Integration.WilsonOriginalPointTaste
import YM.Integration.ActualRunFixedOrders

/-! The same qualified old band pays the prescribed norm and the genuine marked-forced divisor,
and is merged with the actual fresh source on the same configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRetainedPaidCourse
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence WilsonRootedTwoDateProduct OPE.Therm
open WilsonLimitConstruction Push.AbsoluteSums.Animals RG.Shoot Pert.Asymptotics
open scoped Classical Topology BigOperators
open Overlay QuadraticLocal Extra.Iteration.Comparison
open PhysicalNext.Repeat.Daisy.Charity.RG12
open Pert.Asymptotics
universe u

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
  {B : MS.Local.Physical.Deck G} {R : Run G}

omit [Fintype V] [DecidableEq V] in
theorem selected_norm {T : Campaign R} {Δ : Decal G} (funded : R2I.Funded Δ R T)
    (orders : ∀ j,j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (J : Request V) (reserve : J.inputSupport ≤ 100) :
    ∀ᶠ m : ℕ in atTop, ∀ N p (_ : m<N) (A : NumericSchedule R.family J),
      HasBudget (R.family.path.rep N p (m+1)).p (A.inputNorm m) := by
  filter_upwards [ActualRunFixedOrders.eventually_orders R orders J.inputFieldOrder J.inputDistanceOrder]
    with m entered N p hm A
  let Z := ActualRunSpring.selected R N p m hm
  have native : (R.family.path.rep N p (m+1)).p = R.family.path.levels.budget (m+1) :=
    (congrArg Rep.p Z.fine).trans (Z.spring.knows Z.point.val Z.point.property).1.point
  rw [native]
  have e:=A.input_norm m
  refine ⟨⟨e.threshold.symm,e.order.le.trans entered.1,e.distance.le.trans entered.2⟩,e.block.symm,e.reserve.le.trans ?_⟩
  change J.inputSupport ≤ (R.alloy.B.a.params (m+1)).supportExponent
  rw [funded.fixed (m+1)]
  exact reserve

variable [Nonempty V] {N p m : ℕ}
variable (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m) (hG : G.Simple)
local notation "Y" => R.family.path.rep N p (m+1)
local notation "Γ" => Stock.census V
local notation "D" => (ActualOriginalQPointSetup.request R old.labels old.request).tests
local notation "g₂" => regulatorRun R.family N p (m+2)
local notation "nativeCut" => ActualRunSpring.selected R N p m fresh.below

def Purchased (amount : BudgetPoint) (prev : ℕ) : Prop :=
  ∃ τ : ℝ,0<τ ∧ τ≤1 ∧ ∃ b : Bands (Γ) (Y),
    b.origins=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots ∧
    b.units=0 ∧ b.Active ∧ Seed.RadialReceipt b τ prev ∧
    FunctionalRetains (WilsonOriginalPointTaste.representation (D) b) (fun v=>{b.origins v}) ∧
    Multilinear (D) (WilsonOriginalPointTaste.representation (D) b) ∧
    Nonempty (RelativeBudget amount (pullback (testInclusion (D)) (WilsonOriginalPointTaste.representation (D) b))
      (fun _=>τ*1) (forcedDivisor R.family (m+1)) (envelopeProduct (fun _ : V=>1))
      (Real.exp 1 * OriginalMarkedSpringBand.ordinary R (m+1) (Fintype.card V)) ((Real.sqrt 2*g₂)^(prev+1))) ∧
    (∀ (x : IndependentTests (D)) (k : (Γ).Mode) U,
      ((old.with_test x).response hG (Nat.le_succ (m+1)) U).part k=
        (∏ i∈k.val,(x i).val 0)*(((Y).eval U)⁻¹ • b.density U).part k) ∧
    ∃ (s : ℝ),0<s ∧ s≤1 ∧ ∃ (I : Type) (_ : Fintype I) (a : I→Menu.Hat (Γ) (Y)),
      GapsLocal.Full.given a 0=b.density ∧ ∃ (K : Type) (_ : Fintype K) (f : K→Menu.Hat (Γ) (Y)),
      WilsonRootedTwoDateMenu.Combined R fresh.below (nativeCut) fresh.roots (fun _=>s) a f ∧
      ∀ U,((Y).eval U)⁻¹ • GapsLocal.Full.given (Sum.elim a f) 0 U=(((Y).eval U)⁻¹ • b.density U)*fresh.masked hG U

theorem submitted (q : BudgetPoint) (compatible : HasBudget (Y).p q) (prev : ℕ)
    (enrolled : WilsonRootedTwoDatePointGallery.Common old fresh hG prev (nativeCut)) :
    Purchased old fresh hG q prev := by
  obtain ⟨τ,hτ,upper,b,birth,zero,active,radial,model,read,offer⟩:=enrolled
  have scale : 0 < forcedDivisor R.family (m+1) := Real.sqrt_pos.2 (Real.exp_pos _)
  have due := WilsonRetainedRequestedBudget.original (D) b compatible scale active radial
  refine ⟨τ,hτ,upper,b,birth,zero,active,radial,WilsonOriginalPointTaste.retains _ _ active,
    WilsonOriginalPointTaste.multilinear _ _,due,?_,?_⟩
  · intro x k U
    rw [←(model U).1]
    exact (read x k).2 U
  · obtain ⟨s,pos,small,I,ii,a,issued,K,kk,f,merged,field⟩:=offer
    refine ⟨s,pos,small,I,ii,a,issued,K,kk,f,merged,?_⟩
    intro U
    rw [←(model U).1]
    exact field U

theorem original {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {Δ : Decal G}
    (paid : FundedOriginalProperties.{u} hG ε W) (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (orders : ∀ j,j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (J : Request V) (reserve : J.inputSupport≤100) (room : 0<J.forcedConstant)
    (u v : V→MS.Rake.Label B) (prev now j : ℕ) {η : ℝ} (pos : 0<η) :
    ∀ᶠ m : ℕ in atTop,∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m)
      (A : NumericSchedule R.family J),old.labels=u → fresh.labels=v →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      Purchased old fresh hG (A.inputNorm m) prev ∧
      (Real.sqrt 2*regulatorRun R.family N p (m+2))^(prev+1)≤J.forcedConstant ∧
      ∀ x : IndependentTests (ActualOriginalQPointSetup.request R old.labels old.request).tests,
        Integrable (fun U=>Poly.price (fun _ : V=>1) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U))
          (scene R.family.path N p (m+1)) ∧
        ∫ U,Poly.price (fun _ : V=>1) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U)
          ∂scene R.family.path N p (m+1) ≤ η*(regulatorRun R.family N p (m+1))^j := by
  filter_upwards [selected_norm spring orders J reserve,WilsonRetainedPointBudget.eventually_divided hG room,
    WilsonRootedTwoDatePointGallery.original hG paid spring marks u v prev now j pos]
    with m fits bills available N p old fresh A appeared arrives roots
  obtain ⟨entry,error⟩:=available N p old fresh appeared arrives roots
  exact ⟨submitted old fresh hG _ (fits N p fresh.below A) prev entry,bills N p old.below prev,error⟩

end YM.Integration.WilsonRetainedPaidCourse

