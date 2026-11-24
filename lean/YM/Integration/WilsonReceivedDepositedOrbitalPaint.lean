import YM.Integration.WilsonReceivedDepositedOrbitalPhases
import YM.Integration.WilsonOriginalCensusPolyPages

/-! The temporary array introduced on genuine copied phases is Gaussian-integrable at
every occupied and proper subset. Each constituent has the original finite polynomial
register, whether it carries a thermal label alone or an entire earlier marked word. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalPaint
open Function Filter Finset Lattice Laurent RG Wilson Stationary Primitives.TwoWave
open QuadraticLocal QuadraticLocal.Poetry QuadraticLocal.Sunrise QuadraticLocal.Earn QuadraticLocal.Sunrise.Aviary QuadraticLocal.Affinity
open Marker Next.SectorChange Multi Comparison.RG02 AllOrder AllOrder.Floe
open Further.PhysicalPeriodLimitF933 Macrame Shingle Precision Tree Exterior PhysicalNext.Repeat.Legato
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Ink WilsonCoeffUV WilsonCoeffUV.Blue PowerSeries
open WilsonOlderFreshGraphVote WilsonNeutralRenderedColumn WilsonOlderFreshGraphArmada FVA1Physical.TwoReset
open WilsonVacuumPreResetStationaryChange WilsonOriginalPrimerReplicatedInk PhysicalForestMarkedRay PhysicalForestRay
open FreeResolvent WilsonVacuumPreResetDepositedGeometric WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalPointCompactRoster WilsonOriginalThreeCopiedCharts
open scoped Classical BigOperators ContDiff Topology
open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonOriginalThreePurchasedRays (prescribed)
attribute [local instance] Gauge.frobInner
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet WilsonOriginalCensusCopySlate
open WilsonOlderFreshGraphSlate (Copy)
variable {G:Gauge} {n:Side} {V I:Type} [Fintype V] [DecidableEq V] [Fintype I]
  {P:Passport n V}(binders:I→Binder P (Stock.census V))(grades:V→ℕ)
  (R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (h:n.val∣(fine R i per).val)(x:Wallet (room V))
  (Z:I→(n:Side)→Site n→PChart G n)(B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)
local notation "J" => Stock.census V
open Function Finset Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonCoeffUV.Blue.Cameo Marker QuadraticLocal QuadraticLocal.Earn FVA1Physical.TwoReset PowerSeries
open scoped Classical BigOperators


open WilsonOriginalCensusPaidForest (ray)
open WilsonOriginalFoldedMarkedRightColumn (before)
open WilsonOriginalCensusPageRays (atLift)
open WilsonOriginalGaussianPaidTable (presented)
open MeasureTheory YM.Comparison.RG02.Cumulants

local notation "finePage" => Fin (Pages n (fine R i per))
local notation "whereFrom" => Option (I × finePage)
local notation "full" => WilsonOriginalCensusPaidForest.value binders R N i per hi F h x Z B z


open WilsonReceivedDepositedOrbitalSlice WilsonReceivedDepositedOrbitalMonomials


open WilsonReceivedDepositedOrbitalPhases
open WilsonOriginalCensusPolyPages
open private ink from YM.Integration.WilsonOriginalCensusPolyPages
open SignedRegisteredMarkedProgram (register)
local notation "S₁" => Stock.census (I×finePage)

def vacuum {r:ℕ}(t:Index r):Next.Rank.Normal.poly (Precision.Key F G):=
  if t.val.Nonempty then MvPolynomial.C (t.val.card.factorial:ℂ)*register F B
    (coeff t.val.card (relative R N i per hi F (covered R N i per))) else 0

theorem quiet {r:ℕ}(t:Index r):Cloud.paint z (vacuum R N i per hi F B t)=
    (Join.projectRight _ _ (lit (Board (J) r) (full r))).part t:=by
  rw [Join.right_projection]
  by_cases used:t.val.Nonempty
  · have both:(Join.pair (J).quiet t).val.Nonempty:=by
      obtain ⟨v,hv⟩:=used
      exact ⟨Sum.inr v,by simpa [Join.pair] using hv⟩
    rw [show (lit (Board (J) r) (full r)).part (Join.pair (J).quiet t)=full r ⟨_,both⟩ from part_lit (full r) ⟨Join.pair (J).quiet t,both⟩]
    simp only [vacuum,used,if_true,WilsonOriginalCensusPaidForest.value,Join.right_pair,Join.left_pair]
    have blank:¬(J).quiet.val.Nonempty:=Finset.not_nonempty_empty
    simp [blank,map_mul,Cloud.paint]
  · have empty:t=(indices r).quiet:=not_not.mp (fun h=>used ((hot_iff_ne _).mpr h))
    subst t
    rw [Join.pair_quiet,part_lit_quiet,vacuum,if_neg used,map_zero]

def letter {r:ℕ}(u:I×finePage)(t:Index r):Next.Rank.Normal.poly (Precision.Key F G):=
  MvPolynomial.C ((t.val.card.factorial:ℂ)*(∏v∈(binders u.1).mode.val,(x v).val))*
    register F B (coeff t.val.card
      (before R N i per hi F (Z u.1 (fine R i per) (page h (binders u.1).center u.2).val)))

omit [Fintype I] in
theorem marked {r:ℕ}(u:I×finePage)(t:Index r):
    Cloud.paint z (letter binders R N i per hi F h x Z B u t)=
      (t.val.card.factorial:ℂ)*atLift binders R N i per hi F h x Z B z u.1 u.2 t.val.card:=by
  exact (ink R i per F B z _ _).trans (mul_assoc ..)

def primitive {r:ℕ}(s:Hot (Board (S₁) r)):Next.Rank.Normal.poly (Precision.Key F G):=
  let u:=Join.left s.val
  let t:=Join.right s.val
  (if u=(S₁).quiet then vacuum R N i per hi F B t else 0)+
    ∑l:I×finePage,if u=(S₁).fire l then letter binders R N i per hi F h x Z B l t else 0

theorem attached {r:ℕ}(s:Hot (Board (S₁) r)):
    Cloud.paint z (primitive binders R N i per hi F h x Z B s)=
      (temporary binders R N i per hi F h x Z B z r).part s.val:=by
  obtain ⟨⟨u,t⟩,placed⟩:=(Join.pairs (S₁) (indices r)).surjective s.val
  change Join.pair u t=s.val at placed
  rw [primitive,←placed,Join.left_pair,Join.right_pair,temporary,WilsonReceivedDepositedOrbitalMonomials.coefficient,
    map_add,map_sum]
  congr 1
  · by_cases live:u=(S₁).quiet
    · rw [if_pos live,if_pos live,quiet binders R N i per hi F h x Z B z t]
    · rw [if_neg live,if_neg live,map_zero]
  · refine Finset.sum_congr rfl fun l _=>?_
    by_cases hit:u=(S₁).fire l
    · rw [if_pos hit,if_pos hit,marked binders R N i per hi F h x Z B z l t]; rfl
    · rw [if_neg hit,if_neg hit,map_zero]

theorem zero (r:ℕ):(temporary binders R N i per hi F h x Z B z r).part (Board (S₁) r).quiet=0:=by
  rw [←Join.pair_quiet,temporary,WilsonReceivedDepositedOrbitalMonomials.coefficient,
    if_pos rfl,Join.right_projection,Join.pair_quiet,part_lit_quiet]
  suffices ∀ l:I×finePage,(S₁).quiet ≠ (S₁).fire l by simp only [this,if_false,Finset.sum_const_zero,add_zero]
  intro l
  exact Ne.symm ((hot_iff_ne _).mp ⟨l,Finset.mem_singleton_self _⟩)

theorem original (tag:(step R i per).Choices)(r:ℕ):
    let Q₀:=(model R N i per hi).covariance F tag
    ∀s,Integrable (fun z=>((temporary binders R N i per hi F h x Z B z r).pass).part s) (Gaussian.cloud Q₀):=by
  intro Q₀
  let input:=fun z (s:Hot (Board (S₁) r))=>(temporary binders R N i per hi F h x Z B z r).part s.val
  have issued:=WilsonOriginalGaussianPaidTable.original (Board (S₁) r) Q₀ input
    ((model R N i per hi).symm F tag) ((model R N i per hi).positive F tag).posSemidef
    (primitive binders R N i per hi F h x Z B) (fun z s=>attached binders R N i per hi F h x Z B z s)
  intro s
  refine (issued.2 s).congr (Filter.Eventually.of_forall fun z=>?_)
  change ((lit (Board (S₁) r) (input z)).pass).part s=_
  apply congrArg (fun T:Grade (S₁) r=>T.pass.part s)
  exact lit_identity _ (zero binders R N i per hi F h x Z B z r)

end YM.Integration.WilsonReceivedDepositedOrbitalPaint
end
