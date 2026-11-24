import YM.Integration.WilsonEmittedOriginalReturn
import YM.Integration.WilsonEmittedReportedRate
import YM.Integration.WilsonMeasuredSparseCatalogue
import YM.Integration.WilsonPositionProgramEmittedPupil

/-! The original paid finite census, heard at an eligible reporting date with
the complete regular and forced source on the one measured physical prior. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredAllFieldCensusReturn
open Finset Filter Lattice Wilson RG RG.Supply Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent
open QuadraticLocal.Earn.Scene AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Comparison.Density.Transport Push.Local PhysicalNext PhysicalNext.Repeat.Legato
open WilsonLimitConstruction FundedDictionaryPatchPrices WilsonEmittedDictionary
open WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue WilsonEmittedJoinedFares
open WilsonEmittedSignedTariff
open scoped BigOperators Classical
variable {G:Gauge} (tube:LinkTube G) (R:Run G) (simple:G.Simple)
local notation "levels" => R.family.path.levels
local notation "budgetAt" j:max => (levels).budget (j+1)
local notation "hatAt" j:max => (levels).clock.hatBeta (j+1)
local notation "patchAt" j:max per:max => ((levels).clock.op j per).patch
local notation "betaAt" j:max N:max per:max => (R.family.path.rep N per (j+1)).beta
local notation "couplingAt" j:max N:max per:max => (Real.sqrt (betaAt j N per))⁻¹
local notation "sideAt" j:max per:max => (levels).S.side (j+1) per
local notation "chosenGrade" d:max q:max => 2*4+(d+1)+1+(q+3)

open Source Labels Push.AbsoluteSums Pert.Asymptotics WilsonEmittedGrossTariff
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP QuadraticLocal.Sunrise
open ConnectedActivityE6 Trace.Physical PhysicalNext Repeat Legato Roost Org AnalyticBridge VerifiedReset
open WilsonEmittedOriginalReturn WilsonOlderFreshGraphSchool
include simple in
theorem original (bought:Covered (program tube) R) (strength:∀i,((levels).budget i).supportExponent ≤ 100)
    (slow:WilsonWindowReportingPace.Slow R.kit)
    (d q k:ℕ) (clear:3*(chosenGrade d q) ≤ k) {ε:ℝ} (ep:0<ε) :
    ∀ᶠ j:ℕ in atTop,∀ (m N per k₀ probe:ℕ) (π:ℕ→Layout G)(Γ₀:ℕ→Pace.Coin)
      (Ψ:(t:ℕ)→Rep G (R.family.side t per)), Concourse R.alloy R.kit R.T π Γ₀ m N per k₀ Ψ →
      m ≤ j+1 → j+1<N → probe ≤ j+1 →
    ∀ (A V:Type) [Fintype A] [DecidableEq V] (Γ:Census V)
      (I W:A→Type) (P:A→Passport (sideAt j per) V) (M:(a:A)→I a→Row (P a) Γ G (W a))
      (w:A→V→ℝ) (grades:A→V→ℕ) (x:(a:A)→W a) (c:A→ℝ)
      (ν ℓ p pieces depth height:A→ℕ) (b K σ:A→ℝ) (s:Multi.Hot Γ) (v:V)
      (L:A→Layout G) (tape:A→Finset Age) (y:Site (sideAt j per)) (mass:ℝ),
    let ζ:=fun a=>σ a/4
    (∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a)) →
    (∀a,Invoice.Supports (budgetAt j) (K a) ((budgetAt j).supportExponent+2) (couplingAt j N per) (σ a) (ζ a)) →
    (∀a,p a+depth a+1 ≤ capacity (patchAt j per) k ∧ pieces a ≤ capacity (patchAt j per) k ∧ ℓ a ≤ capacity (patchAt j per) k ∧
      height a ≤ capacity (patchAt j per) k ∧ depth a ≤ d) →
    (∀a,0 ≤ b a ∧ 0<σ a ∧ Real.exp (((σ a)⁻¹)^2) ≤ hatAt j) →
    (∀a, Real.exp ((ζ a)/2) ≤ 16*(2^(height a)*budgetR R (j+1)) ∧
      Invoice.price (budgetAt j) (K a) (p a+depth a+1) (pieces a) ((budgetAt j).supportExponent+2) (ζ a) G  ≤ 
          256*(2^(height a)*budgetR R (j+1))^3) →
    (v∈s.val.val) → (∀a,(P a).origin v=y) → 0 < mass → cash s.val w c b ≤ 34*(hatAt j)^4*mass →
    (∀e<3*(chosenGrade d q),∀u:Directions G (sideAt j per),
      (∑a:A,c a • WilsonEmittedFiledGerm.price M grades x ℓ s L tape e u a)=0) →
    (∀a,(d+1)+ν a=ℓ a+(Launch.index Γ (grades a) s.val+1)) →
    ∃z:Coefficient (R.family.labels.level d) (sideAt j per),
      z.Format y R.family.params (Ψ (j+1)) ∧
      z.remBound y (Ψ (j+1)) (LocalComparison.forcedDivisor R.family (j+1))
        (3*(ε*(regulatorRun R.family N per probe)^q)*mass) ∧
      (R.family.labels.level d).coeffSize z.x ≤ (ε*(regulatorRun R.family N per probe)^q)*mass ∧
      ∀U,z.density y (R.family.localSection d) (Ψ (j+1)) U=((Ψ (j+1)).eval U:ℂ)*
        (∑a,c a • ((Coat.gStep (Ψ (j+1)).beta)^(ν a) •
          (Spill.Foundry.uncut (M a) (Coat.gStep (Ψ (j+1)).beta) (x a) U).part s.val)) :=by
  obtain ⟨δ,live,quoted⟩:=WilsonEmittedReportedRate.funded R simple slow.2 d q ep
  have hard : 0<hardCost d:=by unfold hardCost boxCost stageCost fixedCost;positivity
  have next:=WilsonMeasuredSparseCatalogue.original R simple d (d+227) q hard ep
  filter_upwards [WilsonEmittedOriginalReturn.funded tube R simple bought strength d q k clear live,
    (tendsto_add_atTop_nat 1).eventually quoted,(tendsto_add_atTop_nat 1).eventually next]
    with j tested active ready m N per k₀ probe π Γ₀ Ψ course before below report A V fin da Γ I W P M w grades x c
      ν ℓ p pieces depth height b K σ s v L tape y mass
  dsimp only
  intro rows scope school charged stamped selected home mass0 fare read closed
  let i:=j+1
  let G₀:=Coat.gStep (Ψ i).beta
  let B:=(Ψ i).p
  have native:=course.1.walk i before below.le
  have point:B=(budgetAt j):=native.truep.point
  have stage:G₀=(couplingAt j N per):=by change Coat.gStep (Ψ i).beta=_;rw [native.beta];rfl
  have G₁:0<G₀:=by rw [stage];exact inv_pos.mpr (Real.sqrt_pos.mpr (RG02.Actual.coupling_pos R.makes.wilson below.le))
  have roots a:Invoice.Supports B (K a) (B.supportExponent+2) G₀ (σ a) (σ a/4):=by
    rw [point,stage]
    exact scope a
  obtain ⟨good,controlled,amount,short,coarse⟩:=tested N per below.le A V Γ I W P M w grades x c
    ν ℓ p pieces depth height b K σ s v L tape y mass rows scope school charged stamped selected home mass0.le fare read
  have pt₁:(Ψ (j+1)).p=(budgetAt j):=point
  have g₁:Coat.gStep (Ψ (j+1)).beta=(couplingAt j N per):=stage
  have positive:0 < (couplingAt j N per):=stage ▸ G₁
  have indexed: y∈neighborhood ((budgetAt j).B+1) y:=by
    apply halo_spec.mpr
    exact ⟨y,Finset.mem_singleton_self _,by simp⟩
  have submitted (a:A)(U:Config G (sideAt j per)):Summable (fun z=>Spill.raw (M a) G₀ (x a) z U):=by
    have staff:=WilsonEmittedFiledCatalogue.staff M w grades x B rows roots a
    exact WilsonPositionProgramEmittedPupil.paid (M a) (x a) (grades a) staff G₀ G₁.ne' U
  let scale:=WilsonEmittedOutputPower.constant (chosenGrade d q)*(cash s.val w c b*(couplingAt j N per)⁻¹)*
    (couplingAt j N per)^(chosenGrade d q)
  let cut:=(budgetAt j).B/32
  let D:=(budgetAt j).B+1
  have funded:=ready m N per k₀ probe π Γ₀ Ψ course before below report A V I W Γ P M w grades x c ν ℓ σ b K
    (fun a=>σ a/4) p pieces depth s.val v y cut D (d+1) scale mass selected mass0
  dsimp only at funded
  apply funded rows roots home indexed G₁ closed
  · simpa only [pt₁,g₁] using good
  · simpa only [pt₁,g₁] using controlled
  · exact amount
  · exact submitted
  · simpa only [pt₁,g₁] using coarse
  · let Z:=reservedMass (budgetAt j) (neighborhood D y) (‖(↑(((couplingAt j N per)^(d+1))⁻¹):ℂ)‖*scale)+
      WilsonEmittedLongInvoice.budget (G:=G) w c ν (budgetAt j) s.val cut (couplingAt j N per) p pieces depth K b (fun a=>σ a/4)
    have zmax:max 0 Z≤δ*(couplingAt j N per)^(q+2)*mass:=max_le (by positivity) short
    have se:(Ψ i).p.supportExponent ≤100:=by rw [native.truep.point];exact strength i
    have actual:=active N per probe below report (Ψ i) point se (max 0 Z) mass
      (le_max_left ..) mass0.le zmax
    have fact:0≤factor R.family.params (R.family.localSection d) B.supportExponent ((levels).params i).columns:=by
      unfold Push.Local.factor
      exact mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (atomPrice_ge_one _ _
        (zero_le_one.trans ((levels).params i).columns_ge)))
    have bill:= (mul_le_mul_of_nonneg_left (le_max_right 0 Z) fact).trans actual
    simpa only [i,B,pt₁,g₁,Z] using bill

end YM.Integration.WilsonMeasuredAllFieldCensusReturn
end
