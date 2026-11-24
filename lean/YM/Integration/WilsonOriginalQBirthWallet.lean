import YM.Integration.WilsonOriginalProjectedCurvatureOnCard

/-! The original source price through the semester voter and its funded card. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalQBirthWallet
/-- The actual purchased clause at a stated source price. The witness theorem
only names that clause. Both numerical parameters remain free in the result. -/
abbrev At {P:ℝ→ℕ→Prop} (_receipt:∃ C:ℝ, 1≤C ∧ ∃ b:ℕ,P C b) (C:ℝ) (b:ℕ) : Prop := P C b
end YM.Integration.WilsonOriginalQBirthWallet

namespace YM.Integration.WilsonOriginalProjectedCurvatureMovingArmada
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal QuadraticLocal.Earn AllOrder AllOrder.Floe AllOrder.Floe.Step ConnectedActivityE6
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
  {ψ:ℕ→ℕ} (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u

include income hG
theorem atBirth (K q:ℕ) (hw:∀i,0<w i) {ε:ℝ} (εpos:0<ε) {C:ℝ} {b:ℕ} (hC:1≤C)
    (source: WilsonOriginalQBirthWallet.At (WilsonOriginalProjectedCurvatureMovingClock.purchased R hG J Q u μ extra w K hw) C b) :
    WilsonOriginalQBirthWallet.At (original R hG J Q u μ extra w root income K q hw εpos) C b := by
  unfold WilsonOriginalQBirthWallet.At at source ⊢
  have fees:=WilsonOriginalProjectedCurvatureReportingRefund.original (V:=V) R hG hC (b+1) q εpos
  have hot:=((Next.Rank.Station.hat_rate R.family.path.levels hG).comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (2:ℝ)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually source,fees,hot] with m filed sale warm
  intro k reached Ω one roof N p o orders capped live D σ η X a g
  have levy:=WilsonMovingMentorRootRadius.at_date (ψ:=ψ) R root income (m+1) k reached
  have beta:= (R.makes.wilson.represents N p (m+1) (Nat.succ_le_of_lt live)).band.1
  change β̂ (m+1)/2 ≤ (R.family.path.rep N p (m+1)).beta at beta
  change 2 ≤ β̂ (m+1) at warm
  have head:1≤(R.family.path.rep N p (m+1)).beta:=by linarith
  have sqhead:1≤Real.sqrt (R.family.path.rep N p (m+1)).beta:=by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt head
  have pos:0<Pert.Asymptotics.regulatorRun R.family N p (m+1):=inv_pos.mpr (zero_lt_one.trans_le sqhead)
  have unit:Pert.Asymptotics.regulatorRun R.family N p (m+1)≤1:=inv_le_one_of_one_le₀ sqhead
  obtain ⟨pw,paid,restore⟩:=filed σ Ω (zero_lt_one.trans_le one) levy N p (m+1) o orders capped (Nat.succ_le_of_lt live) pos unit
  have members:=WilsonOriginalProjectedCurvatureProduction.census R u
  refine ⟨⟨⟨fun s=>(members s).1,fun s=>(members s).2⟩,pw,paid,
    WilsonOriginalProjectedCurvatureLamps.issued Q D u η orders N σ extra,?_⟩,?_⟩
  · intro i
    exact (WilsonOriginalProjectedCurvatureRender.priced Q D u η orders N i.1 σ (extra i.1.1.1) i.2).1
  · intro s
    exact ⟨restore s,sale Ω one roof N p live s⟩

end YM.Integration.WilsonOriginalProjectedCurvatureMovingArmada

namespace YM.Integration.WilsonOriginalProjectedCurvatureSemesterVoter
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal QuadraticLocal.Earn AllOrder AllOrder.Floe AllOrder.Floe.Step ConnectedActivityE6
open Push.PriceCompiler
open scoped Classical BigOperators
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V]

variable (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  (J:Request V) (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
  {ψ:ℕ→ℕ} (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

include hG income
theorem atBirth (K order q:ℕ) (hw:∀i,0<w i) {ε:ℝ} (εpos:0<ε) {C:ℝ} {b:ℕ}
    (paid: WilsonOriginalQBirthWallet.At (WilsonOriginalProjectedCurvatureMovingArmada.original R hG J Q u μ extra w root income K q hw εpos) C b) :
    WilsonOriginalQBirthWallet.At (original R hG J Q u μ extra w root income K order q hw εpos) C b := by
  unfold WilsonOriginalQBirthWallet.At at paid ⊢
  filter_upwards [paid,R.alloy.B.a.fits.deep.eventually_ge_atTop (rank+v)] with m purchase large
  intro r E seats stage book Ω one roof N p o orders cap live D σ η X a g
  have height:Burn.horizon E.vac ≤ J₀ (m+1):=
    (Nat.le_trans (Nat.le_add_right ..) E.paid).trans (step_paid R.alloy.B.a m).1
  obtain ⟨file,restore⟩:=purchase (Burn.horizon E.vac) height Ω one roof N p o orders cap live
  exact ⟨admitted file (by omega) (by omega) seats stage book,file,restore⟩

end YM.Integration.WilsonOriginalProjectedCurvatureSemesterVoter

namespace YM.Integration.WilsonOriginalProjectedCurvatureOnCard
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal QuadraticLocal.Earn AllOrder AllOrder.Floe AllOrder.Floe.Step ConnectedActivityE6
open Push.PriceCompiler
open scoped Classical BigOperators
variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V]

variable (R:Run G) (hG:G.Simple) {B:MS.Local.Physical.Deck G}
  (J:Request V) (Q:MS.Land.Prescription B) (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
  {ψ:ℕ→ℕ} (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income:WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "h" => Fintype.card V
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u

include hG income
theorem atBirth (K order q:ℕ) (hw:∀i,0<w i) {ε:ℝ} (εpos:0<ε) {C:ℝ} {b:ℕ}
    (course: WilsonOriginalQBirthWallet.At (WilsonOriginalProjectedCurvatureSemesterVoter.original R hG J Q u μ extra w root income K order q hw εpos) C b) :
    WilsonOriginalQBirthWallet.At (original R hG J Q u μ extra w root income K order q hw εpos) C b := by
  unfold WilsonOriginalQBirthWallet.At at course ⊢
  let k:=order+v+h
  filter_upwards [course,R.alloy.B.a.fits.deep.eventually_ge_atTop (Burn.horizon k+2),
    R.alloy.B.a.fits.deep.eventually_ge_atTop (h+order+1)] with m ready high room
  intro card
  let r:Mentor.Opportunity (J₀ (m+1)) (J₀ m):=⟨h,order+1,step_paid R.alloy.B.a m,by omega,by omega,by omega⟩
  let E:Mentor.Epoch root R.rolls (J₀ (m+1)) (J₀ m) r:=
    ⟨k,R.alloy.B.a.clock.adm (m+1),high,⟨card⟩⟩
  have horizon:order+v ≤ Burn.horizon k+2:=by unfold Burn.horizon k; omega
  exact ready r E (le_refl _) (le_refl _) horizon

end YM.Integration.WilsonOriginalProjectedCurvatureOnCard

end
