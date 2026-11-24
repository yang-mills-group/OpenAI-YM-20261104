import YM.Integration.WilsonOriginalMixedFiniteMaterial
import YM.Integration.WilsonMixedPassportVote
import YM.Integration.WilsonOriginalProjectedCurvatureMovingArmada

/-! Before the two regulators, fund the genuine fresh Q face and return the full old/fresh voter and finite material. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMixedFiniteVoter
open Function Filter Finset Lattice Wilson RG Tree Source Labels Marker Multi Exterior QuadraticLocal QuadraticLocal.Earn
open Push Push.PriceCompiler PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvaturePassport
open WilsonOriginalProjectedCurvatureEnvelope AllOrder AllOrder.Floe AllOrder.Floe.Step ConnectedActivityE6
open Comparison.RG02 WilsonMixedPassportVote

open Finset Lattice Wilson RG Tree Source Labels Marker Multi Exterior
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureSalary WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open QuadraticLocal.Earn AllOrder.Floe Comparison.RG02 WilsonMixedFaceLog
open private staff from YM.Integration.WilsonOriginalClubSourcePackets

open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {B : MS.Local.Physical.Deck G} {V : Type} [DecidableEq V] [Fintype V]
  (request : Request V) (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B) (μ : ℝ)
  (extra : V → ℕ) (free : V → ℝ)
  {ψ : ℕ → ℕ} (root : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
local notation "age" => R.alloy.B.a.clock.J
local notation "β̂" => R.alloy.B.a.clock.hatBeta
local notation "tollQ" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u

section date
variable {i N per vac : ℕ} (D : ActualRunQlocalNativeTuple.Datum R per (i+1) (i+1) (le_refl _) V)
  (orders : V → ℕ) (η σ Ω : ℝ) (wQ : V → ℝ) (live : i < N)


local notation "Y" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
local notation "costQ" => Ω⁻¹
local notation "step" => step_paid R.alloy.B.a i
local notation "gradeQ" => (fun _ : V => tollQ)
local notation "Qrank" => ActualOriginalQLayout.rankCap R u

/-- The two independently placed faces submit one second voter. Its finite read is on the original forest and tag. -/
def Issued (ready : Burn.horizon vac+2 ≤ age i) : Prop :=
  ∀ {ι α γ : Type} {P : Passport (R.family.side (i+1) per) V}
    (M : ι → Row P (Stock.census V) G α) (old fresh : Finset V) (sep : Disjoint old fresh)
    (leftTest : γ → α) (rightTest : γ → tastes D)
    {w₀ : V → ℝ} {t₀ : V → ℕ} {c₀ : ℝ} {o₀ d₀ e₀ : ℕ}
    (_ : Scene.Armada M w₀ t₀ σ c₀ o₀ d₀ e₀) (school : Syl.School vac)
    (_ : o₀ ≤ school.order) (_ : Qrank ≤ school.order) (_ : Fintype.card V ≤ school.pieces)
    (_ : gradeTotal old t₀ gradeQ ≤ school.horizon) (_ : c₀ ≤ costQ),
    let S := WilsonMixedFaceLog.routed M Y old fresh sep leftTest rightTest
    let w := Stoop.radius (choice old w₀ wQ) 2
    let grades := choice old t₀ gradeQ
    let cost := (2:ℝ)⁻¹ * (c₀ + costQ)
    let op := school.room step ready
    Scene.Armada S w grades σ cost school.order school.pieces school.horizon ∧
    cost ≤ costQ ∧ Mentor.Cruise.Voter S σ school.order op.count op.stage vac (age i) ∧
    ∀ (x : γ) (L : Layout G) (T : Finset Age), Legal T L → ∀ (_ : BudgetPoint)
      (F : Forest (R.family.path.levels.clock.op i per).ratio) (tag : (R.family.path.levels.clock.op i per).Choices)
      (b : fieldDir G (R.family.side i per) 1) (r : ℕ),
      let joint := Air.craft S (fun a => (S a).paint x) grades L T
      let oldBank := Air.craft M (fun a => (M a).paint (leftTest x)) t₀ L T
      let test := testInclusion (ActualRunQlocalNativeTuple.orbit D) (rightTest x)
      let newBank := NativePaidPacketColors.colors (ActualOriginalQPackets.packets Q D u η orders N) oldBank.vac test
      let pred := WilsonOriginalMixedFiniteMaterial.bank old fresh oldBank newBank
      let K := (RunFormalChain.fromRun R).step N i per live
      joint.Standard ∧ pred.Standard ∧
      (∀ g, g ≠ 0 → ∀ U, Integral.markedLog g U joint = Integral.markedLog g U pred) ∧
      Bulk.Fk K F tag joint b r = Bulk.Fk K F tag pred b r ∧
      PhysicalWilsonPeriodizedMaterial.reference R N i per live b joint r =
        PhysicalWilsonPeriodizedMaterial.reference R N i per live b pred r

end date

include income

/-- The constants and threshold precede the cutoff, the period, every individual fresh position and every old roster. -/
theorem original (simple : G.Simple) (K q : ℕ) (positive : ∀ v, 0 < free v) {ε : ℝ} (allow : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ b : ℕ, ∀ᶠ i : ℕ in atTop,
    ∀ vac : ℕ, ∀ ready : Burn.horizon vac+2 ≤ age i, ∀ Ω : ℝ, 1 ≤ Ω →
      Ω ≤ (β̂ (i+1))^(Beaming.grain (age i)) →
      ∀ (N per : ℕ) (sites : V → Site (R.family.side (i+1) per)) (orders : V → ℕ),
      (∀ v, orders v ≤ K) → ∀ live : i < N,
      let D := ActualOriginalQPointSetup.pointDatum R request per (i+1) sites
      let σ := Poetry.Agenda.seed root ψ (Burn.horizon vac) (age (i+1))
      let η := (μ+R.family.S.scale N-R.family.S.scale (i+1))-R.family.S.scale N
      let a := C * (β̂ (i+1))^(b+1)
      let wQ := fun v => free v/(a*Ω)
      let g := Coat.gStep (R.family.path.rep N per (i+1)).beta
      Issued R Q u extra D orders η σ Ω wQ live ready ∧
      ∀ s : (Stock.census V).Mode,
        Poly.toll wQ s * (a*Ω)^s.val.card = Poly.toll free s ∧ (a*Ω)^s.val.card *
          g^(q+2*((b+1)*Fintype.card V)+1) ≤ ε*g^q := by
  obtain ⟨C, one, b, schedule⟩ :=
    WilsonOriginalProjectedCurvatureMovingArmada.original R simple request Q u μ extra free root income K q positive allow
  refine ⟨C, one, b, ?_⟩
  filter_upwards [schedule] with i earned
  intro vac ready Ω low cap N per sites orders degrees live
  have enter : Burn.horizon vac ≤ age (i+1) :=
    (show Burn.horizon vac ≤ age i by omega).trans (R.alloy.B.a.fits.mono (Nat.le_succ i))
  have item := earned (Burn.horizon vac) enter Ω low cap N per sites orders degrees live
  refine ⟨?_, item.2⟩
  let D := ActualOriginalQPointSetup.pointDatum R request per (i+1) sites
  let σ := Poetry.Agenda.seed root ψ (Burn.horizon vac) (age (i+1))
  let η := (μ+R.family.S.scale N-R.family.S.scale (i+1))-R.family.S.scale N
  let Y := WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
  have good : 0 < σ := Poetry.Agenda.stem ..
  unfold Issued
  intro ι α γ P M old fresh sep leftTest rightTest w₀ t₀ c₀ o₀ d₀ e₀ hM school ord freshOrd seats mass rent
  have both := WilsonMixedPassportVote.original M Y old fresh sep leftTest rightTest school
    (step_paid R.alloy.B.a i) ready hM item.1 ord freshOrd seats mass rent (le_refl _)
  refine ⟨both.1, both.2.1, both.2.2, ?_⟩
  intro x L T legal point F tag b r
  exact WilsonOriginalMixedFiniteMaterial.original Q D u η orders N σ extra L T M old fresh sep leftTest rightTest x
    t₀ (choice old t₀ (fun _ => tollQ)) hM good both.1 good live legal point F tag b r

end YM.Integration.WilsonOriginalMixedFiniteVoter
