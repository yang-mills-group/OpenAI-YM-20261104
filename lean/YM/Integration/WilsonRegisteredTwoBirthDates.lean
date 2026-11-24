import YM.Integration.WilsonRegisteredTwoBirthAllCutoffs

/-! The registered point sources installed on consecutive dates on one original election.
Their complete cover inputs have one polynomial allowance for all later dates and tops. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRegisteredTwoBirthDates
open Function Filter Finset Set Lattice RG RG.Supply Wilson Source Labels Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Blue FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction
open FundedNeutralCostRun IndependentSourcePathFamily
open scoped BigOperators Classical Topology
variable {G : Gauge} {v : ℕ}

abbrev dims (grades weights : Fin v → ℕ) := fun z => (QlocalNativeTests.orbit (grades z) (weights z)).D

/-- The rows are the deposited full old Gears and the fresh registered point source.
Each site and test derivative is named on its own original lattice. -/
def represents (R : Run G) {deck : MS.Local.Physical.Deck G} (P : MS.Land.Prescription deck)
    (grades weights : Fin v → ℕ) (labs : Fin v → MS.Rake.Label deck) (μ : ℝ)
    (normal : Fin v → ℂ) (quad : Fin v → Bool) {e i : ℕ} {Q : Realm G (e+1) Credit.leanC}
    {head : Q.anchor ≤ i} (transport k oldOrders freshOrders : Fin v → ℕ) (N : ℕ)
    (old : Finset (Fin v)) (cells : (Fin v → Cover) → Fin v → Site (loose Q.draws i).L)
    {A : ℝ} (T : Input Q head univ k (dims grades weights) A) : Prop :=
  T.offsets = cells ∧ ∀ per (oldSites : Fin v → Site (R.family.side (i+2) per))
    (freshSites : Fin v → Site (R.family.side (i+1) per)),
    let X := FundedOriginalMarkedInput.chosen P
      (FundedPointMarkedSeed.datum R grades weights per (i+2) oldSites)
      labs (μ - R.family.S.scale (i+2)) oldOrders normal quad
    let Y := FundedOriginalMarkedInput.chosen P
      (FundedPointMarkedSeed.datum R grades weights per (i+1) freshSites)
      labs (μ - R.family.S.scale (i+1)) freshOrders normal quad
    (∀ y S, S ⊆ old → T.familyAt y S = Gears Q.draws Q.paid transport k N (i+2) (i+1)
      (independent X) (chartIn (loose Q.draws i) y (cells y)) S) ∧
    (∀ y z, z ∉ old → T.familyAt y {z} =
      single Y z (chartIn (loose Q.draws i) y (cells y) z))

theorem original (R : Run G) (simple : G.Simple) {deck : MS.Local.Physical.Deck G}
    (P : MS.Land.Prescription deck) (grades weights : Fin v → ℕ) (labs : Fin v → MS.Rake.Label deck)
    (μ : ℝ) (normal : Fin v → ℂ) (quad : Fin v → Bool) (transport k : Fin v → ℕ) (e budget : ℕ) :
    let L := R.family.path.levels
    let D := dims grades weights
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ᶠ m in atTop,
      ∀ (Q : Realm G (e+1) Credit.leanC) (anchor : Q.anchor ≤ m), Q.draws = L → Q.y = zz L →
      Cloze D k Q Credit.leanC → (∀ i (hi : m ≤ i), (Q.mint i (anchor.trans hi)).σ ≤ 1) →
      ∃ A : ℕ → ℝ, (∀ i, m ≤ i → 0 ≤ A i ∧ A i ≤ C*(L.clock.hatBeta i)^d) ∧
        ∀ i (age : m ≤ i) N, i+2 ≤ N → ∀ (x y : Fin v → ℕ), (∀ z, x z ≤ budget) →
        (∀ z, y z ≤ budget) → ∀ (old : Finset (Fin v))
          (cells : (Fin v → Cover) → Fin v → Site (loose Q.draws i).L),
          ∃ T : Input Q (anchor.trans age) univ k D (A i),
            represents R P grades weights labs μ normal quad transport k x y N old cells T := by
  intro L D
  obtain ⟨C,hC,d,points⟩ :=
    FundedPointSourceClock.window R P grades weights labs μ k e normal quad simple 1 budget
  obtain ⟨V,t,hV,carry⟩ := WilsonAdjacentWindingIncome.original (D:=D) (k:=k) R simple transport e
  obtain ⟨b₀,clock₀⟩ := eventually_atTop.1 points
  obtain ⟨b₁,clock₁⟩ := eventually_atTop.1 carry
  refine ⟨V*C,t+d,mul_pos hV hC,?_⟩
  filter_upwards [eventually_ge_atTop b₀,eventually_ge_atTop b₁] with m late₀ late₁ Q anchor same band cloze unit
  let b := fun i => C*(L.clock.hatBeta i)^d
  have pos (i : ℕ) : 0 ≤ b i := mul_nonneg hC.le (pow_nonneg (WardBin.hot L i).le _)
  let A := fun i => WilsonTwoBirthCoverIncome.amount (m:=i) (D:=D) (k:=k) Q transport (b i)
  refine ⟨A,?_,?_⟩
  · intro i age
    have h := anchor.trans age
    have pr := clock₁ i (late₁.trans age) Q h same band (b i) (pos _)
    exact ⟨add_nonneg (FundedInheritedMarkedInput.charge (D:=D) (k:=k) Q h (Nat.le_succ (i+1))
      transport (b i) (pos _)) (pos _),pr.trans_eq (by dsimp only [b]; rw [pow_add]; ring)⟩
  · intro i age N top x y hX hY old cells
    let X := FundedPointMarkedSeed.source R P grades weights labs (μ - R.family.S.scale (i+2)) x normal quad
    let Y := FundedPointMarkedSeed.source R P grades weights labs (μ - R.family.S.scale (i+1)) y normal quad
    have source := clock₀ i (late₀.trans age)
    have payX : bill X k e 4 ≤ b i := by
      have p := source 1 le_rfl 0 (i+2) (fun _ => 0) x hX
      rw [FundedPointMarkedSeed.same] at p
      exact p
    have payY : bill Y k e 4 ≤ b i := by
      have p := source 0 (by omega) 0 (i+1) (fun _ => 0) y hY
      rw [FundedPointMarkedSeed.same] at p
      exact p
    obtain ⟨T,off,stored,fresh⟩ := (WilsonTwoBirthCoverIncome.original Q (anchor.trans age) cloze
      transport _ (pos i) (unit _ (by omega)) (unit _ (by omega)) X Y
      (fun z _ => Nat.le_add_left _ (k z)) (fun z _ => Nat.le_add_left _ (k z)) payX payY).2
      N top old cells
    refine ⟨T,off,?_⟩
    intro per oldSites freshSites
    dsimp only
    rw [FundedPointMarkedSeed.same, FundedPointMarkedSeed.same]
    exact ⟨stored,fresh⟩

end YM.Integration.WilsonRegisteredTwoBirthDates
end

