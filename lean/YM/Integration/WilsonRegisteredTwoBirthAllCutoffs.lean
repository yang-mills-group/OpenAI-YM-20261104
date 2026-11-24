import YM.Integration.WilsonAdjacentWindingIncome
import YM.Integration.WilsonRegisteredPointWindingReadout
import YM.Integration.WilsonFundedRegisteredTwoBirthWinding

/-! A cutoff-uniform funded winding price for a curvature source installed on the aged
history and a fresh curvature source at the next reporting date. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRegisteredTwoBirthAllCutoffs
open Function Filter Finset Set Lattice RG RG.Supply Wilson Source Labels Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Blue FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonRegisteredTwoBirthWinding
open WilsonLimitConstruction
open FundedNeutralCostRun IndependentSourcePathFamily
open scoped Topology BigOperators Classical



variable {G : Gauge} {v : ℕ}

def signed (R : Run G) {e m : ℕ} {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}
    (Γ : Census (Fin v)) (k : Fin v → ℕ) (O : Fin v → Orbit) {A : ℝ}
    (T : Input Q hm univ k (NativeMarkedAddressTokens.axes O) A)
    (c q N per : ℕ) (scale : Block Γ k e → Gear G → ℝ) (degree : Block Γ k e → ℕ) : Prop :=
  let n := R.family.side m per
  let g := Pert.Asymptotics.regulatorRun R.family N per (m+1)
  ∀ b : Block Γ k e,
    let S := b.1.val.val
    let o := owner Γ b.1
    let P := WilsonRegisteredPointWindingReadout.difference Q T S o N per b.2.1.val b.2.2.val R
    ∀ (x : Cover) (tests : Fence (Hooks G) S o b.2.2.val → SignedRootedWindingReadout.Tests
      (NativeMarkedAddressTokens.axes O)) (U : ℝ), 0 ≤ U →
      (∀ z, SignedRootedWindingReadout.amplitude S (tests z) ≤ U) →
      ∀ ξ : Fence (Hooks G) S o b.2.2.val → ℂ, (∀ z, ‖ξ z‖ ≤ 1) →
      let f := fun z => ξ z * SignedRootedWindingReadout.read S (tests z) (towerV S o b.2.2.val P x z)
      Summable f ∧
        ‖∑' z, f z‖ ≤ U * (ActualRunAdmissionScales.admittedCost R.family.path.levels m^(degree b) *
          (Real.exp (-(scale b (Q.mint m hm).gear/512)*(n.val:ℝ)) * A^S.card)) ∧
        ‖∑' z, f z‖ * g^(-(c:ℝ)) ≤ U * (g^q * A^S.card)

private theorem from_invoice {R : Run G} {e m : ℕ} {Q : Realm G (e+1) Credit.leanC}
    {hm : Q.anchor ≤ m} {Γ : Census (Fin v)} {k : Fin v → ℕ} {O : Fin v → Orbit} {A : ℝ}
    (T : Input Q hm univ k (NativeMarkedAddressTokens.axes O) A) {c q N per : ℕ} (cut : m < N)
    {scale : Block Γ k e → Gear G → ℝ} (hs : ∀ b M, 0 < scale b M)
    {degree derivative : Block Γ k e → ℕ} {fee : Block Γ k e → ℝ}
    (row : ∀ b, FundedMarkedWindingPayment.RowInvoice Γ k O (R:=R) T N per c q scale degree derivative
      b (fee b)) : signed R Γ k O T c q N per scale degree := by
  intro b S o P x tests U hU cap ξ phases f
  obtain ⟨small, spatial, posted⟩ := row b
  have positive := hs b (Q.mint m hm).gear
  have hg := ActualRunKernelPackets.regulator_pos R N per (m+1) cut
  obtain ⟨sums,bound⟩ := SignedRootedWindingReadout.tested S (owner_mem Γ b.1)
    (by positivity) posted x tests U hU cap ξ phases
  refine ⟨sums, bound.trans (mul_le_mul_of_nonneg_left spatial hU), ?_⟩
  exact (mul_le_mul_of_nonneg_right bound (Real.rpow_nonneg hg.le _)).trans
    ((mul_assoc _ _ _).le.trans (mul_le_mul_of_nonneg_left small hU))

/-- A common inlet rent is polynomial in the reporting schedule. It is quoted before
every ultraviolet cutoff, subset, placement and period. All finite descendants of
the genuine old source are present in the table on which the folded-input invoice is paid. -/
theorem original (E : ℕ → ℕ) (j : ℕ) (Γ : Census (Fin v)) (k transport : Fin v → ℕ)
    (req : Request (Fin v)) (derivative : Block Γ k (E j) → ℕ) (c q : ℕ)
    (grades weights : Fin v → ℕ)
    (hk : ∀ z, k z < (QlocalNativeTests.orbit (grades z) (weights z)).D) (budget : ℕ) :
    ∃ (donor : ℕ → Gear G → ℝ) (scale : Block Γ k (E j) → Gear G → ℝ)
      (degree : Block Γ k (E j) → ℕ), (∀ b M, 0 < scale b M) ∧
      (∀ b n M, (scale b M)⁻¹ ≤ donor n M) ∧
      FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G donor) ∧
      ∀ {I : Inventory G} {D : FundedPacketWidthPrices.Diagrams G}
        {prior : FundedPacketWidthPrices.Ceilings G} {K S : ℕ → ℕ}
        (R : Run G) (p : Purchase
          (FundedPacketWidthPrices.augment I D (FundedRunPacketWidths.ceilings prior E K S)) R)
        {deck : MS.Local.Physical.Deck G} (P : MS.Land.Prescription deck)
        (labs : Fin v → MS.Rake.Label deck) (μ : ℝ) (normal : Fin v → ℂ) (quad : Fin v → Bool),
      G.Simple → S j = v → K j = mass k univ → FundedMarkedCoverRows.prices donor R.kit →
      RG05Preconstruction.ReadoutPurchase R.b →
      ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∀ᶠ m in atTop,
        ∃ (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m) (A : ℝ),
          Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧ 0 ≤ A ∧
          A ≤ C*(R.family.path.levels.clock.hatBeta m)^d ∧
          ∀ N (top : m+2 ≤ N), ∀ (oldOrders freshOrders : Fin v → ℕ), (∀ z, oldOrders z ≤ budget) →
          (∀ z, freshOrders z ≤ budget) → ∀ (old : Finset (Fin v))
            (cells : (Fin v → Cover) → Fin v → Site (loose Q.draws m).L),
          ∃ T : Input Q hm univ k (NativeMarkedAddressTokens.axes (orbits R grades weights)) A,
            T.offsets = cells ∧ ∀ per,
            FundedInheritedWinding.Invoice p j Γ k (orbits R grades weights) req
              scale degree derivative c q Q hm N per (lt_of_lt_of_le (by omega) top) A T ∧
            signed R Γ k (orbits R grades weights) T c q N per scale degree ∧
            ∀ (oldSites : Fin v → Site (R.family.side (m+2) per))
              (freshSites : Fin v → Site (R.family.side (m+1) per)),
            let X := FundedOriginalMarkedInput.chosen P
              (FundedPointMarkedSeed.datum R grades weights per (m+2) oldSites) labs
              (μ - R.family.S.scale (m+2)) oldOrders normal quad
            let Y := FundedOriginalMarkedInput.chosen P
              (FundedPointMarkedSeed.datum R grades weights per (m+1) freshSites) labs
              (μ - R.family.S.scale (m+1)) freshOrders normal quad
            (∀ y S, S ⊆ old → T.familyAt y S =
              Gears Q.draws Q.paid transport k N (m+2) (m+1) (independent X)
                (chartIn (loose Q.draws m) y (cells y)) S) ∧
            (∀ y z, z ∉ old → T.familyAt y {z} =
              single Y z (chartIn (loose Q.draws m) y (cells y) z)) := by
  classical
  let O := fun z => QlocalNativeTests.orbit (grades z) (weights z)
  obtain ⟨donor,scale,degree,positive,width,purchase,market⟩ :=
    OriginalCommonWindingMarket.presoldWithRate Γ k O hk
      (FundedMarkedWindingPayment.menu Γ k derivative)
      (fun _ (M : Gear G) => M.past) (fun _ M => M.depth)
  refine ⟨donor,scale,degree,positive,width,purchase,?_⟩
  intro I D prior K S R p deck P labs μ normal quad hG count rank priced readout
  obtain ⟨C,hC,d,points⟩ :=
    FundedPointSourceClock.window R P grades weights labs μ k (E j) normal quad hG 1 budget
  obtain ⟨V,t,hV,carry⟩ := WilsonAdjacentWindingIncome.original (D:=NativeMarkedAddressTokens.axes O)
    (k:=k) R hG transport (E j)
  have sales := market R hG donor priced (Filter.Eventually.of_forall fun _ _ => le_rfl) readout c q
  refine ⟨V*C,t+d,mul_pos hV hC,?_⟩
  filter_upwards [sales,FundedPacketWidthPrices.supported p hG req j,points,carry]
    with m sale widths source transportFee
  obtain ⟨Q,hm,levels,ratio,clock,_,cloze,tickets,crests,book,read⟩ := sale
  obtain ⟨five,stamp,_⟩ := crests m le_rfl hm
  have ready := FundedRunPacketWidths.onRealm p j Γ k O req m Q hm tickets book
    five stamp count rank widths
  have issue := FundedInheritedWinding.onRealm p j Γ k O req scale degree derivative c q m Q hm ready read
  have unit (l : ℕ) (hl : m ≤ l) : (Q.mint l (hm.trans hl)).σ ≤ 1 := by
    obtain ⟨f,st,_⟩ := crests l hl (hm.trans hl)
    exact st.le.trans (WilsonCoeffUV.StableStrip.crest_le_one R.family.path.levels l f)
  let H := R.family.path.levels.clock.hatBeta m
  let b := C*H^d
  have hb : 0 ≤ b := mul_nonneg hC.le (pow_nonneg (WardBin.hot R.family.path.levels m).le _)
  let A := WilsonTwoBirthCoverIncome.amount (m:=m) (D:=NativeMarkedAddressTokens.axes O) (k:=k)
    Q transport b
  have ha : 0 ≤ A := add_nonneg (FundedInheritedMarkedInput.charge (D:=NativeMarkedAddressTokens.axes O)
    (k:=k) Q hm (Nat.le_succ (m+1)) transport b hb) hb
  have hA : A ≤ V*C*H^(t+d) := by
    have bound := transportFee Q hm levels clock b hb
    exact bound.trans_eq (by dsimp only [b]; rw [pow_add]; ring)
  refine ⟨Q,hm,A,levels,ratio,ha,hA,?_⟩
  intro N top oldOrders freshOrders oldOK freshOK old cells
  let X := FundedPointMarkedSeed.source R P grades weights labs
    (μ - R.family.S.scale (m+2)) oldOrders normal quad
  let Y := FundedPointMarkedSeed.source R P grades weights labs
    (μ - R.family.S.scale (m+1)) freshOrders normal quad
  have payX : bill X k (E j) 4 ≤ b := by
    have v := source 1 le_rfl 0 (m+2) (fun _ => 0) oldOrders oldOK
    rw [FundedPointMarkedSeed.same] at v
    exact v
  have payY : bill Y k (E j) 4 ≤ b := by
    have v := source 0 (by omega) 0 (m+1) (fun _ => 0) freshOrders freshOK
    rw [FundedPointMarkedSeed.same] at v
    exact v
  obtain ⟨T,offsets,previous,fresh⟩ :=
    (WilsonTwoBirthCoverIncome.original Q hm cloze transport b hb (unit _ (by omega))
      (unit _ (by omega)) X Y (fun z _ => Nat.le_add_left _ (k z))
        (fun z _ => Nat.le_add_left _ (k z)) payX payY).2 N top old cells
  refine ⟨T,offsets,?_⟩
  intro per
  have current := issue N per (by omega) A T ha
  obtain ⟨fee,row,_⟩ := current.2
  refine ⟨current,from_invoice T (by omega) positive row,?_⟩
  intro oldSites freshSites
  dsimp only
  rw [FundedPointMarkedSeed.same, FundedPointMarkedSeed.same]
  exact ⟨previous,fresh⟩

end YM.Integration.WilsonRegisteredTwoBirthAllCutoffs
end
