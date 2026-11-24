import YM.Integration.WilsonRegisteredTwoBirthWinding

/-! One before-test election supports both actual curvature births, the inherited
quiet cash, and the entire signed second finite Wilson coefficient. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFundedRegisteredTwoBirthWinding
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

variable {G : Gauge} {v : ℕ} {R : Run G}
variable {deck : MS.Local.Physical.Deck G}

variable {I : Inventory G} {D : FundedPacketWidthPrices.Diagrams G}
    {prior : FundedPacketWidthPrices.Ceilings G} {E K S : ℕ → ℕ}
    (p : Purchase (FundedPacketWidthPrices.augment I D (FundedRunPacketWidths.ceilings prior E K S)) R)
    (j : ℕ) (Γ : Census (Fin v)) (k : Fin v → ℕ) (req : Request (Fin v))
    (derivative : Block Γ k (E j) → ℕ)
    (c q : ℕ) (P : MS.Land.Prescription deck)
    (grades weights : Fin v → ℕ) (labs : Fin v → MS.Rake.Label deck) (μ : ℝ)
    (normal : Fin v → ℂ) (quad : Fin v → Bool)

def Report {m : ℕ} (scale : Block Γ k (E j) → Gear G → ℝ) (degree : Block Γ k (E j) → ℕ)
    (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (J : Finset (Fin v)) (o : Fin v) (i r budget : ℕ) (quiet : Credit) (sourceBill : ℝ) : Prop :=
    ∀ (transport oldOrders freshOrders : Fin v → ℕ), (∀ z, oldOrders z ≤ budget) →
      (∀ z, freshOrders z ≤ budget) → ∀ (old : Finset (Fin v))
        (cells : (Fin v → Cover) → Fin v → Site (loose Q.draws m).L),
        ∃ (A : ℝ) (T : Input Q hm univ k (NativeMarkedAddressTokens.axes (orbits R grades weights)) A)
          (d : ℕ) (C B σ : ℝ), 0 ≤ A ∧ T.offsets = cells ∧ 0 ≤ C ∧ 1 ≤ B ∧ 0 < σ ∧
          ∀ per, FundedInheritedWinding.Invoice p j Γ k (orbits R grades weights) req
            scale degree derivative c q Q hm (m+2) per (by omega) A T ∧
          traces T R J o i r per σ (C * (max 1 (Q.cash quiet (m+1)))^d * B^J.card *
            rimJ (ratioHigh Q.draws Q.paid (m+2) m) i r) ∧
          ∀ (oldSites : Fin v → Site (R.family.side (m+2) per))
            (freshSites : Fin v → Site (R.family.side (m+1) per)),
          let X := FundedOriginalMarkedInput.chosen P
            (FundedPointMarkedSeed.datum R grades weights per (m+2) oldSites) labs
            (μ - R.family.S.scale (m+2)) oldOrders normal quad
          let Y := FundedOriginalMarkedInput.chosen P
            (FundedPointMarkedSeed.datum R grades weights per (m+1) freshSites) labs
            (μ - R.family.S.scale (m+1)) freshOrders normal quad
          IndependentSourcePathFamily.bill X k (E j) 4 ≤ sourceBill ∧
          IndependentSourcePathFamily.bill Y k (E j) 4 ≤ sourceBill ∧
          (∀ y S, S ⊆ old → T.familyAt y S =
            Gears Q.draws Q.paid transport k (m+2) (m+2) (m+1) (independent X)
              (chartIn (loose Q.draws m) y (cells y)) S) ∧
          (∀ y z, z ∉ old → T.familyAt y {z} = single Y z
            (chartIn (loose Q.draws m) y (cells y) z))

/-- The original common-venue sale pays the two adjacent quoted dates. The two source
bills are uniform over the cutoff torus, independently placed sites and admitted
derivative orders. The remaining mixed read retains the complete signed cofactor. -/
theorem original (menu : Gear G → ℝ) (hmenu : ∀ L, 0 < menu L) (budget : ℕ)
    (hk : ∀ z, k z < NativeMarkedAddressTokens.axes (orbits R grades weights) z)
    (hG : G.Simple) (count : S j = v) (rank : K j = mass k univ)
    (J : Finset (Fin v)) (o : Fin v) (ho : o ∈ J) (i r : ℕ) (hi : i ≤ E j) :
    ∃ (donor : ℕ → Gear G → ℝ) (scale : Block Γ k (E j) → Gear G → ℝ)
      (degree : Block Γ k (E j) → ℕ) (quiet : Credit) (C : ℝ) (d : ℕ),
      (∀ b M, 0 < scale b M) ∧ (∀ b n M, (scale b M)⁻¹ ≤ donor n M) ∧ 0 < C ∧
      FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G donor) ∧
      (FundedMarkedCoverRows.prices donor R.kit →
        RG05Preconstruction.ReadoutPurchase R.b →
        ∀ᶠ m in atTop, ∃ (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m),
          Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
          Report p j Γ k req derivative c q P grades weights labs μ normal quad scale degree Q hm
            J o i r budget quiet (C * (R.family.path.levels.clock.hatBeta m)^d)) := by
  classical
  let seed := FundedPointMarkedSeed.reference R grades weights
  let O := orbits R grades weights
  obtain ⟨cap, quiet, _, hearing⟩ := WilsonTwoBirthWindingHearing.original
    (D:=NativeMarkedAddressTokens.axes O) (k:=k) (e:=E j)
    (I:=fun z => FundedOriginalMarkedInput.Count seed labs z)
    (U:=fun z => FundedOriginalMarkedInput.Count seed labs z) (J:=J) (o:=o) (i:=i) (r:=r)
    Credit.leanC menu hmenu
  obtain ⟨cost, scale, degree, positive, covered, _, market⟩ :=
    OriginalCommonWindingMarket.presoldWithRate Γ k O hk
      (FundedMarkedWindingPayment.menu Γ k derivative)
      (fun _ (M : Gear G) => M.past) (fun _ M => M.depth)
  let donor := fun n (M : Gear G) => max (cost n M) (cap M)
  obtain ⟨C,hC,d,points⟩ :=
    FundedPointSourceClock.window R P grades weights labs μ k (E j) normal quad hG 1 budget
  refine ⟨donor,scale,degree,quiet,C,d,positive,fun b n M => (covered b n M).trans
    (le_max_left _ _),hC,FundedMarkedCoverRows.purchase donor,?_⟩
  intro financed readout
  have sales := market R hG donor financed (Filter.Eventually.of_forall fun _ _ =>
    le_max_left _ _) readout c q
  filter_upwards [sales,FundedPacketWidthPrices.supported p hG req j,points]
    with m sale width source
  obtain ⟨Q,hm,levels,ratio,_,_,cloze,tickets,crests,book,read⟩ := sale
  obtain ⟨five,stamp,_⟩ := crests m le_rfl hm
  have ready := FundedRunPacketWidths.onRealm p j Γ k O req m Q hm tickets book
    five stamp count rank width
  have issue := FundedInheritedWinding.onRealm p j Γ k O req scale degree derivative c q m Q hm
    ready read
  obtain ⟨_,_,paid⟩ := crests (m+1) (Nat.le_succ m) (hm.trans (Nat.le_succ m))
  have quietCash := (le_max_right _ _).trans paid
  refine ⟨Q,hm,levels,ratio,?_⟩
  intro transport oldOrders freshOrders oldOK freshOK old cells
  let X := FundedPointMarkedSeed.source R P grades weights labs
    (μ - R.family.S.scale (m+2)) oldOrders normal quad
  let Y := FundedPointMarkedSeed.source R P grades weights labs
    (μ - R.family.S.scale (m+1)) freshOrders normal quad
  obtain ⟨A,T,hA,offsets,previous,fresh,t,L,B,σ,hL,hB,hσ,heard⟩ :=
    hearing Q m hm quietCash cloze transport X Y (fun z _ => Nat.le_add_left _ (k z))
      (fun z _ => Nat.le_add_left _ (k z)) (fun _ => 1) (fun _ => zero_lt_one) old cells ho hi
  refine ⟨A,T,t,L,B,σ,hA,offsets,hL,hB,hσ,?_⟩
  intro per
  refine ⟨issue (m+2) per (by omega) A T hA, heard (R.family.side m per), ?_⟩
  intro oldSites freshSites
  dsimp only
  refine ⟨source 1 le_rfl per (m+2) oldSites oldOrders oldOK,
    source 0 (by omega) per (m+1) freshSites freshOrders freshOK,?_⟩
  rw [FundedPointMarkedSeed.same, FundedPointMarkedSeed.same]
  exact ⟨previous, fresh⟩

end YM.Integration.WilsonFundedRegisteredTwoBirthWinding
end
