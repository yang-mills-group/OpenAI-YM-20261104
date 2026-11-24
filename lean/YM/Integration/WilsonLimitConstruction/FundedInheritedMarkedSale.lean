import YM.Integration.WilsonLimitConstruction.FundedRunPacketWidths
import YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedInput
import YM.Integration.WilsonLimitConstruction.FundedMarkedIntervalClock
import YM.Integration.OriginalFrozenSourceInvoice

/-! The previously selected original packet realm issues every actually
inherited correlated source from the frozen ultraviolet field and every
finite intervening native log, including coincident marks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedSale
open Filter Function Lattice RG RG.Supply Precision Wilson Marker
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open FundedMarkedPathSelection IndependentSourcePathFamily Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FundedNeutralCostRun
open scoped Topology BigOperators Classical

variable {G : Gauge} {I : Inventory G} {D : FundedPacketWidthPrices.Diagrams G}
    {prior : FundedPacketWidthPrices.Ceilings G} {E K S : ℕ→ℕ} {R : Run G}
    (p : Purchase (FundedPacketWidthPrices.augment I D (FundedRunPacketWidths.ceilings prior E K S)) R)
    (j : ℕ) {v : ℕ} (Γ : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit)
    (J : Request (Fin v)) {m b N : ℕ} (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (ready : FundedRunPacketWidths.Proceeds p j Γ k O J m Q hm)
    (hi : m+1≤b) (last : b≤N) (closed : Cloze (NativeMarkedAddressTokens.axes O) k Q Credit.leanC)
    (move : Fin v→ℕ) {Rows : Fin v→Type} [∀v,Fintype (Rows v)]
    (seeds : ∀v,Rows v→Seed G ((NativeMarkedAddressTokens.axes O) v))
    (legal : ∀v s,(seeds v s).rank≤k v+(seeds v s).head)
    (cells : (Fin v → Cover)→Fin v→Site (loose Q.draws m).L)

local notation "D₀" => NativeMarkedAddressTokens.axes O
local notation "hb" => Nat.le_trans (Nat.le_trans hm (Nat.le_succ m)) hi
local notation "A₀" => FundedInheritedMarkedInput.base (k:=k) Q seeds (hb)
local notation "T₀" => tollStep G (D₀) k move (E j) Credit.leanC Credit.leanC
local notation "U₀" => FundedInheritedMarkedInput.actual Q hm hi last closed move seeds legal Finset.univ cells

include ready in
theorem full :
    FundedRunPacketWidths.PaidInput p j Γ k O J m Q hm N
      (FundedInheritedMarkedInput.fee (D:=D₀) (k:=k) Q move (m+1) b (A₀)) (U₀) := by
  exact ready N (by omega) _ _ (FundedInheritedMarkedInput.charge (D:=D₀) (k:=k) Q hm hi move _
    (FundedInheritedMarkedInput.first (k:=k) Q seeds (hb) legal).1)

def quoted {z : ℝ} (span : PadRank Q (m+1) b z) :
    Input Q hm Finset.univ k (D₀) ((T₀).buy z^(b-(m+1))*(A₀)) :=
  let seed := FundedInheritedMarkedInput.first (k:=k) Q seeds (hb) legal
  FundedInheritedMarkedInput.inputAt Q hm hi last closed move z span (independent seeds)
    (OriginalCoverReanchoring.deposited seeds legal).1 seed.1 seed.2 Finset.univ cells

include ready in
theorem atQuote {z : ℝ} (span : PadRank Q (m+1) b z) (one : 1≤z) :
    FundedRunPacketWidths.PaidInput p j Γ k O J m Q hm N ((T₀).buy z^(b-(m+1))*(A₀))
      (quoted j k O Q hm hi last closed move seeds legal cells span) := by
  exact ready N (by omega) _ _ (mul_nonneg (pow_nonneg (zero_le_one.trans ((T₀).purchase one)) _)
    (FundedInheritedMarkedInput.first (k:=k) Q seeds (hb) legal).1)

theorem quoted_ancestors {z : ℝ} (span : PadRank Q (m+1) b z) (y : Fin v → Cover) :
    (quoted j k O Q hm hi last closed move seeds legal cells span).familyAt y=
      Gears Q.draws Q.paid move k N b (m+1) (independent seeds) (chartIn (loose Q.draws m) y (cells y)) := rfl

theorem fixed (hG : G.Simple) (A : NumericSchedule R.family J) (h : ℕ) (transport : Fin v→ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ (Q₀ : Realm G (E j+1) Credit.leanC) (anchor : Q₀.anchor ≤ i),
      Q₀.y=zz R.family.path.levels → Cloze (D₀) k Q₀ Credit.leanC →
      FundedRunPacketWidths.Proceeds p j Γ k O J i Q₀ anchor →
      ∀ (b N : ℕ) (lo : i+1≤b), b ≤ i+1+h → ∀ _last : b≤N,
      ∀ (Rows : Fin v→Type) [∀a,Fintype (Rows a)] (seeds : ∀a,Rows a→Seed G ((D₀) a)),
      ∀ _legal : ∀a s,(seeds a s).rank≤k a+(seeds a s).head,
      ∀ cells : (Fin v → Cover)→Fin v→Site (loose Q₀.draws i).L,
        let b₀ := FundedInheritedMarkedInput.base (k:=k) Q₀ seeds ((anchor.trans (Nat.le_succ i)).trans lo)
        let toll := (tollStep G (D₀) k transport (E j) Credit.leanC Credit.leanC).buy
          (FundedMarkedIntervalClock.quote R h i)^(b-(i+1))
        toll*b₀ ≤ A.admittedCost i*b₀ ∧
        ∃ bank : Input Q₀ anchor Finset.univ k (D₀) (toll*b₀),
          (∀ y,bank.familyAt y=Gears Q₀.draws Q₀.paid transport k N b (i+1) (independent seeds)
            (chartIn (loose Q₀.draws i) y (cells y))) ∧
          FundedRunPacketWidths.PaidInput p j Γ k O J i Q₀ anchor N (toll*b₀) bank := by
  let T := tollStep G (D₀) k transport (E j) Credit.leanC Credit.leanC
  filter_upwards [FundedMarkedIntervalClock.calendar R hG h,FundedMarkedIntervalClock.earned R hG T h A]
    with i present money Q₀ anchor clock licence supplied b N lo hi last Rows fRows seeds legal cells b₀ toll
  let span := (present.2 Q₀ clock).zone (le_refl _) hi
  have paid := FundedInheritedMarkedInput.first (k:=k) Q₀ seeds ((anchor.trans (Nat.le_succ i)).trans lo) legal
  refine ⟨mul_le_mul_of_nonneg_right (money b lo hi) paid.1,
    quoted j k O Q₀ anchor lo last licence transport seeds legal cells span,?_,?_⟩
  · intro y; rfl
  · exact atQuote p j Γ k O J Q₀ anchor supplied lo last licence transport seeds legal cells span present.1

section original
variable {per t : ℕ} {ht : t≤b} {B : MS.Local.Physical.Deck G} (original : MS.Land.Prescription B)
  (datum : ActualRunQlocalNativeTuple.Datum R per b t ht (Fin v))
  (labs : Fin v→MS.Rake.Label B) (μ : ℝ) (orders : Fin v→ℕ) (normal : Fin v→ℂ) (quadrature : Fin v→Bool)
local notation "microscopic" => FundedOriginalMarkedInput.chosen original datum labs μ orders normal quadrature
local notation "orbits" => ActualRunQlocalNativeTuple.orbit datum
local notation "raw" => FundedInheritedMarkedInput.base (k:=k) Q microscopic (hb)

include last in
theorem physical_price :
    (raw)≤ActualOriginalQPackets.packetCost original datum labs μ orders N
      (OriginalFrozenSourceInvoice.weight datum labs k (E j) (4*(Q.mint b (hb)).σ) normal) (4*(Q.mint b (hb)).σ) :=
  OriginalFrozenSourceInvoice.input original datum labs μ orders k N (E j) (4*(Q.mint b (hb)).σ) normal quadrature last

theorem frozen (source : FundedRunPacketWidths.Proceeds p j Γ k orbits J m Q hm)
    (licence : Cloze (NativeMarkedAddressTokens.axes orbits) k Q Credit.leanC) :
    FundedRunPacketWidths.PaidInput p j Γ k orbits J m Q hm N
      (FundedInheritedMarkedInput.fee (D:=FundedOriginalMarkedInput.OrbitD datum) (k:=k) Q move (m+1) b (raw))
      (FundedInheritedMarkedInput.actual Q hm hi last licence move microscopic
        (fun v _=>Nat.le_add_left _ (k v)) Finset.univ cells) :=
  full p j Γ k orbits J Q hm source hi last licence move microscopic (fun v _=>Nat.le_add_left _ (k v)) cells

end original
end YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedSale
end
