import YM.Integration.WilsonLimitConstruction.FundedRunPacketSale
import YM.Integration.WilsonLimitConstruction.FundedPacketWidthPrices
import YM.Integration.ActualRequestNumericSchedule

/-! The independently issued rooted measures on the one funded original
Run buy both real adjacent widths, at every regulated and bare coupling
between the declared endpoints, before all placements and measurements. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonLimitConstruction.FundedRunPacketWidths
open Function Filter Finset Set MeasureTheory Lattice RG RG.Supply Wilson Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FundedNeutralCostRun
open scoped Topology BigOperators Classical

variable {G : Gauge}

def ceilings (prior : FundedPacketWidthPrices.Ceilings G) (E K S : ℕ→ℕ) : FundedPacketWidthPrices.Ceilings G :=
  fun s q C j => FundedPresoldPacketWidths.profile G s.kernel (E j) (K j) (S j) (prior s q C j)

variable {I : Inventory G} {D : FundedPacketWidthPrices.Diagrams G}
    {prior : FundedPacketWidthPrices.Ceilings G} {E K S : ℕ→ℕ} {R : Run G}
    (p : Purchase (FundedPacketWidthPrices.augment I D (ceilings prior E K S)) R) (j : ℕ)
    {v : ℕ} (Γ : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit)

local notation "A₀" => FundedPacketWidthPrices.layout p j
local notation "L₀" => R.family.path.levels
local notation "D₀" => NativeMarkedAddressTokens.axes O

theorem apertures (m : ℕ) (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (five : 5≤(L₀).clock.J (m+1)) (stamp : (Q.mint m hm).σ=crestM (L₀) m five) :
    (A₀).input.pair R.family m/2≤VestS (S j) (K j) Q m hm ∧
    (A₀).target R.family m≤VestS (S j) (K j) Q m hm := by
  let low := prior p.sheet p.quote p.choice j
  let h := ceilings prior E K S p.sheet p.quote p.choice j
  have same : (L₀).clock.kernel=p.sheet.kernel := R.alloy.B.valid.kernel.trans (by
    simpa only [PhysicalNext.ThroughLaunch.raise] using congrArg (fun s : Sheet G=>s.kernel) p.original_sheet)
  have trueWidth : h.width ((L₀).clock.J m)≤VestS (S j) (K j) Q m hm := by
    simpa only [h,ceilings,same,low] using FundedPresoldPacketWidths.live R (K j) (S j) low m Q hm five stamp
  have before := FundedPacketWidthChain.before (D p.sheet p.quote p.choice) (ceilings prior E K S p.sheet p.quote p.choice)
    j ((L₀).clock.J m)
  have after := FundedPacketWidthChain.target (D p.sheet p.quote p.choice) (ceilings prior E K S p.sheet p.quote p.choice)
    j R.family m
  have pair : (A₀).input.pair R.family m≤(A₀).input.width ((L₀).clock.J m) := min_le_right _ _
  have half : (A₀).input.pair R.family m/2≤(A₀).input.pair R.family m := by
    linarith only [(A₀).input.pair_positive R.family m]
  exact ⟨half.trans (pair.trans (before.trans trueWidth)),after.trans trueWidth⟩

def PaidInput (J : Request (Fin v)) (m : ℕ) (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (N : ℕ) (a : ℝ) (X : Input Q hm univ k (D₀) a) : Prop :=
    ∃ M : RootedMeasures Γ k O (e:=E j) (G:=G),rootedSale Γ k O Q hm X (N:=N) M ∧
      ∀ (A : NumericSchedule R.family J) (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d),
      d.level=m → ∀ g room (hg : 0<g) (hr : 0<room),
      let out := FundedRunPacketSale.funded Γ k O R m (e:=E j) F a g room hg hr
      ∀ (n : Side) (roots : Fin v→Site n) (Y : Fin v→Dip), (∀i,(Y i).Fits (O i).field) →
        let packets := OriginalFundedMarkedPackets.packets Γ k roots O Y Q hm X (N:=N) (sampled Γ k roots O M)
        ∀ z,g≤z → z≤1 → ∀ ω, ω=(A₀).input.pair R.family m/2 ∨ ω=(A₀).target R.family m →
          packets.Paid (A.outputNorm m) (fun i=>{roots i}) (OriginalMeasuredSourceRows.region O Y (fun i=>{roots i}))
            (fun i=>out.outputRadii i/F.kernelCosts i) z ω room (OriginalFundedMarkedPackets.offset k (e:=E j)) 1

def Proceeds (J : Request (Fin v)) (m : ℕ) (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m) : Prop :=
  ∀ N,m<N → ∀ a (X : Input Q hm univ k (D₀) a),0≤a → PaidInput p j Γ k O J m Q hm N a X

def Stage (J : Request (Fin v)) (m : ℕ) : Prop :=
  ∃ (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m),
    Q.draws=(L₀) ∧ Q.paid=R.metals.O ∧ Q.anchor=m ∧ Q.y=zz (L₀) ∧
    Cloze (D₀) k Q Credit.leanC ∧ Insure v (mass k univ) Q Credit.leanC ∧
    (∀ l,m≤l → ∀ hl : Q.anchor≤l, ∃ five : 5≤(L₀).clock.J (l+1), (Q.mint l hl).σ=crestM (L₀) l five) ∧
    Proceeds p j Γ k O J m Q hm

theorem onRealm (J : Request (Fin v)) (m : ℕ) (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (sale : Insure v (mass k univ) Q Credit.leanC)
    (original : OriginalRunMarkedPacketPurchase.proceeds Γ k O R Q hm)
    (five : 5≤(L₀).clock.J (m+1)) (stamp : (Q.mint m hm).σ=crestM (L₀) m five)
    (count : S j=v) (degree : K j=mass k univ)
    (cover : ∀ A : NumericSchedule R.family J,
      (A.outputNorm m).supportExponent/((A.outputNorm m).B:ℝ)≤((A₀).input.pair R.family m/2)/4 ∧
      (A.outputNorm m).supportExponent/((A.outputNorm m).B:ℝ)≤(A₀).target R.family m/4) :
    Proceeds p j Γ k O J m Q hm := by
  obtain ⟨cash,sources⟩ := original
  have widths := apertures p j m Q hm five stamp
  rw [count,degree] at widths
  intro N hn a X ha
  obtain ⟨M,law,observed,_⟩ := sources N hn a X ha
  refine ⟨M,law,?_⟩
  intro A d F hlevel g room hg hr out n roots Y fits packets z hz hz1 ω member
  have positive (i) : 0<out.outputRadii i/F.kernelCosts i := div_pos (out.output_radius_positive i) (F.kernel_positive i)
  have bounds : 0<ω ∧ ω≤width k Q hm ∧ (A.outputNorm m).supportExponent/((A.outputNorm m).B:ℝ)≤ω/4 := by
    rcases member with rfl|rfl
    · exact ⟨div_pos ((A₀).input.pair_positive R.family m) (by norm_num),by simpa [width] using widths.1,(cover A).1⟩
    · exact ⟨lt_min ((A₀).output.pair_positive R.family (m-1)) zero_lt_one,by simpa [width] using widths.2,(cover A).2⟩
  have raw := observed n roots Y fits (A.outputNorm m) (fun i=>out.outputRadii i/F.kernelCosts i) z ω positive
    bounds.1 bounds.2.1 bounds.2.2
  have bill := FundedRunPacketSale.upper Γ k O R m F a g room hg hr Q hm ha sale cash hz hz1
  exact {raw with roots:=fun i=>⟨(raw.roots i).1,(raw.roots i).2.1,(raw.roots i).2.2.trans bill⟩}

theorem selected (J : Request (Fin v)) (hG : G.Simple) (income : ℕ→Gear G→ℝ)
    (donor : FundedMarkedCoverRows.prices income R.kit) (hgrade : ∀i,k i<(D₀) i)
    (count : S j=v) (degree : K j=mass k univ) :
    ∀ᶠ m : ℕ in atTop, Stage p j Γ k O J m := by
  filter_upwards [OriginalRunMarkedPacketPurchase.selected Γ k O R (e:=E j) hG income donor hgrade,
    FundedPacketWidthPrices.supported p hG J j] with m issued cover
  obtain ⟨Q,hm,levels,ratio,anchor,clock,cl,ticket,crest,cash,sources⟩ := issued
  have sale : Insure v (mass k univ) Q Credit.leanC := by simpa using ticket
  obtain ⟨five,stamp⟩ := crest m le_rfl hm
  exact ⟨Q,hm,levels,ratio,anchor,clock,cl,sale,crest,
    onRealm p j Γ k O J m Q hm sale ⟨cash,sources⟩ five stamp count degree cover⟩

theorem actual_width (hG : G.Simple) (reader : RG05Preconstruction.ReadoutPurchase R.b)
    {V : Type} [DecidableEq V] [Fintype V] (J : Request V) (cap : ℕ→ℝ)
    (hcap : ∀m,0≤cap m) (hcap0 : Tendsto cap atTop (𝓝 0)) (m : ℕ) :
    (ActualRequestNumericSchedule.selected R hG reader (A₀).input (FundedPacketWidthPrices.input_payment p j)
      J cap hcap hcap0).outputWidth m=(A₀).input.pair R.family m/2 := rfl

theorem acquired (hG : G.Simple) {ε : ℝ} (hε : 0<ε) (I : Inventory G)
    (D : FundedPacketWidthPrices.Diagrams G) (prior : FundedPacketWidthPrices.Ceilings G) (E K S : ℕ→ℕ)
    (income : ℕ→Gear G→ℝ) (other : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@other)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      FundedMarkedCoverRows.prices income R.kit ∧ other R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} hG ε W ∧ Nonempty (Purchase I R) ∧
      Nonempty (Purchase (FundedPacketWidthPrices.augment I D (ceilings prior E K S)) R) := by
  let together : FundedCompanySelection.Prediction G := @FundedPredictionSupply.Both G
    (@FundedMarkedCoverRows.prices G income) (@other)
  have ready : FundedPredictionSupply.AllPrices (@together) := fun s q =>
    FundedPredictionSupply.both (FundedMarkedCoverRows.purchase income s q) (paid s q)
  obtain ⟨R,T,W,⟨own,rest⟩,fva,native,old,selected⟩ :=
    FundedPacketWidthPrices.purchase.{u} hG hε I D (ceilings prior E K S) (@together) ready
  exact ⟨R,T,W,own,rest,fva,native,old,selected⟩

end YM.Integration.WilsonLimitConstruction.FundedRunPacketWidths
end
