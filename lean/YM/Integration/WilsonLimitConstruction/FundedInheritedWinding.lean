import YM.Integration.WilsonLimitConstruction.FundedMarkedWindingPayment
import YM.Integration.WilsonLimitConstruction.FundedInheritedMarkedSale
import YM.Integration.ActualRunKernelPackets

/-! One original realm pays for the independently placed compound marked
input, both adjacent packet widths and every nonzero finite-to-cover winding
row at the same positive physical radii. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonLimitConstruction.FundedInheritedWinding
open IndependentSourcePathFamily
open Function Filter Finset Set Lattice RG RG.Supply Wilson Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FundedNeutralCostRun
open scoped Topology BigOperators Classical
variable {G : Gauge} {I : Inventory G} {D : FundedPacketWidthPrices.Diagrams G}
    {prior : FundedPacketWidthPrices.Ceilings G} {E K S : ℕ→ℕ} {R : Run G}
    (p : Purchase (FundedPacketWidthPrices.augment I D (FundedRunPacketWidths.ceilings prior E K S)) R)
    (j : ℕ) {v : ℕ} (Γ : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit) (J : Request (Fin v))
variable (scale : (Block Γ k (E j))→Gear G→ℝ) (degree derivative : (Block Γ k (E j))→ℕ) (c q : ℕ)

def Invoice {m : ℕ} (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (N per : ℕ) (hN : m<N) (amount : ℝ) (X : Input Q hm Finset.univ k ((NativeMarkedAddressTokens.axes O)) amount) : Prop :=
  let g := Pert.Asymptotics.regulatorRun R.family N per (m+1)
  let hg := ActualRunKernelPackets.regulator_pos R N per (m+1) hN
  FundedRunPacketWidths.PaidInput p j Γ k O J m Q hm N amount X ∧
  ∃ bill : (Block Γ k (E j))→ℝ,
    (∀b,FundedMarkedWindingPayment.RowInvoice Γ k O (R:=R) X N per c q scale degree derivative b (bill b)) ∧
    ∀ (A : NumericSchedule R.family J) (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d),
    ∀ room (hr : 0<room),
      let F₀ := FundedRunPacketSale.funded Γ k O R m (e:=E j) F amount g room hg hr
      let w := fun a=>F₀.outputRadii a/F.kernelCosts a
      ∀ z : ℝ,g≤z → z≤1 →
        ∑b,Poly.toll w b.1.val*‖(z:ℂ)^(power Γ k (E j) b)‖*(bill b*g^(-(c:ℝ)))≤g^q*room

def Stage (m : ℕ) : Prop :=
  ∃ (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m),
    Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧
    Cloze ((NativeMarkedAddressTokens.axes O)) k Q Credit.leanC ∧ Insure v (mass k Finset.univ) Q Credit.leanC ∧
    (∀ N per,m<N → Pert.Asymptotics.regulatorRun R.family N per (m+1)≤1) ∧
    (∀ l,m≤l → ∀ a : Q.anchor≤l,∃ five : 5≤R.family.path.levels.clock.J (l+1), (Q.mint l a).σ=crestM R.family.path.levels l five) ∧
    FundedRunPacketWidths.Proceeds p j Γ k O J m Q hm ∧
    ∀ (N per : ℕ) (hN : m<N) (amount : ℝ) (X : Input Q hm Finset.univ k ((NativeMarkedAddressTokens.axes O)) amount),
      0≤amount → Invoice p j Γ k O J scale degree derivative c q Q hm N per hN amount X

theorem onRealm (m : ℕ) (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (ready : FundedRunPacketWidths.Proceeds p j Γ k O J m Q hm)
    (market : ∀ b,OriginalCommonWindingMarket.Receipt R ((NativeMarkedAddressTokens.axes O)) k c q (degree b) ((fun (_ : Block Γ k (E j)) (gear : Gear G) => gear.past) b) (scale b)
      m Q hm (FundedMarkedWindingPayment.menu Γ k derivative b))
    (N per : ℕ) (hN : m<N) (amount : ℝ) (X : Input Q hm Finset.univ k ((NativeMarkedAddressTokens.axes O)) amount) (ha : 0≤amount) :
    Invoice p j Γ k O J scale degree derivative c q Q hm N per hN amount X := by
  classical
  choose bill fields using fun b=>FundedMarkedWindingPayment.item Γ k O X ha N per hN c q scale
    degree derivative b (market b)
  refine ⟨ready N hN amount X ha,bill,fields,?_⟩
  intro A d F room hr
  dsimp only
  intro z lo hi
  exact FundedMarkedWindingPayment.portfolio Γ k O F amount _ room ha
    (ActualRunKernelPackets.regulator_pos R N per (m+1) hN) hr q c bill (fun b=>(fields b).1) lo hi

theorem stage (hG : G.Simple) (income : ℕ→Gear G→ℝ) (count : S j=v) (rank : K j=mass k Finset.univ)
    (issued : ∀ᶠ m : ℕ in atTop,OriginalCommonWindingMarket.Sale R Γ k O
      (FundedMarkedWindingPayment.menu Γ k derivative) ((fun (_ : Block Γ k (E j)) (gear : Gear G) => gear.past)) scale degree income c q m) :
    ∀ᶠ m : ℕ in atTop,Stage p j Γ k O J scale degree derivative c q m := by
  obtain ⟨start,stop⟩ := eventually_atTop.mp (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)
  filter_upwards [issued,FundedPacketWidthPrices.supported p hG J j,eventually_ge_atTop start]
    with m sale width small
  obtain ⟨Q,hm,levels,ratio,clock,anchor,cl,tickets,crests,book,read⟩ := sale
  obtain ⟨five,stamp,_⟩ := crests m le_rfl hm
  have ready := FundedRunPacketWidths.onRealm p j Γ k O J m Q hm tickets book five stamp count rank width
  refine ⟨Q,hm,levels,ratio,clock,anchor,cl,tickets,?_,?_,ready,?_⟩
  · exact fun N per hm=>(stop (m+1) (small.trans (Nat.le_succ m)) N per hm).le
  · intro l hl a
    obtain ⟨f,σ,_⟩ := crests l hl a
    exact ⟨f,σ⟩
  · exact onRealm p j Γ k O J scale degree derivative c q m Q hm ready read

theorem inherited {m : ℕ} (book : Stage p j Γ k O J scale degree derivative c q m) :
    ∃ (Q : Realm G (E j+1) Credit.leanC) (hm : Q.anchor ≤ m)
      (included : Cloze ((NativeMarkedAddressTokens.axes O)) k Q Credit.leanC),
      Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧
      ∀ (N per b : ℕ) (lo : m+1≤b) (last : b≤N) (transport : Fin v→ℕ),
      ∀ (Rows : Fin v→Type) [∀ a,Fintype (Rows a)] (seeds : ∀a,Rows a→Seed G (((NativeMarkedAddressTokens.axes O)) a)),
      ∀ (legal : ∀a s,(seeds a s).rank≤k a+(seeds a s).head),
      ∀ cells : (Fin v → Cover)→Fin v→Site (loose Q.draws m).L,
        let amount := FundedInheritedMarkedInput.fee (D:=(NativeMarkedAddressTokens.axes O)) (k:=k) Q transport (m+1) b
          (FundedInheritedMarkedInput.base (k:=k) Q seeds ((hm.trans (Nat.le_succ m)).trans lo))
        let X := FundedInheritedMarkedInput.actual Q hm lo last included transport seeds legal Finset.univ cells
        (∀y,X.familyAt y=Gears Q.draws Q.paid transport k N b (m+1) (independent seeds)
          (chartIn (loose Q.draws m) y (cells y))) ∧
        Invoice p j Γ k O J scale degree derivative c q Q hm N per (by omega) amount X := by
  obtain ⟨Q,hm,levels,ratio,clock,_,included,_,_,_,_,ready⟩ := book
  refine ⟨Q,hm,included,levels,ratio,clock,?_⟩
  intro N per b lo last transport Rows fRows seeds legal cells amount X
  refine ⟨fun _=>rfl,ready N per (by omega) amount X ?_⟩
  exact FundedInheritedMarkedInput.charge (D:=(NativeMarkedAddressTokens.axes O)) (k:=k) Q hm lo transport _
    (FundedInheritedMarkedInput.first (k:=k) Q seeds ((hm.trans (Nat.le_succ m)).trans lo) legal).1

theorem original (hG : G.Simple) {ε : ℝ} (hε : 0<ε) (I : Inventory G)
    (D : FundedPacketWidthPrices.Diagrams G) (prior : FundedPacketWidthPrices.Ceilings G) (E K S : ℕ→ℕ)
    (j : ℕ) {v : ℕ} (Γ : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit) (J : Request (Fin v))
    (derivative : Block Γ k (E j)→ℕ) (count : S j=v) (rank : K j=mass k Finset.univ)
    (grades : ∀ a,k a<NativeMarkedAddressTokens.axes O a)
    (other : FundedCompanySelection.Prediction G) (paid : FundedPredictionSupply.AllPrices (@other)) :
    ∃ (scale : Block Γ k (E j)→Gear G→ℝ) (degree : Block Γ k (E j)→ℕ),
      (∀ b gear,0<scale b gear) ∧
      ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
        (p : Purchase (FundedPacketWidthPrices.augment I D (FundedRunPacketWidths.ceilings prior E K S)) R),
        other R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
        Nonempty (Purchase I R) ∧ ∀ c q,∀ᶠ m : ℕ in atTop,Stage p j Γ k O J scale degree derivative c q m := by
  obtain ⟨income,scale,degree,positive,_,offer⟩ := OriginalCommonWindingMarket.presold Γ k O grades
    (FundedMarkedWindingPayment.menu Γ k derivative) (fun _ gear=>gear.past) (fun _ gear=>gear.depth)
  obtain ⟨R,T,W,bank,rest,fva,native,original,⟨p⟩⟩ :=
    FundedRunPacketWidths.acquired.{u} hG hε I D prior E K S income (@other) paid
  refine ⟨scale,degree,positive,R,T,W,p,rest,fva,native,original,?_⟩
  intro c q
  exact stage p j Γ k O J scale degree derivative c q hG income count rank
    (offer R hG income bank (Eventually.of_forall (fun _ _=>le_rfl)) native.2.2.2.2.2.2.1 c q)

end YM.Integration.WilsonLimitConstruction.FundedInheritedWinding
end
