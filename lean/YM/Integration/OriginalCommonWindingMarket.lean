import YM.Integration.OriginalRunMarkedPacketPurchase
import YM.Integration.RootedVacuumWinding

/-! A single original stage purchases the canonical output packet coefficients,
the named marked winding measurements and the signed vacuum tensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalCommonWindingMarket
open Function Filter Finset Lattice Wilson RG RG.Supply Marker
open PhysicalNext PhysicalNext.Repeat.Legato FreeResolvent WilsonLimitConstruction
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Embroider ComparisonDensity.Address LocalComparison
open scoped Classical BigOperators Topology

universe u

inductive Row (V : Type) (e : ℕ)
  | vacuum (i : Fin (e+1)) (r : ℕ)
  | marked (J : Finset V) (o : J) (i : Fin (e+1)) (r d : ℕ)

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {e : ℕ}

/-- `r` counts the further field slots after the named vacuum bond, and the
marked row uses all `r` field slots in addition to the named marked site. -/
def Receipt (R : Run G) (D k : V→ℕ) (c q a : ℕ) (w s : Gear G→ℝ)
    (m : ℕ) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) : Row V e → Prop
  | .vacuum i r => RootedVacuumWinding.ReceiptOn R e i r c q a s m Q hm
  | .marked J o i r d => FundedMarkedWindingWindow.ReceiptOn R J J o.val D k e i r d c q a w s m Q hm

theorem quoteWithRate (D k : V→ℕ) (t : Row V e) (w : Gear G→ℝ) (hw : ∀ I,0<w I) :
    ∃ (v : ℕ→Gear G→ℝ) (s : Gear G→ℝ) (a : ℕ), (∀ I,0<s I) ∧
      (∀ j I,(s I)⁻¹≤v j I) ∧
      ∀ (R : Run G) (_ : G.Simple), RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, ∀ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws=R.family.path.levels → Q.paid=R.metals.O → Q.y=zz R.family.path.levels →
        v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m →
        Receipt R D k c q a w s m Q hm t := by
  cases t with
  | vacuum i r =>
    exact RootedVacuumWinding.pricedOnWithRate e i r (by omega) w hw
  | marked J o i r d =>
    obtain ⟨v,s,a,hs,bill,_,buy⟩ := FundedMarkedWindingWindow.pricedOnWithRate (Subset.rfl : J⊆J) o.val o.property
      D k e i r (by omega) w hw d
    refine ⟨v,s,a,hs,bill,?_⟩
    intro R hG paid c q
    filter_upwards [buy R hG paid c q] with m buy
    exact fun Q hm _ _ hy fee => buy Q hm hy fee

theorem quote (D k : V→ℕ) (t : Row V e) (w : Gear G→ℝ) (hw : ∀ I,0<w I) :
    ∃ (v : ℕ→Gear G→ℝ) (s : Gear G→ℝ) (a : ℕ), (∀ I,0<s I) ∧
      ∀ (R : Run G) (_ : G.Simple), RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, ∀ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws=R.family.path.levels → Q.paid=R.metals.O → Q.y=zz R.family.path.levels →
        v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m →
        Receipt R D k c q a w s m Q hm t := by
  obtain ⟨v,s,a,hs,_,witness⟩ := quoteWithRate D k t w hw
  exact ⟨v,s,a,hs,witness⟩

variable {v : ℕ} {T : Type} [Fintype T]

def Sale (R : Run G) (C : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit)
    (menu : T→Row (Fin v) e) (w s : T→Gear G→ℝ) (a : T→ℕ)
    (donor : ℕ→Gear G→ℝ) (c q m : ℕ) : Prop :=
  ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
    Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧
    Q.anchor=m ∧ Cloze (NativeMarkedAddressTokens.axes O) k Q Credit.leanC ∧
    Insure v (mass k univ) Q Credit.leanC ∧
    (∀ j,m≤j → ∀ hj : Q.anchor ≤ j, ∃ z : 5≤R.family.path.levels.clock.J (j+1),
      (Q.mint j hj).σ=crestM R.family.path.levels j z ∧
      donor (R.family.path.levels.clock.J (j+1)) (Q.mint j hj).gear≤Q.cash Credit.leanC j) ∧
    OriginalRunMarkedPacketPurchase.proceeds C k O R Q hm ∧
    ∀ t,Receipt R (NativeMarkedAddressTokens.axes O) k c q (a t) (w t) (s t) m Q hm (menu t)

/-- The complete finite menu is quoted before R. A larger original donor
keeps the registered account for every ensuing stage of the very same realm. -/
theorem presoldWithRate (C : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit)
    (hk : ∀ x,k x<NativeMarkedAddressTokens.axes O x)
    (menu : T→Row (Fin v) e) (w : T→Gear G→ℝ) (hw : ∀ t I,0<w t I) :
    ∃ (v₀ : ℕ→Gear G→ℝ) (s : T→Gear G→ℝ) (a : T→ℕ), (∀ t I,0<s t I) ∧
      (∀ t j I,(s t I)⁻¹≤v₀ j I) ∧
      FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v₀) ∧
      ∀ (R : Run G) (_ : G.Simple) (donor : ℕ→Gear G→ℝ),
        FundedMarkedCoverRows.prices donor R.kit →
        (∀ᶠ m : ℕ in atTop, ∀ I,v₀ (R.family.path.levels.clock.J (m+1)) I≤
          donor (R.family.path.levels.clock.J (m+1)) I) →
        RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
        ∀ᶠ m : ℕ in atTop,Sale R C k O menu w s a donor c q m := by
  classical
  choose costs s a rates inverse spend using fun t =>
    quoteWithRate (NativeMarkedAddressTokens.axes O) k (menu t) (w t) (hw t)
  let v₀ : ℕ→Gear G→ℝ := fun j I => ∑ t : T,max 0 (costs t j I)
  have individual (t : T) (j : ℕ) (I : Gear G) : costs t j I≤v₀ j I :=
    (le_max_right ..).trans (single_le_sum (fun x _ => le_max_left 0 (costs x j I)) (mem_univ t))
  refine ⟨v₀,s,a,rates,fun t j I => (inverse t j I).trans (individual t j I),
    FundedMarkedCoverRows.purchase v₀,?_⟩
  intro R hG donor funded tender readout c q
  have measurements := eventually_all.mpr (fun t => spend t R hG readout c q)
  filter_upwards [FundedMarkedCoverRows.realm R hG donor funded v k _ hk e v (mass k univ),
    tender,OriginalRunMarkedPacketPurchase.onRealm C k O R (e:=e) hG,measurements]
    with m witness ceiling issue allRows
  obtain ⟨Q,draws,stock,hy,anchor,closed,insured,_,mint⟩ := witness
  have hm : Q.anchor ≤ m := anchor.le
  obtain ⟨_,_,account⟩ := mint m le_rfl hm
  refine ⟨Q,hm,draws,stock,hy,anchor,closed,insured,mint,issue Q hm hy closed insured,?_⟩
  intro t
  exact allRows t Q hm draws stock hy
    ((individual t _ _).trans ((ceiling _).trans account))

theorem presold (C : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit)
    (hk : ∀ x,k x<NativeMarkedAddressTokens.axes O x)
    (menu : T→Row (Fin v) e) (w : T→Gear G→ℝ) (hw : ∀ t I,0<w t I) :
    ∃ (v₀ : ℕ→Gear G→ℝ) (s : T→Gear G→ℝ) (a : T→ℕ), (∀ t I,0<s t I) ∧
      FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v₀) ∧
      ∀ (R : Run G) (_ : G.Simple) (donor : ℕ→Gear G→ℝ),
        FundedMarkedCoverRows.prices donor R.kit →
        (∀ᶠ m : ℕ in atTop, ∀ I,v₀ (R.family.path.levels.clock.J (m+1)) I≤
          donor (R.family.path.levels.clock.J (m+1)) I) →
        RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
        ∀ᶠ m : ℕ in atTop,Sale R C k O menu w s a donor c q m := by
  obtain ⟨v₀,s,a,rates,_,sale,issued⟩ := presoldWithRate C k O hk menu w hw
  exact ⟨v₀,s,a,rates,sale,issued⟩

/-- A genuine run and original physical campaign for the entire requested menu.
All original external integrands, periods, cutoffs and sensors follow the sale. -/
theorem original (hG : G.Simple) {ε : ℝ} (hε : 0<ε)
    (C : Census (Fin v)) (k : Fin v→ℕ) (O : Fin v→Orbit)
    (hk : ∀ x,k x<NativeMarkedAddressTokens.axes O x)
    (menu : T→Row (Fin v) e) (w : T→Gear G→ℝ) (hw : ∀ t I,0<w t I)
    (P : FundedCompanySelection.Prediction G) (hP : FundedPredictionSupply.AllPrices (@P)) :
    ∃ (v₀ : ℕ→Gear G→ℝ) (s : T→Gear G→ℝ) (a : T→ℕ),
      (∀ t I,0<s t I) ∧ ∃ (R : Run G) (ground : Campaign R) (W : Campaign.Pillars R ground),
        FundedMarkedCoverRows.prices v₀ R.kit ∧ P R.kit ∧ NativeFVAPlateau.Correlations R ∧
        FundedOriginalProperties.{u} hG ε W ∧ ∀ c q : ℕ,
        ∀ᶠ m : ℕ in atTop,Sale R C k O menu w s a v₀ c q m := by
  obtain ⟨v₀,s,a,rates,_,sale⟩ := presold C k O hk menu w hw
  obtain ⟨R,ground,W,paid,other,corr,facts⟩ := FundedMarkedCoverRows.original.{u} hG hε v₀ P hP
  have readout : RG05Preconstruction.ReadoutPurchase R.b := facts.2.2.2.2.2.2.1
  exact ⟨v₀,s,a,rates,R,ground,W,paid,other,corr,facts,sale R hG v₀ paid
    (Eventually.of_forall (fun _ _ => le_rfl)) readout⟩

end YM.Integration.OriginalCommonWindingMarket
end
