import YM.Integration.FundedMarkedWindingWindow
import YM.Integration.FundedMarkedPathSelection
import YM.Integration.WilsonMeasuredWindingSum

/-! The complete winding current on every age of one funded original realm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFundedWindingHistory
open Filter Function Finset Lattice RG Laurent Next.Foundations Precision Wilson
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Embroider
open ActualRunAdmissionScales FundedMarkedPathSelection
open scoped Topology BigOperators Classical
variable {G : Gauge} {v e l : ℕ} {D k : Fin v → ℕ}

abbrev current (R : Run G) (J : Finset (Fin v)) (o : Fin v) (a r N per : ℕ)
    {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ l} {A : ℝ}
    (X : Input Q hm univ k D A) :=
  let n := R.family.side l per
  let x := fun z => PeriodicMarkedWinding.roots n z o
  RootedPeriodicMarkedWinding.row n J o (fun z =>
    Carp.plume ((output X J N (x z)).2 a r) n -
    coilH Q.draws Q.paid l N n (X.familyAt (x z)) k (ratioHigh Q.draws Q.paid N l) J a r)

theorem original (J : Finset (Fin v)) (o : Fin v) (ho : o ∈ J)
    (D k : Fin v → ℕ) (hk : ∀ i, k i < D i) (e a r d : ℕ) (ha : a ≤ e) :
    ∃ (v₀ : ℕ → Gear G → ℝ) (s : Gear G → ℝ) (deg : ℕ),
      WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v₀) ∧
      ∀ (R : Run G) (_ : G.Simple), FundedMarkedCoverRows.prices v₀ R.kit →
      RG05Preconstruction.ReadoutPurchase R.b → ∀ K : ℝ, 0 ≤ K →
      let L := R.family.path.levels
      ∀ᶠ m : ℕ in atTop, ∃ (Q : Realm G (e+1) Credit.leanC) (anchor : Q.anchor = m),
        Q.draws = L ∧ Q.paid = R.metals.O ∧ Q.y = zz L ∧
        Cloze D k Q Credit.leanC ∧ Insure J.card (mass k J) Q Credit.leanC ∧
        ∀ (N per : ℕ) (u transport : Fin (N-m) → ℝ),
          (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ transport j) →
          ∀ X : ∀ j : Fin (N-m), Input Q (m := m+j.val) (by omega) univ k D (u j),
          (∀ j : Fin (N-m), transport j*(admittedCost L (m+j.val))^deg*(u j)^J.card ≤
            WilsonMeasuredWindingSum.room L K (m+j.val)) →
          ∃ bill : Fin (N-m) → ℝ,
            (∀ j : Fin (N-m), let σ := s (Q.mint (m+j.val) (by omega)).gear
              PostMark J o r (current R J o a r N per (X j)) (σ/32/2/2/2) (bill j) d) ∧
            ∑ j, transport j*bill j ≤ 2*Real.exp (-((L.S.period per).val : ℝ)*(L.clock.hatBeta m)^2/2048) := by
  obtain ⟨v₀,s,deg,hs,hsC,offer,spent⟩ := FundedMarkedWindingWindow.pricedOnWithRate
    (subset_univ J) o ho D k e a r ha (fun I : Gear G => I.past) (fun I => I.depth) d
  refine ⟨v₀,s,deg,offer,?_⟩
  intro R simple registered readout K hK L
  obtain ⟨u₀,h₀⟩ := eventually_atTop.1 (spent R simple readout 0 0)
  obtain ⟨u₁,h₁⟩ := eventually_atTop.1 (FundedMarkedWindingWindow.credit L simple Credit.leanC)
  filter_upwards [eventually_ge_atTop u₀, eventually_ge_atTop u₁,
    FundedMarkedCoverRows.realm R simple v₀ registered v k D hk e J.card (mass k J),
    WilsonMeasuredWindingSum.invoice R simple readout hK] with m late₀ late₁ realm numerical
  obtain ⟨Q,draws,physical,same,anchor,cloze,insure,_,reserve⟩ := realm
  refine ⟨Q,anchor,draws,physical,same,cloze,insure,?_⟩
  intro N per u transport hu ht X bound
  have receipts (j : Fin (N-m)) :
      let i := m+j.val
      let σ := s (Q.mint i (by dsimp [i]; omega)).gear
      ∃ B : ℝ, PostMark J o r (current R J o a r N per (X j)) (σ/32/2/2/2) B d ∧
        B ≤ (admittedCost L i)^deg * (Real.exp (-(σ/512)*((R.family.side i per).val : ℝ))*(u j)^J.card) ∧
        0 < σ ∧ σ⁻¹ ≤ admittedCost L i := by
    intro i σ
    have early : m ≤ i := Nat.le_add_right .. 
    have head : Q.anchor ≤ i := anchor.le.trans early
    obtain ⟨_,_,quote⟩ := reserve i early head
    have ear := h₀ i (late₀.trans early) Q head same quote
    have pre x : Eu k ((X j).familyAt x) ∧ (X j).familyAt x ∅ = 0 ∧
        safeB (chartIn (loose Q.draws i) x ((X j).offsets x)) ((X j).familyAt x) univ e
          (Q.mint i head).gear.past (u j) :=
      ⟨(X j).degree _, (X j).empty _, fun T hT v hv r =>
        ((X j).price x T hT v hv r).shave (Q.crossing i head)⟩
    obtain ⟨B,_,cost,mark⟩ := ear N per (by dsimp [i]; omega) (X j).familyAt (X j).offsets (u j) (hu j) pre
    refine ⟨B,mark,cost,hs _,(hsC _ _).trans (quote.trans ?_)⟩
    simpa only [Realm.cash, same, Credit.leanC, Credit.buy, one_mul, pow_one] using (h₁ i (late₁.trans early)).2.1
  choose bill mark cost hot affordable using receipts
  refine ⟨bill,mark,?_⟩
  let H := Real.exp (-((L.S.period per).val : ℝ)*(L.clock.hatBeta m)^2/2048)
  calc _ ≤ ∑ j : Fin (N-m), H*(1/2 : ℝ)^j.val := by
         apply Finset.sum_le_sum
         intro j _
         let i := m+j.val
         let σ := s (Q.mint i (by dsimp [i]; omega)).gear
         let E := Real.exp (-(σ/512)*((R.family.side i per).val : ℝ))
         calc _ ≤ transport j*((admittedCost L i)^deg*(E*(u j)^J.card)) :=
                  mul_le_mul_of_nonneg_left (cost j) (ht j)
              _ = (transport j*(admittedCost L i)^deg*(u j)^J.card)*E := by ring
              _ ≤ WilsonMeasuredWindingSum.room L K i*E :=
                  mul_le_mul_of_nonneg_right (bound j) (Real.exp_pos _).le
              _ ≤ _ := numerical j.val per σ (hot j) (affordable j)
       _ = H*∑ j : Fin (N-m), (1/2 : ℝ)^j.val := (Finset.mul_sum ..).symm
       _ ≤ _ := by
         rw [mul_comm 2 H]
         apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
         rw [Fin.sum_univ_eq_sum_range]
         have geo := hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num)
         have fin := sum_le_hasSum (Finset.range (N-m)) (fun j _ => pow_nonneg (by norm_num : 0 ≤ (1/2 : ℝ)) j) geo
         norm_num at fin ⊢
         exact fin

end YM.Integration.WilsonFundedWindingHistory
