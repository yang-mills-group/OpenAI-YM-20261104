import YM.Integration.WilsonRegisteredTwoBirthDates
import YM.Integration.WilsonMeasuredWindingRoom
import YM.Integration.WilsonFundedWindingHistory

/-! Sum the registered two-birth winding currents along an arbitrary ultraviolet history
on one elected measured Wilson realm, before the period is removed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRegisteredTwoBirthWindingSum
open Function Filter Finset Set Lattice RG RG.Supply Wilson Source Labels Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank.Mosaic.Near WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Blue FundedMarkedPathSelection OriginalRootedPacketLayout Work.F08
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction ActualRunAdmissionScales SignedRootedWindingReadout
open WilsonRegisteredTwoBirthDates WilsonFundedWindingHistory
open scoped BigOperators Classical Topology
variable {G : Gauge} {v : ℕ}

/-- One independent normalized complex test on every charged marked address. -/
def heard {ι α : Type} [DecidableEq ι] {D : ι → ℕ} (J : Finset ι) (o : ι) (r : ℕ)
    (P : (ι → Cover) → Ten (Pen D J) (Cloth α) r) (z : ℂ) : Prop :=
  ∃ (x : Cover) (v : Fence α J o r → Tests D) (ξ : Fence α J o r → ℂ),
    (∀ j, amplitude J (v j) ≤ 1) ∧ (∀ j, ‖ξ j‖ ≤ 1) ∧
    z = ∑' j, ξ j * read J (v j) (towerV J o r P x j)

/-- The signed folded-input currents arise from one original run and one independent bank.
All admissible cutoffs and all independent cells and marked tests share the same bound. -/
theorem original (J : Finset (Fin v)) (o : Fin v) (ho : o ∈ J)
    (grades weights k transport : Fin v → ℕ) (hk : ∀ z, k z < dims grades weights z)
    (e a r d budget : ℕ) (ha : a ≤ e) :
    let D := dims grades weights
    ∃ (v₀ : ℕ → Gear G → ℝ) (s : Gear G → ℝ) (degree : ℕ),
      FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v₀) ∧
      ∀ (R : Run G), G.Simple → FundedMarkedCoverRows.prices v₀ R.kit →
      RG05Preconstruction.ReadoutPurchase R.b → ∀ {deck : MS.Local.Physical.Deck G}
      (P : MS.Land.Prescription deck) (labs : Fin v → MS.Rake.Label deck) (μ : ℝ)
      (normal : Fin v → ℂ) (quad : Fin v → Bool) (K : ℝ), 0 ≤ K →
      let L := R.family.path.levels
      ∃ (C : ℝ) (h : ℕ), 0 < C ∧ ∀ᶠ m in atTop,
        ∃ (Q : Realm G (e+1) Credit.leanC) (anchor : Q.anchor = m) (A : ℕ → ℝ),
          Q.draws = L ∧ Q.paid = R.metals.O ∧ Q.y = zz L ∧
          (∀ i, m ≤ i → 0 ≤ A i ∧ A i ≤ C*(L.clock.hatBeta i)^h) ∧
          ∀ n N, m+n+1 ≤ N → ∀ (x y : Fin n → Fin v → ℕ), (∀ j z, x j z ≤ budget) →
          (∀ j z, y j z ≤ budget) → ∀ (old : Fin n → Finset (Fin v))
            (cells : ∀ j : Fin n, (Fin v → Cover) → Fin v → Site (loose Q.draws (m+j.val)).L),
            ∃ T : ∀ j : Fin n, Input Q (m:=m+j.val) (by omega) univ k D (A (m+j.val)),
              (∀ j, represents R P grades weights labs μ normal quad transport k
                (x j) (y j) N (old j) (cells j) (T j)) ∧
              ∀ per, ∃ B : Fin n → ℝ, (∀ j, let i := m+j.val
                let σ := s (Q.mint i (by dsimp [i]; omega)).gear
                PostMark J o r (current R J o a r N per (T j)) (σ/32/2/2/2) (B j) d ∧
                B j ≤ (admittedCost L i)^degree *
                  (Real.exp (-(σ/512)*((R.family.side i per).val : ℝ))*(A i)^J.card)) ∧
                ∀ (τ : Fin n → ℝ) (z : Fin n → ℂ), (∀ j, 0 ≤ τ j) →
                (∀ j, τ j ≤ WilsonMeasuredWindingSum.room L K (m+j.val)) →
                (∀ j, heard J o r (current R J o a r N per (T j)) (z j)) →
                ∑ j, τ j*‖z j‖ ≤ 2*Real.exp (-((L.S.period per).val:ℝ)*(L.clock.hatBeta m)^2/2048) := by
  classical
  intro D
  obtain ⟨v₀,s,degree,hot,price,offer,spent⟩ := FundedMarkedWindingWindow.pricedOnWithRate
    (subset_univ J) o ho D k e a r ha (fun M : Gear G => M.past) (fun M => M.depth) d
  refine ⟨v₀,s,degree,offer,?_⟩
  intro R simple enrolled readout deck P labs μ normal quad K hK L
  obtain ⟨C,h,hC,sources⟩ := WilsonRegisteredTwoBirthDates.original R simple P grades weights labs
    μ normal quad transport k e budget
  obtain ⟨b₀,spent₀⟩ := eventually_atTop.1 (spent R simple readout 0 0)
  obtain ⟨b₁,paid₁⟩ := eventually_atTop.1 (FundedMarkedWindingWindow.credit L simple Credit.leanC)
  obtain ⟨b₂,room₂⟩ := eventually_atTop.1
    (WilsonMeasuredWindingRoom.original R simple readout degree h J.card C K)
  let k' := K+(↑(degree+(h+1)*J.card):ℝ)
  have hk' : 0 ≤ k' := add_nonneg hK (Nat.cast_nonneg _)
  refine ⟨C,h,hC,?_⟩
  filter_upwards [sources,eventually_ge_atTop b₀,eventually_ge_atTop b₁,eventually_ge_atTop b₂,
    FundedMarkedCoverRows.realm R simple v₀ enrolled v k D hk e J.card (mass k J),
    WilsonMeasuredWindingSum.invoice R simple readout hk'] with m source late₀ late₁ late₂ realm numerical
  obtain ⟨Q,draws,physical,same,anchor,cloze,_,_,reserve⟩ := realm
  have unit (i : ℕ) (age : m ≤ i) : (Q.mint i (anchor.le.trans age)).σ ≤ 1 := by
    obtain ⟨f,st,_⟩ := reserve i age (anchor.le.trans age)
    exact st.le.trans (WilsonCoeffUV.StableStrip.crest_le_one L i f)
  obtain ⟨A,bill,issue⟩ := source Q anchor.le draws same cloze unit
  refine ⟨Q,anchor,A,draws,physical,same,bill,?_⟩
  intro n N top x y hx hy old cells
  have material (j : Fin n) := issue (m+j.val) (by omega) N (by omega)
    (x j) (y j) (hx j) (hy j) (old j) (cells j)
  choose T represented using material
  refine ⟨T,represented,?_⟩
  intro per
  have receipts (j : Fin n) :
      let i := m+j.val
      let σ := s (Q.mint i (by dsimp [i]; omega)).gear
      ∃ B : ℝ, PostMark J o r (current R J o a r N per (T j)) (σ/32/2/2/2) B d ∧
        B ≤ (admittedCost L i)^degree*(Real.exp (-(σ/512)*((R.family.side i per).val:ℝ))*(A i)^J.card) ∧
        σ⁻¹ ≤ admittedCost L i := by
    intro i σ
    have age : m ≤ i := Nat.le_add_right .. 
    have head := anchor.le.trans age
    obtain ⟨_,_,quote⟩ := reserve i age head
    have ear := spent₀ i (late₀.trans age) Q head same quote
    have pre z : Eu k ((T j).familyAt z) ∧ (T j).familyAt z ∅ = 0 ∧
        safeB (chartIn (loose Q.draws i) z ((T j).offsets z)) ((T j).familyAt z) univ e
          (Q.mint i head).gear.past (A i) :=
      ⟨(T j).degree _,(T j).empty _,fun S hS l hl r => ((T j).price z S hS l hl r).shave (Q.crossing i head)⟩
    obtain ⟨B,_,cost,mark⟩ := ear N per (by dsimp [i]; omega) (T j).familyAt (T j).offsets
      (A i) (bill i age).1 pre
    refine ⟨B,mark,cost,(price _ _).trans (quote.trans ?_)⟩
    simpa only [Realm.cash,same,Credit.leanC,Credit.buy,one_mul,pow_one] using (paid₁ i (late₁.trans age)).2.1
  choose B marked cost width using receipts
  refine ⟨B,fun j => ⟨marked j,cost j⟩,?_⟩
  intro τ z hτ hτ' readings
  let H := Real.exp (-((L.S.period per).val:ℝ)*(L.clock.hatBeta m)^2/2048)
  calc _ ≤ ∑ j : Fin n, H*(1/2:ℝ)^j.val := by
         apply Finset.sum_le_sum
         intro j _
         let i := m+j.val
         let σ := s (Q.mint i (by dsimp [i]; omega)).gear
         let E := Real.exp (-(σ/512)*((R.family.side i per).val:ℝ))
         have hs : 0 < σ := hot _
         have a := bill i (Nat.le_add_right ..)
         obtain ⟨u,v,ξ,vp,sp,reads⟩ := readings j
         have test := (SignedRootedWindingReadout.tested J ho (by positivity) (marked j)
           u v 1 zero_le_one vp ξ sp).2
         have readnorm : ‖z j‖ ≤ B j := by rw [reads]; exact test.trans_eq (one_mul _)
         have room := room₂ i (late₂.trans (Nat.le_add_right ..)) (τ j) (A i) (hτ j)
           (hτ' j) a.1 a.2
         calc _ ≤ τ j*B j := mul_le_mul_of_nonneg_left readnorm (hτ j)
              _ ≤ τ j*((admittedCost L i)^degree*(E*(A i)^J.card)) :=
                mul_le_mul_of_nonneg_left (cost j) (hτ j)
              _ = (τ j*(admittedCost L i)^degree*(A i)^J.card)*E := by ring
              _ ≤ WilsonMeasuredWindingSum.room L k' i*E := mul_le_mul_of_nonneg_right room (Real.exp_pos _).le
              _ ≤ _ := numerical j.val per σ hs (width j)
       _ = H*∑ j : Fin n, (1/2:ℝ)^j.val := (Finset.mul_sum ..).symm
       _ ≤ _ := by
         rw [mul_comm 2 H]
         apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
         rw [Fin.sum_univ_eq_sum_range]
         have geo := hasSum_geometric_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)
         have fin := sum_le_hasSum (Finset.range n) (fun j _ => pow_nonneg (by norm_num : 0 ≤ (1/2:ℝ)) j) geo
         norm_num at fin ⊢
         exact fin

end YM.Integration.WilsonRegisteredTwoBirthWindingSum
end

