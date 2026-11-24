import YM.Integration.WilsonLimitConstruction.CostDictionaryInput
import YM.Integration.WilsonLimitConstruction.FundedCostDictionary
import YM.Integration.WilsonLimitConstruction.NativeInheritedRate

/-! Stage-dependent costs on the very allocation selected for the cost dictionary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedDictionaryRenderPrices

open Filter Lattice RG RG.Supply Precision Marker FullQLocal
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open ActualOriginalQCountableRequests FullQLocal.PreRun
open scoped Classical Topology BigOperators

variable {G : Gauge} {hG : G.Simple} {P : ActualQlocalRequestFamily.Recipe}

abbrev Tariff (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe) :=
  ∀ s q, FundedCostDictionary.Demand hG P s q → ℕ → ℕ → ℝ → ℝ

def Pointwise (F : Tariff hG P) : Prop :=
  ∀ s q D k i (δ : ℝ), 0 < δ → ∀ᶠ b : ℝ in atTop, F s q D k i b ≤ b^δ

abbrev PostTariff (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe) :=
  ∀ s q, FundedCostDictionary.Demand hG P s q → (ℕ → ℕ) → ℕ → ℕ → ℝ → ℝ

abbrev Rows (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe) :=
  ∀ s q, FundedCostDictionary.Demand hG P s q → (ℕ → ℕ) → ℕ → ℕ → ℝ

def PostPointwise (F : PostTariff hG P) : Prop :=
  ∀ s q D L k i (δ : ℝ), 0 < δ → ∀ᶠ b : ℝ in atTop, F s q D L k i b ≤ b^δ

private def exponent (n : ℕ) : ℝ := 1/(n+1)

private theorem positive (n : ℕ) : 0 < exponent n := by
  unfold exponent
  positivity

private def threshold (F : PostTariff hG P) (bounded : PostPointwise F) : Rows hG P :=
  fun s q D L row i => Classical.choose (Filter.eventually_atTop.1
    (bounded s q D L (Nat.unpair row).1 i (exponent (Nat.unpair row).2) (positive _)))

private theorem above (F : PostTariff hG P) (bounded : PostPointwise F)
    (s : Sheet G) (q : MapPrices) (D : FundedCostDictionary.Demand hG P s q)
    (L : ℕ → ℕ) (k d i : ℕ) (b : ℝ) (hb : threshold F bounded s q D L (Nat.pair k d) i ≤ b) :
    F s q D L k i b ≤ b^(exponent d) := by
  have h := Classical.choose_spec (Filter.eventually_atTop.1
    (bounded s q D L (Nat.unpair (Nat.pair k d)).1 i
      (exponent (Nat.unpair (Nat.pair k d)).2) (positive _))) b hb
  simpa only [Nat.unpair_pair] using h

def joined (old fresh : ℕ → ℕ → ℝ) (k i : ℕ) : ℝ :=
  max |old k i| |fresh k i|

theorem paid_part {A : Levels G} {T U : ℕ → ℕ → ℝ}
    (h : ∀ k i, |T k i| ≤ |U k i|) (paid : NativeDiagonalClockRequest.PaidRequests U A) :
    NativeDiagonalClockRequest.PaidRequests T A := by
  refine ⟨paid.1,?_⟩
  intro k
  obtain ⟨first,hf⟩ := paid.2 k
  exact ⟨first,fun m hm i hi => (h k i).trans (hf m hm i hi)⟩

/-- Countably many real costs can depend on the actual selected pre-Run
dictionary and the genuine block lengths, before the delay chooses beta. -/
theorem paid_rows (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (available : ∀ s q, Nonempty (FundedCostDictionary.Demand hG P s q))
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction)) (rows : Rows hG P) :
    ∃ A : FundedCostDictionary.PredictionPurchase hG P Δ ε (@prediction),
      let receipt := A.original.dictionary.purchase
      let L := A.original.run.family.path.levels
      NativeDiagonalClockRequest.PaidRequests
        (rows receipt.sheet receipt.quote receipt.chosen (fun i => (L.clock.factor i).val)) L := by
  obtain ⟨native,hPrediction⟩ := FundedPlateauRun.purchase hG Δ hε
    (FundedCostDictionary.Demand hG P) available (fun _ _ choice => CostPaired.extra choice)
    (fun _ _ choice => CostPaired.numeric choice) (fun s q choice lengths =>
      joined (CostPaired.postnumeric choice lengths) (rows s q choice lengths)) (@prediction) paid
  obtain ⟨s,q,chosen,n,hbase,hextra,hsheet,hquote,hnumeric,hboth,hstage⟩ := native.selected
  let L := native.run.family.path.levels
  let lengths := fun i => (L.clock.factor i).val
  let old := CostPaired.postnumeric chosen lengths
  let fresh := rows s q chosen lengths
  have hOld := paid_part (T:=old)
    (fun k i => (le_max_left |old k i| |fresh k i|).trans (le_abs_self _)) hboth
  have hNew := paid_part (T:=fresh)
    (fun k i => (le_max_right |old k i| |fresh k i|).trans (le_abs_self _)) hboth
  have stage : NativePostLengthPayment.StagePaid (old 0) L := fun m =>
    (le_abs_self _).trans ((le_max_left |old 0 (L.clock.J (m+1))|
      |fresh 0 (L.clock.J (m+1))|).trans (hstage m))
  let dict : CommonConstruction.CostDictionarySupply hG P native.run :=
    ⟨⟨s,q,chosen,n,hbase,hextra,hsheet,hquote,hnumeric,hOld,stage⟩,native.readout⟩
  exact ⟨⟨⟨native.run,native.campaign,native.pillars,native.penalty,native.funded,
      native.orders,native.treasury,native.period,dict⟩,hPrediction,native.windows⟩,hNew⟩

/-- One Run pays every fixed-stage subpower family even when the grades and
fees vary along its successive physical blocks. -/
theorem postpurchase (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (available : ∀ s q, Nonempty (FundedCostDictionary.Demand hG P s q))
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction))
    (F : PostTariff hG P) (bounded : PostPointwise F) :
    ∃ A : FundedCostDictionary.PredictionPurchase hG P Δ ε (@prediction),
      let receipt := A.original.dictionary.purchase
      let L := A.original.run.family.path.levels
      ∀ k (δ : ℝ), 0 < δ → ∀ᶠ m : ℕ in atTop, ∀ i, i ≤ L.clock.J (m+1) →
        F receipt.sheet receipt.quote receipt.chosen (fun j => (L.clock.factor j).val) k i
          (L.clock.hatBeta m) ≤ (L.clock.hatBeta m)^δ := by
  obtain ⟨A,hNew⟩ := paid_rows hG P Δ hε available (@prediction) paid (threshold F bounded)
  refine ⟨A,?_⟩
  dsimp only
  intro k δ hδ
  obtain ⟨d,hd⟩ := exists_nat_one_div_lt hδ
  obtain ⟨first,hf⟩ := hNew.2 (Nat.pair k d)
  let S := A.original.dictionary.purchase
  let L := A.original.run.family.path.levels
  let lengths := fun i => (L.clock.factor i).val
  filter_upwards [eventually_ge_atTop first,(WardBin.bell L hG).eventually_ge_atTop 2]
    with m hm hhot
  intro i hi
  have hb : 1 < L.clock.hatBeta m := by linarith
  have hlog := Real.log_le_sub_one_of_pos (Real.log_pos hb)
  have hbaseLog := Real.log_le_sub_one_of_pos (zero_lt_one.trans hb)
  have hc : threshold F bounded S.sheet S.quote S.chosen lengths (Nat.pair k d) i ≤ L.clock.hatBeta m :=
    ((le_abs_self _).trans (hf m hm i hi)).trans (by linarith)
  exact (above F bounded S.sheet S.quote S.chosen lengths k d i _ hc).trans
    (Real.rpow_le_rpow_of_exponent_le hb.le hd.le)

theorem purchase (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe)
    (Δ : Decal G) {ε : ℝ} (hε : 0 < ε)
    (available : ∀ s q, Nonempty (FundedCostDictionary.Demand hG P s q))
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction))
    (F : Tariff hG P) (bounded : Pointwise F) :
    ∃ A : FundedCostDictionary.PredictionPurchase hG P Δ ε (@prediction),
      let receipt := A.original.dictionary.purchase
      let L := A.original.run.family.path.levels
      ∀ k (δ : ℝ), 0 < δ → ∀ᶠ m : ℕ in atTop, ∀ i, i ≤ L.clock.J (m+1) →
        F receipt.sheet receipt.quote receipt.chosen k i (L.clock.hatBeta m) ≤
          (L.clock.hatBeta m)^δ :=
  postpurchase hG P Δ hε available (@prediction) paid (fun s q D _ => F s q D)
    (fun s q D _ => bounded s q D)

end YM.Integration.WilsonLimitConstruction.FundedDictionaryRenderPrices
end
