import YM.Integration.FullQLocalCostProfileResources
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! Purchase the original countable floors, current widths and both cash
calendars independently of the terminal formal action law. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonLimitConstruction.FundedNeutralCostRun
open Filter Lattice RG RG.Supply Precision
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open FullQLocal.PreRun.CostProfile

variable {G : Gauge}

abbrev Inventory (G : Gauge) :=
  ∀ s : Sheet G, MapPrices → NativeComponentRecipe.Choice s → ℕ → Resources

def floor (I : Inventory G) (s : Sheet G) (q : MapPrices) (C : NativeComponentRecipe.Choice s) (i : ℕ) :=
  max (NativeComponentRecipe.floor s q C i) (Resources.extra s.floorL (I s q C) i)

def join (x y : ℝ) := max |x| |y|

def numeric (I : Inventory G) (s : Sheet G) (q : MapPrices) (C : NativeComponentRecipe.Choice s) (k i : ℕ) :=
  join (NativeComponentRecipe.numeric s q C k i) (Resources.numeric (I s q C) k i)

def post (I : Inventory G) (s : Sheet G) (q : MapPrices) (C : NativeComponentRecipe.Choice s)
    (L : ℕ→ℕ) (k i : ℕ) :=
  join (ActualRunNativeComponentRecipe.postnumeric s q C L k i) (Resources.postnumeric (I s q C) L k i)

private theorem paid_le {F K : ℕ→ℕ→ℝ} {A : Levels G}
    (le : ∀ k i, |F k i|≤|K k i|) (paid : NativeDiagonalClockRequest.PaidRequests K A) :
    NativeDiagonalClockRequest.PaidRequests F A := by
  refine ⟨paid.1,?_⟩
  intro k
  obtain ⟨first,all⟩ := paid.2 k
  exact ⟨first,fun m hm i hi => (le k i).trans (all m hm i hi)⟩

structure Purchase (I : Inventory G) (R : Run G) where
  sheet : Sheet G
  quote : MapPrices
  choice : NativeComponentRecipe.Choice sheet
  lengths : ℕ→ℕ
  base : sheet.floorL≤lengths
  original_sheet : R.metals.p=PhysicalNext.ThroughLaunch.raise sheet lengths
  original_quote : R.metals.K=PhysicalNext.ThroughLaunch.raging sheet quote
  components : NativeComponentRecipe.Realized sheet quote choice R.family.path.levels R.alloy.B.M
  numbers : Resources.Receipt (I sheet quote choice) R sheet.floorL lengths

theorem split (I : Inventory G) (R : Run G)
    (H : R2I.RG05Joint.PostnumericPreselection (fun s (_ : MapPrices) => NativeComponentRecipe.Choice s)
      (floor I) (numeric I) (post I) R) :
    ActualRunNativeComponentRecipe.Attached R ∧ Nonempty (Purchase I R) := by
  obtain ⟨s,q,C,n,hb,hf,hs,hq,hn,hp,ht⟩ := H
  have left (x y : ℝ) : |x|≤|join x y| := (le_max_left _ _).trans (le_abs_self _)
  have right (x y : ℝ) : |y|≤|join x y| := (le_max_right _ _).trans (le_abs_self _)
  have nativeFloor : NativeComponentRecipe.floor s q C ≤ n :=
    fun i => (le_max_left _ _).trans (hf i)
  have paid := paid_le (F:=NativeComponentRecipe.numeric s q C) (K:=numeric I s q C) (fun k i => left (NativeComponentRecipe.numeric s q C k i)
    (Resources.numeric (I s q C) k i)) hn
  let L := fun i => (R.family.path.levels.clock.factor i).val
  have postPaid := paid_le (F:=ActualRunNativeComponentRecipe.postnumeric s q C L) (K:=post I s q C L) (fun k i => left (ActualRunNativeComponentRecipe.postnumeric s q C L k i)
    (Resources.postnumeric (I s q C) L k i)) hp
  have stage : NativePostLengthPayment.StagePaid (NativeComponentRecipe.post s q C L) R.family.path.levels :=
    fun m => (le_abs_self _).trans ((le_max_left _ _).trans (ht m))
  have hC := ActualRunNativeComponentRecipe.on_run R s q C n hs hq nativeFloor stage
  refine ⟨⟨s,q,C,n,hb,nativeFloor,hs,hq,paid,postPaid,stage,hC⟩,
    ⟨⟨s,q,C,n,hb,hs,hq,hC,?_⟩⟩⟩
  refine ⟨fun i => (le_max_right _ _).trans (hf i),?_,?_⟩
  · exact paid_le (fun k i => right _ (Resources.numeric (I s q C) k i)) hn
  exact paid_le (fun k i => right _ (Resources.postnumeric (I s q C) L k i)) hp

theorem original (hG : G.Simple) {ε : ℝ} (hε : 0<ε) (I : Inventory G)
    (prediction : FundedCompanySelection.Prediction G) (hpaid : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      prediction R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
      Nonempty (Purchase I R) := by
  obtain ⟨A,hPred⟩ := FundedPlateauRun.purchase hG (garment10 G) hε
    (fun s (_ : MapPrices) => NativeComponentRecipe.Choice s)
    (fun s _ => NativeComponentRecipe.available hG s) (floor I) (numeric I) (post I) (@prediction) hpaid
  obtain ⟨native,numbers⟩ := split I A.run A.selected
  exact ⟨A.run,A.campaign,A.pillars,hPred,A.correlations hG,
    fundedOriginalRun_on.{u} hG A.pillars A.penalty A.funded native A.orders A.treasury A.period A.readout,
    numbers⟩

end YM.Integration.WilsonLimitConstruction.FundedNeutralCostRun
end
