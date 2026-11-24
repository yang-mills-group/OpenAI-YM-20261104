import YM.Integration.OriginalMeasuredSourceRows
import YM.Integration.OriginalBareMarkedInvoice
import YM.Integration.WilsonMarkedAddressGeometry

/-! An actual countable curvature packet bank assembled from the rooted
cover issuer. Its row labels are a genuine marker mode, nominal order,
field rank, finite rooted path datum, and invariant colour. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalRootedPacketLayout
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Marker Precision Tree Laurent
open ComparisonDensity.Address Comparison.Density.RenderM LocalComparison
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Soil
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider
open WilsonCoeffUV.Embroider.Canvas FundedMarkedPathSelection Work.F08
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (C : Census V) (k : V → ℕ) (e : ℕ)

abbrev Block := (s : {s : C.Mode // s.val.Nonempty}) ×
  (i : Fin (e+1)) × Fin (mass k s.val.val + i.val + 1)

def owner (s : {s : C.Mode // s.val.Nonempty}) : V := s.property.choose

omit [Fintype V] in
theorem owner_mem (s : {s : C.Mode // s.val.Nonempty}) : owner C s ∈ s.val.val :=
  s.property.choose_spec

abbrev Row := (b : Block C k e) × (RadP G b.2.2.val × Stationary.Ink G b.2.2.val)

def cap := mass k Finset.univ + e

theorem degree_le (b : Block C k e) : b.2.2.val ≤ cap k e := by
  have h : mass k b.1.val.val ≤ mass k Finset.univ :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have := b.2.2.isLt
  have := b.2.1.isLt
  unfold cap
  omega

def power (b : Block C k e) : ℤ := (b.2.1.val : ℤ) - (b.2.2.val : ℤ)

theorem power_le (b : Block C k e) : (power C k e b).natAbs ≤ cap k e := by
  have hi : b.2.1.val ≤ cap k e := (Nat.le_of_lt_succ b.2.1.isLt).trans (Nat.le_add_left ..)
  have hr := degree_le C k e b
  unfold power
  omega

variable {n : Side} (p : V → Site n)

def actual (s : {s : C.Mode // s.val.Nonempty}) : Frill s.val.val (owner C s) :=
  fun v => lift (p (owner C s)) + lift (p v.val - p (owner C s))

def placed (s : {s : C.Mode // s.val.Nonempty}) : V → Cover :=
  toe s.val.val (owner C s) (lift (p (owner C s))) (actual C p s)

omit [Fintype V] in
theorem addresses (s : {s : C.Mode // s.val.Nonempty}) {v : V} (hv : v ∈ s.val.val) :
    wrap n (placed C p s v) = p v := by
  by_cases he : v = owner C s
  · subst v
    simp [placed,toe]
  have hne : v∈s.val.val.erase (owner C s) := mem_erase.mpr ⟨he,hv⟩
  simp [placed,toe,he,hne,actual,map_add,wrap_lift]

variable {e} {m N : ℕ} (O : V → Orbit) (Y : V → Dip)
variable (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
variable (X : Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A)

def atCover (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
    (source : FundedMarkedPathSelection.Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A)
    {N : ℕ} (b : Block C k e) (a : Cover)
    (t : Frill b.1.val.val (owner C b.1) × RadP G b.2.2.val) :
    Comet G (Pen (NativeMarkedAddressTokens.axes O) b.1.val.val) b.2.2.val :=
  (WilsonCoeffUV.Mer.Rolls.packetH b.1.val.val (FundedMarkedPathSelection.output source b.1.val.val N) (mass k b.1.val.val) (e+1)
    (owner C b.1) a t.1) b.2.1 b.2.2 t.2

abbrev original (p : V → Site n) (O : V → Orbit) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
    (X : FundedMarkedPathSelection.Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A) {N : ℕ} (b : Block C k e)
    (t : Frill b.1.val.val (owner C b.1) × RadP G b.2.2.val) :
    Comet G (Pen (NativeMarkedAddressTokens.axes O) b.1.val.val) b.2.2.val :=
  atCover (C:=C) (k:=k) (O:=O) (Q:=Q) (hm:=hm) (source:=X) (N:=N) b (lift (p (owner C b.1))) t

def expenses (b : Block C k e) :=
  NativeMarkedAddressTokens.cellPrice O b.1.val.val *
    (glacier G (mass k b.1.val.val) (e+1) *
      VestZ (Fintype.card V) (mass k Finset.univ) Q m hm *
      price Q k (NativeMarkedAddressTokens.axes O) A b.1.val.val m *
      sprigs b.1.val.val (owner C b.1) (Vσ Q m hm))

abbrev width := VestS (Fintype.card V) (mass k Finset.univ) Q m hm

def MeasureArray :=
  (b : Block C k e) → (t : Frill b.1.val.val (owner C b.1) × RadP G b.2.2.val) →
    Stationary.Ink G b.2.2.val → Measure (Sky (NativeMarkedAddressTokens.axes O))

def RootedMeasures :=
  (b : Block C k e) → Cover →
    (t : Frill b.1.val.val (owner C b.1) × RadP G b.2.2.val) →
    Stationary.Ink G b.2.2.val → Measure (Sky (NativeMarkedAddressTokens.axes O))

def sampled (μ : RootedMeasures C k O (e:=e) (G:=G)) : MeasureArray C k O (e:=e) (G:=G) :=
  fun b => μ b (lift (p (owner C b.1)))

def rootedSale (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
    (X : FundedMarkedPathSelection.Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A) {N : ℕ} (μ : RootedMeasures C k O (e:=e) (G:=G)) : Prop :=
  (∀ b a t, Barn (atCover C k O Q hm X (N:=N) b a t) (μ b a t)) ∧
  ∀ (b : Block C k e) a, SumBudget (fun t : Frill b.1.val.val (owner C b.1) × RadP G b.2.2.val =>
    Real.exp (width k Q hm * feeH (toe b.1.val.val (owner C b.1) a t.1) (owner C b.1) b.1.val.val) *
    lease (atCover C k O Q hm X (N:=N) b a t) (μ b a t) (width k Q hm))
    (glacier G (mass k b.1.val.val) (e+1) * VestZ (Fintype.card V) (mass k Finset.univ) Q m hm *
      price Q k (NativeMarkedAddressTokens.axes O) A b.1.val.val m * sprigs b.1.val.val (owner C b.1) (Vσ Q m hm))

/-- The common measures on every source displacement and thickness are
fixed before the period, the independently moved root sites, the affine
external test cells, and the complex probes. -/
theorem preselected (O : V → Orbit) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
    (X : FundedMarkedPathSelection.Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A) {N : ℕ}
    (hA : 0 ≤ A) (hN : m<N) (closed : Cloze (NativeMarkedAddressTokens.axes O) k Q Credit.leanC)
    (tickets : Insure (Fintype.card V) (mass k Finset.univ) Q Credit.leanC) :
    ∃ μ : RootedMeasures C k O (e:=e) (G:=G), rootedSale C k O Q hm X (N:=N) μ := by
  have hcost (J : Finset V) : 0 ≤ price Q k (NativeMarkedAddressTokens.axes O) A J m :=
    mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth m hm))) (pow_nonneg hA _)
  have sale (b : Block C k e) (a : Cover) := rolled_sum (tickets.proof m hm) (output X b.1.val.val N)
    (owner_mem C b.1)
    (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ b.1.val.val) (fun _ _ _ => Nat.zero_le _))
    (Finset.card_le_univ _) le_rfl (hcost b.1.val.val)
    (fun y => (ready X (subset_univ b.1.val.val) hA hN closed y).1)
    (fun y => (ready X (subset_univ b.1.val.val) hA hN closed y).2)
    a b.2.1.val b.2.1.isLt b.2.2
  choose μ hμ hs using sale
  exact ⟨μ,hμ,hs⟩

def token (p : V → Site n) (O : V → Orbit) (Y : V → Dip) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
    (X : FundedMarkedPathSelection.Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A) {N : ℕ} (μ : MeasureArray C k O (e:=e) (G:=G)) (v : Row (G:=G) C k e) :
    Token G n (fun v => (O v).Mood) v.1.2.2.val :=
  let loc := (actual C p v.1.1,v.2.1)
  NativeMarkedAddressTokens.token O v.1.1.val.val Y
    (original C k p O Q hm X (N:=N) v.1 loc) (μ v.1 loc) v.2.2
    (placed C p v.1.1) (owner C v.1.1) (p (owner C v.1.1)) (fun i => {p i})

private theorem sliced {U T : Type*} {f : U → ℝ} {a : ℝ} (h : SumBudget f a)
    (t : T → U) (ht : Injective t) : SumBudget (fun i => f (t i)) a := by
  have hp := h.2.1.comp_injective ht
  exact ⟨fun i => h.1 _,hp,
    (Summable.tsum_le_tsum_of_inj (f:=fun i : T => f (t i)) (g:=f) t ht (fun _ _ => h.1 _) (fun _ => le_rfl) hp h.2.1).trans h.2.2⟩

private theorem colored {U T : Type*} [Fintype T] {f : U × T → ℝ} {a : ℝ}
    (he : ∀ u, 0 ≤ f u) (H : SumBudget (fun u => ∑ t, f (u,t)) a) : SumBudget f a := by
  have full : Summable f := (summable_prod_of_nonneg he).mpr ⟨fun u => (hasSum_fintype (fun v : T => f (u,v))).summable,
    by simpa only [tsum_fintype] using H.2.1⟩
  exact ⟨he,full,by simpa only [full.tsum_prod,tsum_fintype] using H.2.2⟩

/-- One ordinary realm pays every allowed mode and all path and colour rows
at its common preselected width. No physical coupling occurs in this sale. -/
theorem purchase (p : V → Site n) (O : V → Orbit) (Y : V → Dip) (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) {A : ℝ}
    (X : FundedMarkedPathSelection.Input Q hm Finset.univ k (NativeMarkedAddressTokens.axes O) A) {N : ℕ}
    (M : RootedMeasures C k O (e:=e) (G:=G))
    (hold : rootedSale C k O Q hm X (N:=N) M) :
    let μ := sampled C k p O M
    (∀ b t, Barn (original C k p O Q hm X (N:=N) b t) (μ b t)) ∧
      ∀ b : Block C k e,
        SumBudget (fun v : RadP G b.2.2.val × Stationary.Ink G b.2.2.val =>
          let P := token C k p O Y Q hm X (N:=N) μ ⟨b,v⟩
          P.coin * Real.exp (width k Q hm * P.fall)) (expenses C k O Q hm (A:=A) b) := by
  intro μ
  refine ⟨fun b t => hold.1 b _ t,?_⟩
  intro b
  let atRoot (t : RadP G b.2.2.val) :=
    (actual C p b.1,t)
  have scaled := cap_scale (hold.2 b (lift (p (owner C b.1))))
    (show 0 ≤ NativeMarkedAddressTokens.cellPrice O b.1.val.val by
    unfold NativeMarkedAddressTokens.cellPrice; positivity)
  have hrow := sliced scaled atRoot (fun _ _ h => congrArg Prod.snd h)
  apply colored
  · intro v
    change 0 ≤ (sprigB _ _).magnitude * (NativeMarkedAddressTokens.cellPrice O b.1.val.val * _) * _
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (mul_nonneg (by unfold NativeMarkedAddressTokens.cellPrice; positivity) ENNReal.toReal_nonneg))
      (Real.exp_pos _).le
  · simpa only [token,NativeMarkedAddressTokens.expense,original,expenses,placed,width,atRoot,μ,sampled] using hrow

end YM.Integration.OriginalRootedPacketLayout
end
