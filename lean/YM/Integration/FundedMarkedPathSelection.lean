import YM.Integration.FundedMarkedCoverRows
import YM.WilsonCoeffUV.Marked.Paths.Height

/-! Select the genuine cover packets of the normalized one-step marked
logarithm before test evaluation. The field path and every independently
located marked stub share a single absolute expense. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedMarkedPathSelection
open Function Filter Finset MeasureTheory Lattice RG Precision Wilson Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical

variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι]
variable {S J : Finset ι} {k D : ι → ℕ} {e m N : ℕ} {A : ℝ}

/-- The raw fine input for each choice of the independent coarse centres. Its
cell address and all Euclidean source tests are still unevaluated. -/
structure Input (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m)
    (S : Finset ι) (k D : ι → ℕ) (A : ℝ) where
  familyAt : (ι → Cover) → family G D
  offsets : (ι → Cover) → ι → Site (ll Q.draws m).L
  empty y : familyAt y ∅ = 0
  degree y : Eu k (familyAt y)
  price y : safeB (fun b => (ll Q.draws m).L.val • y b + lift (offsets y b))
    (familyAt y) S e (Q.mint (m+1) (by omega)).σ A

variable {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}

abbrev output (X : Input Q hm S k D A) (J : Finset ι) (N : ℕ) (y : ι → Cover) :=
  logO Q.draws Q.paid m N (X.familyAt y) k J

abbrev price (Q : Realm G (e+1) Credit.leanC) (k D : ι → ℕ) (A : ℝ) (J : Finset ι) (m : ℕ) :=
  Q.cash (vigor G D k e Credit.leanC Credit.leanC) m * A^J.card

private theorem cash_nn (Q : Realm G (e+1) Credit.leanC) (h : Q.anchor ≤ m)
    (hA : 0 ≤ A) : 0 ≤ price Q k D A J m :=
  mul_nonneg (zero_le_one.trans (Credit.purchase _ (Q.depth m h))) (pow_nonneg hA _)

theorem ready (X : Input Q hm S k D A) (hJ : J ⊆ S) (hA : 0 ≤ A)
    (hN : m < N) (paid : Cloze D k Q Credit.leanC) (y : ι → Cover) :
    Auth (mass k J) (output X J N y) ∧ ∀ j < e+1, ∀ r,
      Wig Bank.terrain y (Vσ Q m hm) (price Q k D A J m) J ((output X J N y).2 j r) := by
  refine ⟨step_L Q.draws Q.paid m N (X.familyAt y) k hN Q.hG Q.green (X.degree y) J, ?_⟩
  intro j hj r
  exact (waltz Q paid (X.familyAt y) (X.degree y) (X.empty y) m N hm hN y
    (X.offsets y) (X.price y) hJ hA (Nat.le_of_lt_succ hj) (r:=r)).shave
      ((min_le_right ..).trans (pureEl (Q.mint m hm).gear).le)

/-- Selection for any anchor, nominal order and field tensor rank. The common
joint measure on all marked derivative addresses is chosen before all test
functions. In particular the invoice for `r.val < j` has no factor `g^(j-r)`.
`lease` includes each original thin field path and its coefficient. `feeH`
includes every independently positioned source, each with its own stub. -/
theorem measured (X : Input Q hm S k D A) (hJ : J ⊆ S) (hA : 0 ≤ A)
    (hN : m < N) (closed : Cloze D k Q Credit.leanC) (B : ℕ) (hB : J.card ≤ B)
    (tickets : Insure B (mass k J) Q Credit.leanC) (c : ι) (hc : c ∈ J)
    (origin : Cover) (j : ℕ) (hj : j < e+1) (r : Fin (mass k J+j+1)) :
    let width := VestS B (mass k J) Q m hm
    let packets := packetH J (output X J N) (mass k J) (e+1) c origin
    let Z := fun a : Frill J c => packets a j r
    ∃ μ : (a : Frill J c × RadP G r.val) → Stationary.Ink G r.val → Measure (Sky D),
      (∀ a, Barn (Z a.1 a.2) (μ a)) ∧
      SumBudget (fun a : Frill J c × RadP G r.val =>
        Real.exp (width*feeH (toe J c origin a.1) c J) * lease (Z a.1 a.2) (μ a) width)
        (glacier G (mass k J) (e+1) * VestZ B (mass k J) Q m hm *
          price Q k D A J m * sprigs J c (Vσ Q m hm)) := by
  exact rolled_sum (tickets.proof m hm) (output X J N) hc le_rfl hB le_rfl
    (cash_nn Q hm hA) (fun y => (ready X hJ hA hN closed y).1)
    (fun y => (ready X hJ hA hN closed y).2) origin j hj r

/-- The very same selected path shell renders the specified coefficient on
every period. The finite operator here is explicitly the periodization of
the cover. Its winding comparison has a separate, quantitative invoice. -/
theorem rendering (X : Input Q hm S k D A) (hJ : J ⊆ S) (hA : 0 ≤ A)
    (hN : m < N) (closed : Cloze D k Q Credit.leanC) (B : ℕ) (hB : J.card ≤ B)
    (tickets : Insure B (mass k J) Q Credit.leanC) (c : ι) (hc : c ∈ J)
    (y : ι → Cover) (j : ℕ) (hj : j < e+1) :
    let P := sphere (output X J N y) (mass k J) (e+1) c y
    let t := shifted (baton P (e+1)) (y c)
    Auth (mass k J) t ∧ t.2 j = (output X J N y).2 j ∧
      ∀ n r, t.1 n j r = Bank.Carp.plume ((output X J N y).2 j r) n := by
  have h := ready X hJ hA hN closed y
  exact (posting (tickets.proof m hm) y (output X J N y) hc le_rfl hB
    (price Q k D A J m) (cash_nn Q hm hA) h.1 h.2 (le_refl (e+1))).2.2 j hj

end YM.Integration.FundedMarkedPathSelection
end
