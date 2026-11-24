import YM.Integration.OriginalIssuedMarkedRows
import YM.Integration.NativeMarkedAddressTokens

/-! The four native expenditures in an actual field-and-address lease are
covered by one explicit credit. The emitting measure also prices the
physical curvature tokens at the same width, before multiplication by g. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalBareMarkedInvoice
open Function Filter Finset Lattice Wilson RG Laurent Next.Foundations Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls
open WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Mer.Patrol
open ComparisonDensity.Address
open WilsonCoeffUV.Shard WilsonCoeffUV.Soil FundedMarkedPathSelection OriginalIssuedMarkedRows
open WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Winding
open ActualRunAdmissionScales Work.F08 MeasureTheory
open scoped BigOperators Classical

variable {G : Gauge} {n e m i r d c q N p : ℕ} {R : Run G} {o : Fin n}
variable {J Z : Finset (Fin n)} {D k : Fin n → ℕ} {w s : Gear G → ℝ}

def addresses (J : Finset (Fin n)) (a : Fin n) : Credit :=
  (billingQ Unit (Fintype.card (J.erase a)) 0).usingC ((pur 2).prodC Credit.leanC)

def reserve (G : Gauge) (D k : Fin n → ℕ) (J : Finset (Fin n)) (a : Fin n) (e : ℕ) : Credit :=
  ((pur (glacier G (mass k J) (e+1))).prodC Credit.leanC).prodC
    ((vigor G D k e Credit.leanC Credit.leanC).prodC (addresses J a))

def native (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (D k : Fin n → ℕ)
    (J : Finset (Fin n)) (o : Fin n) (A : ℝ) :=
  glacier G (mass k J) (e+1) * VestZ J.card (mass k J) Q m hm * price Q k D A J m *
    sprigs J o (Vσ Q m hm)

theorem common {b t : ℕ} (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (ho : o ∈ J)
    (tickets : Insure b t Q Credit.leanC) (A : ℝ) (hA : 0 ≤ A) :
    glacier G (mass k J) (e+1) * VestZ b t Q m hm * price Q k D A J m *
      sprigs J o (Vσ Q m hm) ≤ Q.cash (reserve G D k J o e) m * A^J.card := by
  let V := vigor G D k e Credit.leanC Credit.leanC
  let T := pur (glacier G (mass k J) (e+1))
  have cash (B : Credit) : 0 ≤ Q.cash B m := zero_le_one.trans (Credit.purchase _ (Q.depth m hm))
  have z : 0 ≤ VestZ b t Q m hm := zero_le_one.trans (tickets.proof m hm).tag
  have roots : 0 ≤ sprigs J o (Vσ Q m hm) :=
    cap_nn (sprigsPay ho (0 : Cover) (perk hm))
  have rootBill : sprigs J o (Vσ Q m hm) ≤ Q.cash (addresses J o) m :=
    punchWorth J o b t Credit.leanC tickets hm
  have fieldBill : glacier G (mass k J) (e+1) * VestZ b t Q m hm ≤
      Q.cash T m * Q.cash Credit.leanC m :=
    mul_le_mul (pure_goal _ _) (tickets.labor m hm).2 z (cash _)
  have rest := mul_le_mul_of_nonneg_left rootBill (cash V)
  calc
    _ = ((glacier G (mass k J) (e+1) * VestZ b t Q m hm) *
        (Q.cash V m * sprigs J o (Vσ Q m hm)))*A^J.card := by unfold FundedMarkedPathSelection.price; ring
    _ ≤ ((Q.cash T m * Q.cash Credit.leanC m) * (Q.cash V m * Q.cash (addresses J o) m)) * A^J.card :=
      mul_le_mul_of_nonneg_right (mul_le_mul fieldBill rest (mul_nonneg (cash V) roots)
        (mul_nonneg (cash T) (cash _))) (pow_nonneg hA _)
    _ = _ := by simp only [reserve, Realm.cash, Credit.products, T, V]

theorem purchased (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (ho : o ∈ J)
    (tickets : Insure J.card (mass k J) Q Credit.leanC) (A : ℝ) (hA : 0 ≤ A) :
    native Q hm D k J o A ≤ Q.cash (reserve G D k J o e) m * A^J.card :=
  common Q hm ho tickets A hA

/-- One simultaneous selection on the funded native Run. This applies to
all incoming marked vertices, including genuine nonsingleton masks. -/
theorem invoice (hG : G.Simple) (hJ : J ⊆ Z) (ho : o ∈ J) (hi : i ≤ e)
    (stock : ∀ᶠ m : ℕ in atTop, FundedMarkedWindingWindow.Window R J Z o D k e i r d c q w s m) :
    ∀ᶠ m : ℕ in atTop, ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
      ∀ N p, m < N → ∀ A : ℝ, ∀ X : Input Q hm Z k D A, 0 ≤ A →
        (∀ y, safeB (chartIn (loose Q.draws m) y (X.offsets y)) (X.familyAt y) Z e (w (Q.mint m hm).gear) A) →
        Award R Q hm J Z o s N p i r d c q X ∧ native Q hm D k J o A ≤
          (admittedCost R.family.path.levels m)^((reserve G D k J o e).d+1) * A^J.card := by
  filter_upwards [stock,FundedMarkedWindingWindow.credit R.family.path.levels hG (reserve G D k J o e)] with m sale cost
  obtain ⟨Q,hm,draws,paid,hy,closed,tickets,wind⟩ := sale
  refine ⟨Q,hm,draws,paid,?_⟩
  intro N p hN A X hA fine
  have y : Q.cash (reserve G D k J o e) m ≤ (admittedCost R.family.path.levels m)^((reserve G D k J o e).d+1) := by
    simpa only [Realm.cash,hy] using cost.2.2
  refine ⟨⟨?_,?_,wind N p hN X.familyAt X.offsets A hA (fun z => ⟨X.degree z,X.empty z,fine z⟩)⟩,
    (purchased (D:=D) Q hm ho tickets A hA).trans (mul_le_mul_of_nonneg_right y (pow_nonneg hA _))⟩
  · exact fun _ => rendering X hJ hA hN closed J.card le_rfl tickets o ho _ i (Nat.lt_succ_of_le hi)
  · exact fun _ _ => measured X hJ hA hN closed J.card le_rfl tickets o ho _ i (Nat.lt_succ_of_le hi) _

/-- The array in a selected joint lease emits the actual physical `Token`.
Summing its bare `coin` with the exponentially weighted actual `fall` over
every independent displacement, raw path, and invariant colour pays the
original fee. Root/support can be chosen independently of every test. -/
theorem tokens (O : Fin n → Orbit) (Y : Fin n → Dip)
    {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m} {A : ℝ}
    (X : Input Q hm Z k (NativeMarkedAddressTokens.axes O) A) (origin : Cover)
    (r : Fin (mass k J+i+1)) (L : Lease Q hm Z J X N i o origin r)
    (u : Side) (root : Frill J o × RadP G r.val → Site u)
    (support : Frill J o × RadP G r.val → Fin n → Support u) :
    let width := VestS J.card (mass k J) Q m hm
    let B := fun a : Frill J o × RadP G r.val => (packetH J (output X J N) (mass k J) (e+1) o origin a.1) i r a.2
    ∃ μ : (a : Frill J o × RadP G r.val) → Stationary.Ink G r.val → Measure (Sky (NativeMarkedAddressTokens.axes O)),
      (∀ a, Barn (B a) (μ a)) ∧
      SumBudget (fun a : Frill J o × RadP G r.val =>
        ∑ h,
          let T := NativeMarkedAddressTokens.token O J Y (B a) (μ a) h (toe J o origin a.1) o (root a) (support a)
          T.coin * Real.exp (width*T.fall))
        (NativeMarkedAddressTokens.cellPrice O J * native Q hm (NativeMarkedAddressTokens.axes O) k J o A) := by
  intro width B
  obtain ⟨μ,hμ,sum⟩ := L
  refine ⟨μ,hμ,?_⟩
  simp_rw [NativeMarkedAddressTokens.expense]
  have hC : 0 ≤ NativeMarkedAddressTokens.cellPrice O J := by
    unfold NativeMarkedAddressTokens.cellPrice; positivity
  exact cap_scale sum hC

end YM.Integration.OriginalBareMarkedInvoice
end
