import YM.RG04B.Request
import YM.RG04B.Scales

/-!
# Allocating the per-stage floors and post-ratio costs

For the UV consumer at arbitrary fixed finite orders. Clients group their known
pre-L, post-L costs in one `Fees`, fixed before shots (can demand e.g. neighbor
searches in each argument and prescribes every finite index, `e` standing for
an entire finite request: marker, derivative, horizon, Taylor setup...). Then
on the `Booked` path get a stage-synchronous subpower of L payment and the
O(z_i^θ) individual bound on post-block costs (even constants e.g. exponents
in geometry polynomials), for any fixed θ>0. Issuable through chooseOnce,
not on all C.Makes. Need to prove input costs really fit -- not reading them
off that C! When using e.g. fixed shrink eps across stages include any desired
powers/reciprocal rates here. Neighbor costs can include/look over all
anticipated `StepStages` in these tallies. Booking can and often should
combine many additional requests before shooting. Don't repick after e fixed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG04B
open Function Filter Lattice Wilson RG Real
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (hG : G.Simple)

/-- Arbitrary pre-L and post-theta fees (abs values counted). Arguments `e` (request id),
`j` (stage). -/
structure Fees where
  first : Pre (ℕ → ℕ → ℝ)
  paid : Post (ℕ → ℕ → ℝ)

private def buyPre (T : Fees) : Pre (ℕ → ℕ) := fun k S j =>
  (Finset.range (j+1)).sup fun e => Nat.ceil ((2+|T.first k S e j|) ^ (j+1))

private def after (T : Fees) : Post (ℕ → ℝ → Prop) := fun k S L θ j x =>
  Real.exp 1 ≤ x ∧ (L j).val ≤ ySize x ∧
    ∀ e : ℕ, e ≤ j → (2+|T.paid k S L θ e j|) ^ (j+1) ≤ ySize x

lemma eventually_after (T : Fees) (k S L θ j) : ∀ᶠ x in atTop, after T k S L θ j x := by
  refine (eventually_ge_atTop _).and ((geoEnd.eventually_ge_atTop _).and ?_)
  filter_upwards [(Finset.range (j+1)).eventually_all.mpr fun e _ =>
    geoEnd.eventually_ge_atTop ((2+|T.paid k S L θ e j|)^(j+1))] with x hx e he
  exact hx e (Finset.mem_range.mpr (Nat.lt_succ_of_le he))

def Fees.reserve (T : Fees) : Request :=
  { Request.none with preLength := buyPre T, hat := after T, eventualHat := eventually_after T }

-- readability for clients

def firstBill (T : Fees) (a : Levels G) (e m : ℕ) :=
  2+abs (T.first a.clock.kernel a.clock.stage e (a.clock.J (m+1)))
def finalBill (T : Fees) (a : Levels G) (e m : ℕ) :=
  2+abs (T.paid a.clock.kernel a.clock.stage a.clock.factor a.clock.theta e (a.clock.J (m+1)))
def stripe (T : Fees) (a : Levels G) := Booked T.reserve a

lemma atLeastOne (T : Fees) (a : Levels G) (e m : ℕ) :
    1 ≤ firstBill T a e m ∧ 1 ≤ finalBill T a e m :=
  ⟨le_trans one_le_two (le_add_of_nonneg_right (abs_nonneg _)),
    le_trans one_le_two (le_add_of_nonneg_right (abs_nonneg _))⟩

variable {T : Fees} {a : Levels G}
lemma limitRatio (h : stripe T a) (m : ℕ) : ratio a m ≤ geo a m := by
  rw [ratio,← a.fits.sameFactor m]; exact (h.hats m).2.1
lemma hat_limit (h : stripe T a) (m : ℕ) : Real.exp 1 ≤ a.clock.hatBeta m := (h.hats m).1
lemma spendingPre (h : stripe T a) (e m : ℕ) (he : e ≤ a.clock.J (m+1)) :
    firstBill T a e m ^ (a.clock.J (m+1)+1) ≤ ratio a m := by
  let k : ℕ := a.clock.J (m+1)
  have hi : Nat.ceil (firstBill T a e m ^ (k+1)) ≤ (a.clock.factor k).val :=
    Nat.le_trans (Finset.le_sup (s:=Finset.range (k+1))
      (f:=fun e => Nat.ceil (firstBill T a e m ^ (k+1))) (Finset.mem_range.mpr (Nat.lt_succ_of_le he)))
      (h.pre k)
  rw [ratio,← a.fits.sameFactor m]; exact (Nat.ceil_le).mp hi

lemma spendingPost (h : stripe T a) (e m : ℕ) (he : e ≤ a.clock.J (m+1)) :
    finalBill T a e m ^ (a.clock.J (m+1)+1) ≤ geo a m :=
  (h.hats m).2.2 _ he

private lemma meet_power (x y : ℝ) (n : ℕ) (ε : ℝ) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (he : 1 ≤ ε*n) (h : x^n ≤ y) : x ≤ y^ε :=
  calc
    x = x^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ x^(ε*n) := Real.rpow_le_rpow_of_exponent_le hx he
    _ = (x^n)^ε := by rw [mul_comm ε, Real.rpow_mul (zero_le_one.trans hx),Real.rpow_natCast]
    _ ≤ _ := Real.rpow_le_rpow (zero_le_one.trans (one_le_pow₀ hx)) h hε

/-- Both payments uniform tail. Includes inter-plateau steps. -/
lemma common (h : stripe T a) (e : ℕ) {ε : ℝ} (he : 0 < ε) : ∀ᶠ i in atTop,
    firstBill T a e i ≤ (ratio a i)^ε ∧ finalBill T a e i ≤ (geo a i)^ε := by
  have ht : Tendsto (fun i : ℕ => a.clock.J (i+1)) atTop atTop := a.fits.deep.comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun i : ℕ => a.clock.J (i+1) + 1) atTop atTop := (tendsto_add_atTop_nat 1).comp ht
  have hv := Tendsto.const_mul_atTop he (tendsto_natCast_atTop_atTop.comp hr)
  filter_upwards [ht.eventually_ge_atTop e,hv.eventually_ge_atTop 1] with i hp hj
  exact ⟨meet_power _ _ _ _ (atLeastOne ..).1 he.le hj (spendingPre h e i hp),
    meet_power _ _ _ _ (atLeastOne ..).2 he.le hj (spendingPost h e i hp)⟩
end YM.RG04B
