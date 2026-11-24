import YM.Integration.WilsonConditionalTaylorThreshold

/-! The actual block index funds every finite Taylor request on one selector.
After the lower height is fixed, one invoice covers all periods and cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorCalendar

open Filter Finset RG Precision RG.Supply Input Org PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato Push.PriceCompiler WilsonConditionalTaylorThreshold
open WilsonLimitConstruction.FundedCompanySelection
open scoped Classical BigOperators Topology

variable {G : Gauge} {ι : Type} [Encodable ι]

private def row (f : ι → MapPrices → Fare) (k : ℕ) : MapPrices → Fare :=
  match Encodable.decode (α := ι) k with
  | some i => f i
  | none => fun _ _ _ _ _ => 0

/-- At physical scale `P.J` buy the first `P.J+1` requests. Every input to
each term is fixed before the period and the source fields are chosen. -/
def atlas (f : ι → MapPrices → Fare) : MapPrices → Fare :=
  fun M H H' P K => ∑ k ∈ range (P.J+1), max 0 (row f k M H H' P K)

theorem covered (f : ι → MapPrices → Fare) (i : ι) (M : MapPrices) (H H' : Stage)
    (P : Patch) (K : KernelChoices) (hi : Encodable.encode i ≤ P.J) :
    f i M H H' P K ≤ atlas f M H H' P K := by
  have seen : row f (Encodable.encode i) = f i := by simp [row]
  rw [←seen]
  exact (le_max_right _ _).trans (Finset.single_le_sum (fun k _ => le_max_left 0
    (row f k M H H' P K)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))

/-- Reading one already bought request does not reselect its trajectory,
delay, cutoff, period, or background. The late height can depend on the request. -/
theorem read (R : Run G) (f : ι → MapPrices → Fare) (fund : Paid (atlas f) R.kit)
    (i : ι) : ∀ᶠ j : ℕ in atTop, ∀ n, f i R.metals.K (R.family.path.levels.params j)
      (R.family.path.levels.params (j+1)) (R.family.path.levels.clock.op j n).patch
      (R.family.path.levels.clock.op j n).kernel ≤ R.family.path.levels.clock.hatBeta j := by
  filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop (Encodable.encode i)] with j late n
  apply (covered f i _ _ _ _ _ ?_).trans (fund j n)
  exact late.trans (R.alloy.B.a.fits.mono (Nat.le_succ j))

/-- The countable cofinal loss menu lies strictly below every positive
coupling-order exponent, including the vacuum order zero. -/
def loss (i : ℕ) : ℝ := 1 / ((i:ℝ)+2)

theorem loss_pos (i : ℕ) : 0 < loss i := by unfold loss; positivity

theorem loss_small (i p : ℕ) : loss i < (p:ℝ)+1 := by
  unfold loss
  exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) i]) |>.trans_le
    (le_add_of_nonneg_left (Nat.cast_nonneg (α:=ℝ) p))

theorem cofinal {η : ℝ} (hη : 0 < η) : ∃ i : ℕ, loss i ≤ η := by
  obtain ⟨i, hi⟩ := exists_nat_gt (η⁻¹)
  refine ⟨i, (div_le_iff₀ (by positivity : 0 < (i:ℝ)+2)).mpr ?_⟩
  have h : η⁻¹ ≤ (i:ℝ)+2 := by linarith
  simpa [hη.ne'] using mul_le_mul_of_nonneg_left h hη.le

end YM.Integration.WilsonConditionalTaylorCalendar
end

