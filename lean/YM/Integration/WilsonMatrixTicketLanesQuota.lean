import YM.Next.RANK.Insiders
import YM.OPE.Log.Measuring

/-! The ultraviolet charge and the two comparisons on the original family,
projection and one fixed ultrafilter. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesQuota
open Filter RG Next.Rank Next.Rank.Price
open scoped Topology
variable {G : Gauge} {C : Family G} {S : Table C.book}

/-- The scale already present in the finite column price recovers the
physical quota on that very cutoff and microscopic label. -/
theorem quota {d : ℕ} (x : C.label d) (k N p : ℕ) :
    Spindle.paid C d k N p x * C.S.a k ^ d = Next.UVStress.quota C d k N p x := by
  rw [Spindle.paid, Price.awake, Extra.Histories.Size.smul, norm_inv, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (C.S.a_pos _).le]
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀, one_mul]
  · rfl
  exact pow_ne_zero _ (C.S.a_pos _).ne'

/-- A nonempty refinement of a fixed ultrafilter has the same eventual
physical bound. Its recovered representative gives the required convergent
constant sequence on this fixed filter. -/
theorem inlet (U : Ultrafilter (ℕ × ℕ)) {d k p : ℕ} (x : C.label d)
    (price : ∃ f : Filter (ℕ × ℕ), f.NeBot ∧ f ≤ (U : Filter (ℕ × ℕ)) ∧ ∃ y : C.label d,
      S.project d y = S.project d x ∧
      ∀ᶠ i in f, Spindle.paid C d k i.1 i.2 y * C.S.a k ^ d ≤ C.path.levels.clock.hatBeta k ^ p) :
    ∃ (y : C.label d) (q : ℕ × ℕ → C.label d), S.project d y = S.project d x ∧
      Tendsto q (U : Filter (ℕ × ℕ)) (𝓝 y) ∧ ∀ᶠ i in (U : Filter (ℕ × ℕ)),
      Next.UVStress.quota C d k i.1 i.2 (q i) ≤ C.path.levels.clock.hatBeta k ^ p := by
  obtain ⟨f,nonempty,refines,y,project,charge⟩ := price
  rw [U.unique refines nonempty] at charge
  refine ⟨y,fun _ => y,project,tendsto_const_nhds,?_⟩
  filter_upwards [charge] with i hi
  rwa [quota] at hi

/-- The positive lattice scale lets the retained outlet use the published
divided charge even when the row's scalar bound was supplied separately. -/
theorem outlet {d w k p : ℕ} {norm z : ℝ}
    (bound : norm * C.S.a k ^ (d-w) ≤ C.path.levels.clock.hatBeta k ^ p * z) :
    norm ≤ C.path.levels.clock.hatBeta k ^ p / C.S.a k ^ (d-w) * z := by
  calc
    norm ≤ (C.path.levels.clock.hatBeta k ^ p * z) / C.S.a k ^ (d-w) :=
      (le_div_iff₀ (pow_pos (C.S.a_pos k) _)).2 bound
    _ = _ := by ring

end YM.Integration.WilsonMatrixTicketLanesQuota
