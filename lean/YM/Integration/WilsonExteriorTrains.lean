import YM.Integration.WilsonExteriorSeparation

/-! The exact native even-cell translates of arbitrary physical positions.
The coarse gap is fixed before the replica count; only the subsequent train,
period, and fine-mesh tails depend on that count. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonExteriorTrains

open Function Filter Set Lattice Cells Extraction StressFlux.Matching
open WilsonExteriorSeparation
open scoped Topology Classical

variable {G : Gauge} (C : Family G) {f : Extraction.Order}

def train (b t j : ℕ) (x : E4) : E4 :=
  x + C.S.gridPoint b (Work.B15.diag t j)

/-- The physical translate is exactly the existing Episode train step at
any compatible comparison grid. -/
theorem train_eq_episode {b k : ℕ} (e : b ≤ k) (t j : ℕ) (x : E4) :
    train C b t j x = x + C.S.gridPoint k (Bid.Episode.step C e t j) := by
  apply PiLp.ext
  intro a
  have hs := C.S.embeds_scale (C.S.toDepth e 0)
  dsimp [train, Schedule.gridPoint, Work.B15.diag, Bid.Episode.step]
  push_cast
  rw [← hs]
  ring

/-- Literal finite-cutoff placements use that same native train step. -/
theorem ceilSite_train {b k N p : ℕ} (e : b ≤ k) (hk : k ≤ N)
    (t j : ℕ) (x : E4) :
    ceilSite C N p (train C b t j x) =
      ceilSite C N p x + location C.S k N p (Bid.Episode.step C e t j) := by
  rw [train_eq_episode C e t j x]
  exact WilsonExteriorGeometry.ceilSite_add_grid hk x _

private theorem train_gap_lt (b : ℕ) (x y : E4) {i j : ℕ} (hij : i < j) :
    ∀ᶠ t : ℕ in atTop,
      C.S.a b < |train C b t i x 0 - train C b t j y 0| := by
  let c := C.S.a b * (2 * ((j : ℝ) - i))
  have hc : 0 < c := mul_pos (C.S.a_pos b)
    (mul_pos (by norm_num) (sub_pos.mpr (by exact_mod_cast hij)))
  have ht : Tendsto (fun t : ℕ => (t : ℝ) * c) atTop atTop :=
    Tendsto.atTop_mul_const hc (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually_gt_atTop (C.S.a b + x 0 - y 0)] with t ht
  have he : train C b t j y 0 - train C b t i x 0 =
      y 0 - x 0 + (t : ℝ) * c := by
    dsimp [train, Schedule.gridPoint, Work.B15.diag, c]
    push_cast
    ring
  rw [abs_sub_comm]
  exact lt_of_lt_of_le (by rw [he]; linarith) (le_abs_self _)

theorem train_gap (b : ℕ) (x y : E4) {i j : ℕ} (hij : i ≠ j) :
    ∀ᶠ t : ℕ in atTop,
      ∃ a : Axis, C.S.a b < |train C b t i x a - train C b t j y a| := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (train_gap_lt C b x y h).mono fun t ht => ⟨0, ht⟩
  · exact (train_gap_lt C b y x h).mono fun t ht =>
      ⟨0, by rwa [abs_sub_comm]⟩

theorem train_coordinate_gaps {I : Type} [Fintype I] (b m : ℕ) (x : I → E4)
    (hx : ∀ i j, i ≠ j → ∃ a : Axis, C.S.a b < |x i a - x j a|) :
    ∀ᶠ t : ℕ in atTop, ∀ q r : Fin m × I, q ≠ r →
      ∃ a : Axis, C.S.a b <
        |train C b t q.1 (x q.2) a - train C b t r.1 (x r.2) a| := by
  refine eventually_all.mpr fun q => eventually_all.mpr fun r =>
    eventually_all.mpr fun hqr => ?_
  rcases q with ⟨q, i⟩
  rcases r with ⟨r, j⟩
  by_cases h : q = r
  · subst r
    have hij : i ≠ j := fun hij => hqr (by rw [hij])
    obtain ⟨a, ha⟩ := hx i j hij
    exact Eventually.of_forall fun t => ⟨a, by
      simpa only [train, PiLp.add_apply, add_sub_add_right_eq_sub] using ha⟩
  · exact train_gap C b (x i) (x j) (Fin.val_injective.ne h)

/-- All actual wrapped train sites are separated at the same preselected
coarse level; no generic-coordinate or aligned-point condition is needed. -/
theorem literal_trains_apart {I : Type} [Fintype I] (b m : ℕ) (x : I → E4)
    (hx : ∀ i j, i ≠ j → ∃ a : Axis, C.S.a b < |x i a - x j a|) :
    ∀ᶠ t : ℕ in atTop, ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ hb : b ≤ z.1,
      ∀ q r : Fin m × I, q ≠ r → span C.S hb z.2 <
        separation (ceilSite C z.1 z.2 (train C b t q.1 (x q.2)))
          (ceilSite C z.1 z.2 (train C b t r.1 (x r.2))) :=
  (train_coordinate_gaps C b m x hx).mono fun t ht =>
    ceilSites_apart C b (fun q : Fin m × I => train C b t q.1 (x q.2)) ht

/-- The geometry scale is selected using only one separated physical copy,
before the number of replicas is supplied. -/
theorem some_scale_trains_apart {I : Type} [Fintype I]
    (x : I → E4) (hx : Injective x) :
    ∀ᶠ b : ℕ in atTop, ∀ m : ℕ, ∀ᶠ t : ℕ in atTop,
      ∀ᶠ z : ℕ × ℕ in f.fuse, ∀ hb : b ≤ z.1,
      ∀ q r : Fin m × I, q ≠ r → span C.S hb z.2 <
        separation (ceilSite C z.1 z.2 (train C b t q.1 (x q.2)))
          (ceilSite C z.1 z.2 (train C b t r.1 (x r.2))) :=
  (eventual_coordinate_gaps C x hx).mono fun b hb m =>
    literal_trains_apart C b m x hb

/-- The complete product of the original physical representatives uses the
same finite-cutoff translation as the native Episode. -/
theorem product_train {S : Table C.book} {I : Type} [Fintype I] {d : I → ℕ}
    {b k N p : ℕ} (e : b ≤ k) (hk : k ≤ N) (x : I → E4)
    (v : OPE.Orbits.Labels S d) (t j : ℕ) :
    WilsonWholeLimit.product (fun i => train C b t j (x i)) v N p =
      WilsonWholeLimit.product x v N p ∘
        translate (location C.S k N p (Bid.Episode.step C e t j)) := by
  simpa only [train_eq_episode C e t j] using
    (WilsonExteriorGeometry.product_add_grid hk x v (Bid.Episode.step C e t j))

end YM.Integration.WilsonExteriorTrains
