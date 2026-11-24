import YM.Integration.WilsonReportHarvestReplayReach

/-! At a fixed earlier scale the separation test is bought after the physical
scale r is fixed and the ultraviolet cutoff tends to infinity. Both the
distance to the earlier scale and a finite cost fixed before the cutoff
can then be covered by the genuine later interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFixedOriginHousing
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato
open WilsonMeasuredAdmission WilsonReportHarvestSourceReach WilsonReportHarvestReplayReach
open scoped Topology
variable {G:Gauge}

theorem housing (R:Run G) (simple:G.Simple) {c t:ℝ} (cp:0 ≤ c) (tp:0 ≤ t) (E:ℕ) :
    ∀ᶠ m:ℕ in atTop,∀n:ℕ,n ≤ m→∀j:ℕ,∀mj:m ≤ j,m-n ≤ j-m→∀per:ℕ,
      let A:=R.family.path.levels
      let B:=(A.budget j).B
      required A c t E n m j*(4*B+2)+2*B ≤ (R.family.S.toDepth mj per).count.val*(A.budget m).B^2 := by
  filter_upwards [WilsonReportHarvestReplayReach.housing R simple cp tp (2*E) 0]
    with m booked n nm j mj mature per
  let A:=R.family.path.levels
  have grown : j-n+1 ≤ 2*(j-m+1) := by omega
  have length:E*(j-n+1) ≤ (2*E)*(j-m+1) :=
    (Nat.mul_le_mul_left E grown).trans_eq (by ring)
  have priced:required A c t E n m j ≤ required A c t (2*E) m m j := by
    unfold required depth
    apply Nat.add_le_add_left
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast length)
      (pow_nonneg (zero_lt_one.trans (mast_gt_one A j)).le _)
  exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ priced) _).trans
    (booked m le_rfl (by simp) j mj per)

theorem schedule (C:Family G) (n m:ℕ) (charge:ℝ) :
    ∀ᶠ j:ℕ in atTop,m ≤ j ∧ m-n ≤ j-m ∧ C.S.a n/C.S.a m ≤ C.S.a m/C.S.a j ∧
      charge ≤ C.S.a m/C.S.a j := by
  let M:=max (C.S.a n/C.S.a m) charge
  filter_upwards [eventually_ge_atTop (m+(m-n)+⌈M⌉₊)] with j late
  have mj:m ≤ j := by omega
  have room:⌈M⌉₊ ≤ j-m:=by omega
  have cash:M ≤ ((j-m:ℕ):ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast room)
  have tall:=RG05Readout.Many.tall (C:=C) m j mj
  have money:M ≤ C.S.a m/C.S.a j:=by
    rw [←mesh]
    change ((j-m:ℕ):ℝ) ≤ elapsed C.S m j at tall
    linarith only [cash,tall,Real.add_one_le_exp (elapsed C.S m j)]
  exact ⟨mj,by omega,(le_max_left _ _).trans money,(le_max_right _ _).trans money⟩

end YM.Integration.WilsonAllDateHarvestFixedOriginHousing
