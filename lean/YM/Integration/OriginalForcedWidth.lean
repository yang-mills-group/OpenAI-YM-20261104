import YM.Integration.OriginalForcedFlat
import YM.Integration.QLocalPhysicalBirthClock

/-! Price the original barcode footprint and the square-root renormalization
at the actual coarse coupling, including arbitrary polynomial Taylor bills. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalForcedWidth

open Filter Lattice Wilson WilsonStartup RG RG.Shoot Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum Pert.Asymptotics MatchingLedger.Compass.Income
open scoped Topology

variable {G : Gauge}

def factor (R : Run G) (m : ℕ) : ℝ :=
  let L := R.family.path.levels
  let γ := L.clock.forcedAllowance m
  2*(γ/Real.sqrt γ)*Push.Local.hitWidth (L.budget m)

theorem nonnegative (R : Run G) (m : ℕ) : 0 ≤ factor R m := by
  unfold factor
  have hw : 0 ≤ Push.Local.hitWidth (R.family.path.levels.budget m) := Nat.cast_nonneg _
  exact mul_nonneg (mul_nonneg (by norm_num) (div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _))) hw

/-- Simultaneously pay the full original footprint (2B+1)^4 and the
physical division by the square-root forced allowance. -/
theorem coefficient (R : Run G) (hG : G.Simple) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per : ℕ, m ≤ N →
      factor R m ≤ ε*regulatorRun R.family N per m^p := by
  let K : ℝ := 5^4*2^8
  have hK : 0 < K := by norm_num [K]
  let t := ε/(2*K)
  have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hK)
  filter_upwards [OriginalForcedFlat.allowance R hG (2*(p+16)) (sq_pos_of_pos ht)] with m hm N per hN
  let L := R.family.path.levels
  let β := (R.family.path.rep N per m).beta
  let γ := L.clock.forcedAllowance m
  let g := regulatorRun R.family N per m
  let w := Push.Local.hitWidth (L.budget m)
  have hw : 0 ≤ w := Nat.cast_nonneg _
  have hγ : 0 < γ := Real.exp_pos _
  have hg : 0 < g := Weather.runs_pos R.family R.makes hN per
  have hn : R.family.path.Conv N per m := R.makes.wilson.represents N per m hN
  have hβ : 0 < β := (div_pos (zero_lt_one.trans (L.fits.delayed m)) (by norm_num)).trans_le hn.band.1
  have hr : Real.sqrt γ ≤ t*g^(p+16) := by
    apply (Real.sqrt_le_left (mul_nonneg ht.le (pow_nonneg hg.le _))).2
    calc
      γ ≤ t^2*g^(2*(p+16)) := hm N per hN
      _ = (t*g^(p+16))^2 := by rw [mul_pow,← pow_mul,Nat.mul_comm (p+16) 2]
  have ha : L.clock.hatBeta m*g^2 ≤ 2 := by
    change L.clock.hatBeta m*((Real.sqrt β)⁻¹)^2 ≤ 2
    rw [inv_pow,Real.sq_sqrt hβ.le,← div_eq_mul_inv,div_le_iff₀ hβ]
    have hband : L.clock.hatBeta m/2 ≤ β := hn.band.1
    linarith
  have hwidth : w*g^16 ≤ K := by
    calc
      _ ≤ (5^4*(L.clock.hatBeta m)^8)*g^16 :=
        mul_le_mul_of_nonneg_right (QLocalPhysicalBirthClock.width L m) (pow_nonneg hg.le _)
      _ = 5^4*(L.clock.hatBeta m*g^2)^8 := by ring
      _ ≤ K := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (zero_lt_one.trans (L.fits.delayed m)).le
          (sq_nonneg g)) ha 8) (by norm_num)
  have hdiv : γ/Real.sqrt γ = Real.sqrt γ := (div_eq_iff (Real.sqrt_pos.2 hγ).ne').2
    (by nlinarith [Real.sq_sqrt hγ.le])
  change 2*(γ/Real.sqrt γ)*w ≤ ε*g^p
  rw [hdiv]
  calc
    _ ≤ 2*(t*g^(p+16))*w := mul_le_mul_of_nonneg_right (by linarith only [hr]) hw
    _ = 2*t*(w*g^16)*g^p := by rw [pow_add];ring
    _ ≤ 2*t*K*g^p := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwidth (by positivity)) (pow_nonneg hg.le _)
    _ = _ := by dsimp only [t]; field_simp [hK.ne']

/-- Include any actual Taylor invoice bounded by a prescribed inverse
power of the recorded coarse coupling. -/
theorem withStem (R : Run G) (hG : G.Simple) (p d : ℕ) {C ε : ℝ}
    (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ N per : ℕ, m ≤ N →
      ∀ v : ℝ, v ≤ C/(regulatorRun R.family N per m^d) →
        factor R m*v ≤ ε*regulatorRun R.family N per m^p := by
  filter_upwards [coefficient R hG (p+d) (div_pos hε hC)] with m hm N per hN v hv
  let g := regulatorRun R.family N per m
  have hg : 0 < g := Weather.runs_pos R.family R.makes hN per
  calc
    _ ≤ factor R m*(C/g^d) := mul_le_mul_of_nonneg_left hv (nonnegative R m)
    _ ≤ (ε/C*g^(p+d))*(C/g^d) := mul_le_mul_of_nonneg_right (hm N per hN) (by positivity)
    _ = _ := by change (ε/C*g^(p+d))*(C/g^d) = ε*g^p;rw [pow_add];field_simp [hC.ne',hg.ne']

end YM.Integration.OriginalForcedWidth
end
