import YM.Integration.FVA1Physical.Sources.Round2.StencilOrder
import YM.OPE.Therm.Request

/-! Polynomial fine-cutoff losses can be priced at the outgoing coupling on a
bounded window of a paid thermodynamic clock. -/

namespace YM.Integration.FVA1Physical.Round2

open Lattice RG Wilson OPE.Therm

theorem windowBeta {G : Gauge} (K : Levels G) (hP : Poetry K) (hG : G.Simple) (i s : ℕ) :
    K.clock.hatBeta (i + s) ≤ (1 + G.slopeConstant) ^ s * K.clock.hatBeta i := by
  have hb := (Gauge.slopeConstant_pos hG).le
  induction s with
  | zero => simp
  | succ s ih =>
    let j := i + s
    have ha := zero_le_one.trans (K.fits.delayed j).le
    have hlog : Real.log (K.S.block j).val ≤ K.clock.hatBeta j :=
      (Real.log_le_self (Nat.cast_nonneg _)).trans
        ((hP.stage j).track.trans (Real.log_le_self ha))
    have hh : K.clock.hatBeta (j + 1) = K.clock.hatBeta j + G.slopeConstant * Real.log (K.S.block j).val := by
      unfold Calendar.hatBeta
      rw [Schedule.scale_succ]
      ring
    change K.clock.hatBeta (j + 1) ≤ _
    rw [hh]
    calc
      _ ≤ K.clock.hatBeta j + G.slopeConstant * K.clock.hatBeta j :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hb)
      _ = (1 + G.slopeConstant) * K.clock.hatBeta j := by ring
      _ ≤ (1 + G.slopeConstant) * ((1 + G.slopeConstant) ^ s * K.clock.hatBeta i) :=
        mul_le_mul_of_nonneg_left ih (add_nonneg zero_le_one hb)
      _ = (1 + G.slopeConstant) ^ (s + 1) * K.clock.hatBeta i := by rw [pow_succ]; ring

theorem windowBeta_actual {G : Gauge} {H : History G} (hH : H.Selected)
    (hP : Poetry H.levels) (hG : G.Simple) {i N n W : ℕ} (hi : i ≤ N) (hw : N - i ≤ W) :
    H.levels.clock.hatBeta N ≤ ((1 + G.slopeConstant) ^ W * 2) * (H.rep N n i).beta := by
  have ha := (H.levels.fits.delayed i).le
  have hb : H.levels.clock.hatBeta i / 2 ≤ (H.rep N n i).beta := (hH.represents N n i hi).band.1
  have hbase : 1 ≤ 1 + G.slopeConstant := le_add_of_nonneg_right (Gauge.slopeConstant_pos hG).le
  have hh := windowBeta H.levels hP hG i (N - i)
  rw [Nat.add_sub_of_le hi] at hh
  exact hh.trans ((mul_le_mul (pow_le_pow_right₀ hbase hw) (show H.levels.clock.hatBeta i ≤
    2 * (H.rep N n i).beta by linarith only [hb]) (zero_le_one.trans ha)
    (pow_nonneg (zero_le_one.trans hbase) W)).trans_eq (mul_assoc ..).symm)

end YM.Integration.FVA1Physical.Round2
