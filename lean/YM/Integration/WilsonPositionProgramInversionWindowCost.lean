import YM.Integration.WilsonPositionProgramDatedFieldCost
import YM.Integration.WilsonPositionProgramReporterBand
import YM.Integration.WilsonPositionProgramSubmittedRate

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

namespace YM.Integration.WilsonPositionProgramInversionWindowCost
open Filter Lattice RG PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open scoped Topology
variable {G : Gauge} (R : Run G) (D : XSpace.Run)

theorem count (S : Schedule) (m k : ℕ) : (k:ℝ)*Real.log 3 ≤ S.scale (m+k)-S.scale m := by
  induction k with
  | zero => simp
  | succ t ih =>
    rw [Nat.cast_succ,add_mul,one_mul,show m+(t+1)=m+t+1 by omega,Schedule.scale_succ]
    have le : (3:ℝ)≤((S.block (m+t)).val:ℝ) := by exact_mod_cast S.block_large (m+t)
    linarith [Real.log_le_log (by norm_num : (0:ℝ)<3) le]

def factor : ℝ := 2+(Real.log 3)⁻¹

theorem bounds (simple : G.Simple) {s : ℕ} (B : WilsonPositionProgramReporterBand.Band R D s) :
    let L := R.family.path.levels
    ∀ᶠ t : ℕ in atTop, let m := B.reporter+t
    let M := m+B.upper t
    let w := (D.step (B.index t)).spacing
    0≤zz L m ∧ zz L m ≤ w⁻¹ ∧ 0≤Compar L.S (zz L) m M ∧
      Compar L.S (zz L) m M ≤ factor * w⁻¹ := by
  intro L
  have ages : Tendsto (fun t:ℕ => B.reporter+t) atTop atTop :=
    tendsto_atTop_mono (fun t => Nat.le_add_left t B.reporter) tendsto_id
  filter_upwards [((RG05Readout.lambda_growth simple L).comp ages).eventually_ge_atTop 3] with t large
  intro m M w
  have scale : Real.log w= -((B.index t:ℝ)*Real.log D.ratio) := by
    change Real.log (((D.den (B.index t):ℕ):ℝ)⁻¹)=_
    simp [XSpace.Run.den,Real.log_pow]
  have gap : L.S.scale M-L.S.scale m = -Real.log w := by
    dsimp only [m,M,w]
    rw [←B.spacing t,Real.log_div (R.family.S.a_pos _).ne' (R.family.S.a_pos _).ne']
    simp only [Schedule.scale,Real.log_inv]
    ring
  have grow : (B.upper t:ℝ)*Real.log 3 ≤ -Real.log w := gap ▸ count L.S m (B.upper t)
  have logpos := Real.log_pos (by norm_num : (1:ℝ)<3)
  have small : (B.upper t:ℝ) ≤ (Real.log 3)⁻¹ * (-Real.log w) := by
    rw [mul_comm,←div_eq_mul_inv]
    exact (le_div_iff₀ logpos).mpr grow
  have young : (3:ℝ) ≤ RG16.Lambda L m := large
  have lb : 1≤Real.log (L.clock.hatBeta m) := by dsimp [RG16.Lambda] at young; linarith
  have non := Real.log_nonneg lb
  have z0 : 0≤zz L m := by dsimp [zz]; linarith
  have z1 : zz L m ≤ -Real.log w := by
    calc zz L m ≤ RG16.Lambda L m := by
          dsimp [zz,RG16.Lambda]
          linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one lb)]
      _ ≤ (RG16.Lambda L m)^((3:ℝ)/2) := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤RG16.Lambda L m by linarith)
            (by norm_num : (1:ℝ)≤3/2)
      _ ≤ -Real.log w := by rw [scale,neg_neg]; exact B.floor t
  have posw : 0 < w := (D.step (B.index t)).positive
  have cap : -Real.log w ≤ w⁻¹ := by
    rw [←Real.log_inv]
    linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr posw)]
  change 0≤zz L m ∧ zz L m ≤ w⁻¹ ∧ 0≤zz L m+(L.S.scale M-L.S.scale m)+(M-m:ℕ) ∧ _
  rw [gap, show M-m=B.upper t by dsimp only [M];omega]
  refine ⟨z0,z1.trans cap,by have hx:=z0.trans z1; positivity,?_⟩
  change zz L m + (L.S.scale M-L.S.scale m)+(M-m:ℕ) ≤ _
  rw [gap,show M-m=B.upper t by dsimp only [M];omega]
  dsimp only [factor]
  have h := small.trans (mul_le_mul_of_nonneg_left cap (inv_pos.mpr logpos).le)
  linarith

theorem original (simple : G.Simple) {s : ℕ} (E : WilsonPositionProgramReporterBand.Band R D s)
    (C B : Credit) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ t : ℕ in atTop, let m := E.reporter+t
    let M := m+E.upper t
    let w := (D.step (E.index t)).spacing
    C.buy (Compar R.family.S (zz R.family.path.levels) m M) * B.buy (zz R.family.path.levels m) ≤
      K*(w⁻¹)^(C.d+B.d) := by
  let K := C.x*factor^C.d*B.x
  have fpos : 0≤factor := by dsimp [factor]; positivity
  have cp : 0≤C.x := zero_le_one.trans C.good
  have bp : 0≤B.x := zero_le_one.trans B.good
  refine ⟨K,mul_nonneg (mul_nonneg cp (pow_nonneg fpos _)) bp,?_⟩
  filter_upwards [bounds R D simple E] with t bounds'
  obtain ⟨z0,z1,c0,c1⟩ := bounds'
  intro m M w
  have left := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ c0 c1 C.d) cp
  have right := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ z0 z1 B.d) bp
  refine (mul_le_mul left right (mul_nonneg bp (pow_nonneg z0 _))
    (mul_nonneg cp (pow_nonneg (c0.trans c1) _))).trans_eq ?_
  dsimp only [K]
  rw [mul_pow,pow_add]
  ring

end YM.Integration.WilsonPositionProgramInversionWindowCost
end
