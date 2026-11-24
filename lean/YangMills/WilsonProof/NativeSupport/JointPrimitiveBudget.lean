import YangMills.WilsonProof.NativeSupport.JointPolynomialCalendar
import YangMills.WilsonProof.NativeSupport.JointDatedNames
import YangMills.WilsonProof.NativeSupport.JointForcedClock
import YangMills.WilsonProof.NativeSupport.JointSkyScale

/-! Actual site multiplicities, closure reserve size, and original
blocking penalty all fit the fixed cutoff powers. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open RG Lattice Wilson RGComparison.Core16 Extra.Multi
open scoped Classical BigOperators
theorem site_budgets (x:ℝ) (B:ℕ) (hot:256 ≤ x) (box:(B:ℝ) ≤ 2*x^2) :
    siteFactor B ≤ x^13 ∧ ((B+B+1:ℕ):ℝ)^4 ≤ x^13 := by
  have x1:1 ≤ x:=by linarith
  have xp:=zero_lt_one.trans_le x1
  have wide:2*(16*(B:ℝ)+9) ≤ x^3 := by
    calc
      2*(16*(B:ℝ)+9) ≤ 82*x^2 := by linarith only [box,one_le_pow₀ (n:=2) x1]
      _ ≤ x*x^2 := by gcongr;linarith
      _ = x^3 := by ring
  have power:(x^3)^4 ≤ x^13 := by
    rw [←pow_mul];apply pow_le_pow_right₀ x1;decide
  constructor
  · unfold siteFactor
    calc
      Real.exp 1*(2*(16*(B:ℝ)+9))^4 ≤ x*(x^3)^4 := by gcongr;exact Real.exp_one_lt_three.le.trans (by linarith)
      _ = x^13 := by ring
  · apply le_trans _ power
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 4
    push_cast
    have bb:0 ≤ (B:ℝ):=Nat.cast_nonneg _
    linarith only [wide,bb]

def fullMultiplicity (m days block:ℕ) := (m+2*days*(block^4*4))*4
theorem multiplicity_budget (m W days block:ℕ) (x:ℝ) (heat:1 ≤ x) (bill:64*((m:ℝ)+W+1) ≤ x)
    (duration:(days:ℝ) ≤ W*x) (diam:(block:ℝ) ≤ x^W) : (fullMultiplicity m days block:ℝ) ≤ x^(4*W+2) := by
  have x0:=zero_le_one.trans heat
  have p:(block:ℝ)^4 ≤ x^(4*W):=by rw [Nat.mul_comm 4 W,pow_mul];exact pow_le_pow_left₀ (Nat.cast_nonneg _) diam _
  have big:1 ≤ x*x^(4*W):=one_le_mul_of_one_le_of_one_le heat (one_le_pow₀ heat)
  unfold fullMultiplicity
  push_cast
  calc
    _ ≤ ((m:ℝ)+2*((W:ℝ)*x)*(x^(4*W)*4))*4 := by gcongr
    _ ≤ (4*(m:ℝ)+32*(W:ℝ))*(x*x^(4*W)) := by
      nlinarith only [mul_le_mul_of_nonneg_left big (Nat.cast_nonneg m)]
    _ ≤ x*(x*x^(4*W)) := by gcongr;linarith only [bill,(Nat.cast_nonneg m : (0:ℝ) ≤ m),(Nat.cast_nonneg W : (0:ℝ) ≤ W)]
    _ = x^(4*W+2) := by rw [pow_add];ring

theorem forced_budget (d:ℕ) (x b Γ:ℝ) (heat:16 ≤ x) (b0:0 < b) (ceiling:x ≤ 2*b)
    (stain:Real.sqrt Γ ≤ (2/b)^(2*d)) : Γ ≤ 1/x^d ∧ Real.sqrt Γ ≤ 1 := by
  have xp:0 < x:=by linarith
  have x1:1 ≤ x:=by linarith
  have ratio:2/b ≤ 4/x:=(div_le_div_iff₀ b0 xp).mpr (by linarith)
  have square:(4/x)^2 ≤ 1/x := by
    rw [div_pow,div_le_div_iff₀ (sq_pos_of_pos xp) xp]
    nlinarith only [mul_nonneg xp.le (sub_nonneg.mpr heat)]
  have faint:Real.sqrt Γ ≤ 1/x^d := by
    apply stain.trans
    rw [pow_mul]
    calc
      ((2/b)^2)^d ≤ ((4/x)^2)^d := by gcongr
      _ ≤ (1/x)^d := pow_le_pow_left₀ (sq_nonneg _) square _
      _ = _ := by rw [div_pow,one_pow]
  have disk:1/x^d ≤ 1 := (div_le_one (pow_pos xp _)).mpr (one_le_pow₀ x1)
  have st:=faint.trans disk
  constructor
  · by_cases non:0 ≤ Γ
    · calc
        Γ=(Real.sqrt Γ)^2 := (Real.sq_sqrt non).symm
        _ ≤ Real.sqrt Γ := by nlinarith only [mul_nonneg (Real.sqrt_nonneg Γ) (sub_nonneg.mpr st)]
        _ ≤ _ := faint
    · exact (le_of_not_ge non).trans (by positivity)
  · exact st

end YM.Integration.InletSusceptibility.Packet
