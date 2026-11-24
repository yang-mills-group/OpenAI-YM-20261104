import YM.Integration.WilsonPositionProgramSubmittedWallet
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedRate
open scoped ENNReal
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
variable (D : XSpace.Run)

theorem absorption {A C : ℝ} (hA : 0<A) (hC : 0<C) (k q : ℕ) :
    ∀ᶠ n : ℕ in atTop, C*(A*Real.exp ((2+Real.log D.ratio)*(n:ℝ)))^k *
      (3*Real.exp (-(n:ℝ)^2*Real.log D.ratio/4)) ≤ (D.step n).spacing^q := by
  let l := Real.log (D.ratio:ℝ)
  let T := Real.log (3*C*A^k)
  let B := (k:ℝ)*(2+l)+(q:ℝ)*l
  have dr : 1<(D.ratio:ℝ) := by exact_mod_cast (show 1<D.ratio from (by decide : 1<3).trans_le D.large)
  have lp : 0<l := Real.log_pos dr
  have A' : 0<3*C*A^k := by positivity
  have hm : Tendsto (fun n:ℕ => (n:ℝ)*l/4) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const lp).atTop_div_const (by norm_num : (0:ℝ)<4)
  filter_upwards [hm.eventually_ge_atTop (|T|+B),eventually_ge_atTop 1] with n gain hn
  have n1 : 1≤(n:ℝ) := by exact_mod_cast hn
  have tg : T + B*(n:ℝ) ≤ (n:ℝ)^2*l/4 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr gain) (by positivity : 0≤(n:ℝ)),
      mul_nonneg (abs_nonneg T) (sub_nonneg.mpr n1), le_abs_self T]
  have floor : (D.step n).spacing^q = Real.exp (-(q:ℝ)*n*l) := by
    change (((D.ratio^n:ℕ):ℝ)⁻¹)^q=_
    have powEq : (D.ratio:ℝ)^n=Real.exp ((n:ℝ)*l) := by
      rw [←Real.rpow_natCast,Real.rpow_def_of_pos (zero_lt_one.trans dr)]; congr 1; dsimp [l];ring
    rw [Nat.cast_pow,powEq,←Real.exp_neg,←Real.exp_nat_mul]
    congr 1; ring
  rw [floor, mul_pow, ←Real.exp_nat_mul]
  calc _ = (3*C*A^k)*Real.exp ((k:ℝ)*((2+l)*(n:ℝ)) + (-(n:ℝ)^2*l/4)) := by
          rw [Real.exp_add];dsimp [l];ring
       _ = Real.exp (T+((k:ℝ)*((2+l)*(n:ℝ)) + (-(n:ℝ)^2*l/4))) := by
          conv_rhs => rw [Real.exp_add]
          dsimp only [T];rw [Real.exp_log A']
       _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [B] at tg; linarith)

variable {G : Gauge} (R : Run G) {X : Type} (simple : G.Simple)
variable (m j : X → ℕ) (w : X → ℕ → ℕ) (i : X → ℕ)
variable (blocks : ∀ x t, (R.family.S.block (m x+t)).val=D.ratio^(w x t))
variable (reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x)
variable (Z : ∀ P : RG.Patch, P.Branches R.family.path.levels.clock.kernel G) (F : Calibration.Tent j)
local notation "S" => WilsonPositionProgramInfraredCircuit.circuit R D m j w blocks
local notation "Q" => Rocket.wage S (Oracle.books R.family.path.levels.clock.kernel) Z F
  (WilsonPositionProgramSubmittedCoefficient.final j) (1/2:ℝ)
local notation "L" => WilsonPositionProgramInfraredMeter.wallet R D m j w i
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda R.family.path.levels

include simple blocks reach in
/-- The complete native finite-regulator bill beats every fixed power of the enrolled
spacing on the same signed experiment, uniformly over its original source placements. -/
theorem original {f : X → ℝ≥0∞} (H : ℝ) (paid : Carry (L H) Q f) (q : ℕ) :
    ∃ threshold : ℕ, ∀x, threshold ≤ i x → 1≤β (m x) → Λ (m x)≤(i x:ℝ)*Real.log D.ratio →
      f x ≤ ENNReal.ofReal ((D.step (i x)).spacing^q) := by
  obtain ⟨aux,⟨C,k,finite,bound⟩,cash⟩ := paid
  obtain ⟨A,Apos,wallet⟩ := WilsonPositionProgramSubmittedWallet.amount R D simple m j w i blocks reach H
  have cpos : 0<C.toReal+1 := by linarith [ENNReal.toReal_nonneg (a:=C)]
  obtain ⟨threshold,lower⟩ := eventually_atTop.mp (absorption D Apos cpos k q)
  refine ⟨threshold,fun x hx old age => ?_⟩
  have cap : C≤ENNReal.ofReal (C.toReal+1) := by
    calc _ = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal finite).symm
         _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  have wcap := ENNReal.ofReal_le_ofReal (wallet x old age)
  have wc := WilsonPositionProgramSubmittedPeriod.wage D R m j w blocks Z F i reach x
  have er := lower (i x) hx
  let amt := A*Real.exp ((2+Real.log D.ratio)*(i x:ℝ))
  let per := 3*Real.exp (-(i x:ℝ)^2*Real.log D.ratio/4)
  have a0 : 0≤amt := by dsimp [amt];positivity
  calc f x ≤ aux x * Q x := cash x
       _ ≤ (C * ((L H).val x)^k)*Q x := mul_le_mul' (bound x) le_rfl
       _ ≤ (ENNReal.ofReal (C.toReal+1)*(ENNReal.ofReal amt)^k)*ENNReal.ofReal per :=
          mul_le_mul' (mul_le_mul' cap (pow_le_pow_left' wcap k)) wc
       _ = ENNReal.ofReal ((C.toReal+1)*amt^k*per) := by
          rw [ENNReal.ofReal_mul (mul_nonneg cpos.le (pow_nonneg a0 _)),
            ENNReal.ofReal_mul cpos.le,ENNReal.ofReal_pow a0]
       _ ≤ _ := ENNReal.ofReal_le_ofReal er

end YM.Integration.WilsonPositionProgramSubmittedRate
