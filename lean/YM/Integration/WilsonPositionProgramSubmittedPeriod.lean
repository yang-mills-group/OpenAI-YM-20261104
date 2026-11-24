import YM.Integration.WilsonPositionProgramSubmittedCoefficient
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Filter
namespace YM.Integration.WilsonPositionProgramSubmittedPeriod
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.FVAAlt2 RegulatorIR.Uniform
open OPE OPE.Owl Precision
variable (D : XSpace.Run)

theorem side (i : ℕ) : ((D.step i).p.side.val : ℝ) =
    (D.finalSide.side.val:ℝ)*(D.ratio:ℝ)^(i+D.reserve*i*i) := by
  change ((D.finalSide.side.val*D.ratio^(i+D.reserve*i*i):ℕ):ℝ) = _
  push_cast
  rfl

private theorem log_lower (i : ℕ) :
    (i:ℝ)^2*Real.log D.ratio ≤ Real.log ((D.ratio:ℝ)^(i+D.reserve*i*i)) := by
  have big : 1 < (D.ratio:ℝ) := by exact_mod_cast (show 1<D.ratio from (by decide : 1<3).trans_le D.large)
  rw [Real.log_pow]
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg big.le)
  exact_mod_cast (show i^2 ≤ i+D.reserve*i*i by
    simpa [Nat.pow_two] using (Nat.mul_le_mul_right i (Nat.le_mul_of_pos_left i D.spare)).trans
      (Nat.le_add_left (D.reserve*i*i) i))

variable {G : Gauge} (C : Run G) {X : Type}
variable (m j : X → ℕ) (w : X → ℕ → ℕ) (blocks : ∀ x t, (C.family.S.block (m x+t)).val=D.ratio^(w x t))
local notation "S" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "Gains" => Oracle.books C.family.path.levels.clock.kernel
local notation "ending" => WilsonPositionProgramSubmittedCoefficient.final j

/-- On the actual path down to the fixed-side auxiliary stop, each of the three infrared errors
decays exponentially in the square of the independently enrolled fine date. -/
theorem wage (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (F : Calibration.Tent j) (i : X → ℕ)
    (reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x) (x : X) :
    Rocket.wage S Gains Z F ending (1/2:ℝ) x ≤
      ENNReal.ofReal (3*Real.exp (-(i x:ℝ)^2*Real.log D.ratio/4)) := by
  have top := WilsonPositionProgramInfraredCircuit.fine D j w (x:=x) (i:=i x) (reach x)
  have stop := WilsonPositionProgramInfraredCircuit.finalSide D j w x
  let N : ℝ := D.finalSide.side.val
  let t : ℝ := (D.ratio:ℝ)^(i x+D.reserve*(i x)*(i x))
  have N1 : 1≤N := by
    dsimp only [N]
    exact_mod_cast (show 1≤D.finalSide.side.val from D.finalSide.side.property)
  have N0 : 0<N := lt_of_lt_of_le zero_lt_one N1
  have t0 : 0<t := by dsimp [t]; exact pow_pos (by exact_mod_cast (show 0<D.ratio from (by decide : 0<3).trans_le D.large)) _
  have ht := log_lower D (i x)
  have t1 : (i x:ℝ)^2*Real.log D.ratio ≤ Real.log t := ht
  have nonneg : 0≤Real.log D.ratio := Real.log_nonneg (by exact_mod_cast (show 1≤D.ratio from (by decide : 1≤3).trans D.large))
  have a0 : 0≤(i x:ℝ)^2*Real.log D.ratio := mul_nonneg (sq_nonneg _) nonneg
  have prod : 0<N*t := mul_pos N0 t0
  have left : (i x:ℝ)^2*Real.log D.ratio ≤ Real.log (N*t) := by
    rw [Real.log_mul N0.ne' t0.ne']; linarith [Real.log_nonneg N1]
  apply ENNReal.ofReal_le_ofReal
  simp only [Sky.modifyErr,Sky.transferErr,Sky.IR₀,Sky.IR₁,pow_zero,pow_one,inv_one,one_mul]
  change (((S).P x)⁻¹+((S).P x ^ ((1/2:ℝ)/2))⁻¹)+
    ((S).l ((ending).choose x) ^ (1/2:ℝ))⁻¹ ≤ _
  have P : (S).P x=N*t := (congrArg (fun n : Side => (n.val:ℝ)) top).trans (side D _)
  have L : (S).l ((ending).choose x) = t := by
    change ((WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val:ℝ) /
      (WilsonPositionProgramInfraredCircuit.count D j w (Page.finallyW j x)).val=_
    rw [top, stop, side]; change (N*t)/N=t; field_simp
  rw [P,L]
  have first : (N*t)⁻¹ ≤ Real.exp (-(i x:ℝ)^2*Real.log D.ratio/4) := by
    rw [←Real.exp_log prod, ←Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  have second : ((N*t)^((1/2:ℝ)/2))⁻¹ ≤ Real.exp (-(i x:ℝ)^2*Real.log D.ratio/4) := by
    rw [Real.rpow_def_of_pos prod,←Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith)
  have third : (t^(1/2:ℝ))⁻¹ ≤ Real.exp (-(i x:ℝ)^2*Real.log D.ratio/4) := by
    rw [Real.rpow_def_of_pos t0,←Real.exp_neg]; exact Real.exp_le_exp.mpr (by linarith)
  linarith

end YM.Integration.WilsonPositionProgramSubmittedPeriod
