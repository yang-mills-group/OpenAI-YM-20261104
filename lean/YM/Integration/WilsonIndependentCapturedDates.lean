import YM.Integration.WilsonIndependentCapturedScale
import YM.Integration.WilsonThermometerUnitFilingWindow

/-! Locate the genuine weak Wilson stop inside the voted infrared band.
Both of its physical mesh bounds use the measured coupling at the upper
report and a single date chosen before either regulator. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedDates
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Pert.Asymptotics WilsonPositionProgramCommonWindow WilsonPositionProgramReporterBand
open scoped Topology Classical
variable {G : Gauge} (C : Run G) (D : XSpace.Run)
local notation "σ" => C.family.S.scale
local notation "a" => C.family.S.a
local notation "H" => C.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda C.family.path.levels

theorem mesh (j b : ℕ) : Real.log (a j/a b) = σ b-σ j := by
  rw [Real.log_div (C.family.S.a_pos j).ne' (C.family.S.a_pos b).ne']
  simp only [Schedule.scale,Real.log_inv]
  ring

theorem increasing : StrictMono (σ) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have large := C.family.S.block_large i
  rw [C.family.S.scale_succ]
  exact lt_add_of_pos_right _ (Real.log_pos
    (by exact_mod_cast (show 1 < (C.family.S.block i).val by omega)))

theorem gap {stage} (B : Band C D stage) (t : ℕ) :
    σ (B.reporter+t) - σ (B.lower t) =
      (D.reserve:ℝ)*(B.index t:ℝ)*(B.index t:ℝ)*Real.log D.ratio := by
  have total := WilsonPositionProgramInversion.logged C D (B.lower t) (B.powers t) (B.blocks t) (B.span t)
  rw [B.extent t,B.top t] at total
  push_cast at total
  have fine := congrArg Real.log (B.spacing t)
  rw [mesh] at fine
  change _ = Real.log ((D.den (B.index t):ℝ)⁻¹) at fine
  rw [Real.log_inv,XSpace.Run.den,Nat.cast_pow,Real.log_pow] at fine
  linarith only [total,fine]

private theorem mass (simple : G.Simple) (N per b : ℕ) (within : b ≤ N) :
    Real.log (regulatorRun C.family N per b)⁻¹ ≤ Λ b := by
  have hh := Extension.UV.hat_positive simple C.alloy.B.a b
  change 1 < H b at hh
  have band := (C.makes.wilson.represents N per b within).band
  let beta := C.family.path.β N per b
  have pos : 0 < beta := lt_of_lt_of_le (div_pos (zero_lt_one.trans hh) (by norm_num)) band.1
  have rb : Real.sqrt beta ≤ 2*H b := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have bound : beta ≤ 2*H b := band.2
    nlinarith [mul_nonneg (show 0 ≤ 2*H b-1 by linarith) (show 0 ≤ 2*H b by linarith)]
  change Real.log ((Real.sqrt beta)⁻¹)⁻¹ ≤ 2+Real.log (H b)
  rw [inv_inv]
  have heard := Real.log_le_log (Real.sqrt_pos.mpr pos) rb
  rw [Real.log_mul (by norm_num) (zero_lt_one.trans hh).ne'] at heard
  linarith only [heard,Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)]

theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow C.kit)
    {stage} (B : Band C D stage) (u d : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∃ v : ℕ, u ≤ v ∧ B.lower t ≤ v ∧ v ≤ B.reporter+t ∧
    ∀ N per : ℕ, B.reporter+t ≤ N →
      let g := regulatorRun C.family N per (B.reporter+t)
      0 < g ∧ g ≤ 1 ∧ a (B.reporter+t) / a v ≤ (g^d)^2 ∧
      σ (B.reporter+t) - σ v ≤ 4*(2*d+1)*Real.log g⁻¹ := by
  let target := 2*d
  have radius := WilsonThermometerUnitFilingWindow.original C simple slow u target
  have later : Tendsto (fun t : ℕ => B.reporter+t) atTop atTop :=
    tendsto_atTop_mono (fun t => Nat.le_add_left t B.reporter) tendsto_id
  filter_upwards [later.eventually radius,B.cofinal.eventually_ge_atTop (4*(target+1))] with t hroom huge
  obtain ⟨v,hbase,hbefore,stop⟩ := hroom
  have hh := Extension.UV.hat_positive simple C.alloy.B.a (B.reporter+t)
  change 1 < H (B.reporter+t) at hh
  have hot : 1 ≤ Λ (B.reporter+t) := by
    change 1 ≤ 2+Real.log (H (B.reporter+t))
    linarith [Real.log_nonneg hh.le]
  have entry := B.floor t
  have first : Λ (B.reporter+t) ≤ (B.index t:ℝ)*Real.log D.ratio :=
    (Real.rpow_one (Λ (B.reporter+t))).symm.le.trans
      ((Real.rpow_le_rpow_of_exponent_le hot (by norm_num : (1:ℝ) ≤ 3/2)).trans entry)
  have ino : (4:ℝ)*(target+1) ≤ B.index t := by exact_mod_cast huge
  have here := (stop (B.reporter+t) 0 le_rfl).2.2.2
  have reach : σ (B.reporter+t) - σ v ≤ 4*(target+1)*Λ (B.reporter+t) := by
    exact here.trans (mul_le_mul_of_nonneg_left (mass C simple (B.reporter+t) 0 _ le_rfl) (by positivity))
  have spare : (1:ℝ) ≤ D.reserve := by exact_mod_cast D.spare
  have idx : 0 ≤ (B.index t:ℝ)*Real.log D.ratio := (zero_le_one.trans hot).trans first
  have room : 4*(target+1)*Λ (B.reporter+t) ≤ σ (B.reporter+t)-σ (B.lower t) := by
    rw [gap C D B t]
    calc
      _ ≤ ((B.index t):ℝ) * ((B.index t:ℝ)*Real.log D.ratio) :=
        mul_le_mul ino first (zero_le_one.trans hot) (by positivity)
      _ ≤ (D.reserve:ℝ) * ((B.index t:ℝ) * ((B.index t:ℝ)*Real.log D.ratio)) :=
        le_mul_of_one_le_left (mul_nonneg (by positivity) idx) spare
      _ = _ := by ring
  refine ⟨v,hbase,(increasing C).le_iff_le.mp (by linarith only [room,reach]),hbefore,?_⟩
  intro N per cut g
  obtain ⟨gp,gs,low,high⟩ := stop N per cut
  refine ⟨gp,gs,?_,?_⟩
  · apply (Real.log_le_log_iff (div_pos (C.family.S.a_pos _) (C.family.S.a_pos _)) (pow_pos (pow_pos gp _) _)).mp
    rw [mesh,Real.log_pow,Real.log_pow]
    change target * Real.log g⁻¹ ≤ _ at low
    rw [Real.log_inv] at low
    dsimp [target] at low
    push_cast at low
    push_cast
    linarith only [low]
  · dsimp [target] at high
    push_cast at high
    exact high

end YM.Integration.WilsonIndependentCapturedDates

