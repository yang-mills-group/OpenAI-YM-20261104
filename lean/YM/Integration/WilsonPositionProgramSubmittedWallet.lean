import YM.Integration.WilsonPositionProgramSubmittedPeriod
import YM.Integration.WilsonPositionProgramInversion
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedWallet
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (simple : G.Simple)
variable (m j : X → ℕ) (w : X → ℕ → ℕ) (i : X → ℕ)
variable (blocks : ∀ x t, (C.family.S.block (m x+t)).val = D.ratio^(w x t))
variable (reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x)
local notation "β" => C.family.path.levels.clock.hatBeta
local notation "Λ" => RG16.Lambda C.family.path.levels
local notation "gains" => G.slopeConstant*Real.log D.ratio

include simple blocks reach in
private theorem height (x : X) (old : 1≤β (m x)) :
    Λ (m x+j x) ≤ Λ (m x)+gains*(D.reserve*(i x:ℝ)*(i x)+i x) := by
  let h : ℝ := gains*((D.reserve:ℝ)*(i x)*(i x)+i x)
  have dr : 1≤(D.ratio:ℝ) := by exact_mod_cast (show 1≤D.ratio from (by decide : 1≤3).trans D.large)
  have h0 : 0≤h := by dsimp [h]; positivity [Gauge.slopeConstant_pos simple, Real.log_nonneg dr]
  have diff : β (m x+j x)-β (m x)= h := by
    have step := WilsonPositionProgramInversion.logged C D (m x) (w x) (blocks x) (j x)
    change (C.family.path.levels.clock.bar+G.slopeConstant*C.family.S.scale (m x+j x))-
      (C.family.path.levels.clock.bar+G.slopeConstant*C.family.S.scale (m x))=_
    rw [reach x] at step
    push_cast at step
    dsimp [h]
    calc _ = G.slopeConstant*(C.family.S.scale (m x+j x)-C.family.S.scale (m x)) := by ring
         _ = _ := by rw [step];ring
  have b : 0<β (m x) := lt_of_lt_of_le zero_lt_one old
  have b' : 0<β (m x+j x) := by linarith only [b,diff,h0]
  have prod : β (m x+j x)≤ β (m x)*(1+h) := by nlinarith only [diff,mul_nonneg (sub_nonneg.mpr old) h0]
  have logb := Real.log_le_log b' prod
  rw [Real.log_mul b.ne' (by linarith only [h0] : 1+h≠0)] at logb
  have logh := Real.log_le_sub_one_of_pos (by linarith only [h0] : 0<1+h)
  change 2 + Real.log (β (m x+j x))≤2+Real.log (β (m x))+h
  linarith

include simple blocks reach in
/-- The joint compact positional tariff grows at most exponentially in the enrolled fine date.
The orbit includes the genuine volumes, post-block expenses and submitted displacements. -/
theorem amount (H : ℝ) : ∃ A : ℝ, 0<A ∧ ∀x, 1≤β (m x) → Λ (m x)≤(i x:ℝ)*Real.log D.ratio →
    WilsonPositionProgramInfraredMeter.amount C D m j w i H x ≤
      A*Real.exp ((2+Real.log D.ratio)*(i x:ℝ)) := by
  let l := Real.log (D.ratio:ℝ)
  let s := G.slopeConstant*l
  let N := (D.finalSide.side.val:ℝ)
  have N1 : 1≤N := by dsimp only [N]; exact_mod_cast (show 1≤D.finalSide.side.val from D.finalSide.side.property)
  have lp : 0≤l := Real.log_nonneg (by exact_mod_cast (show 1≤D.ratio from (by decide : 1≤3).trans D.large))
  have sp : 0 ≤ s := mul_nonneg (Gauge.slopeConstant_pos simple).le lp
  let A := 1+Real.log N+l+(s+l)*(1+D.reserve)+(max 0 H+1)
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]; positivity [Real.log_nonneg N1,le_max_left 0 H]
  intro x old lower
  let u := (i x:ℝ)
  let E := Real.exp ((2+l)*u)
  have u0 : 0≤u := by positivity
  have ue : (1+u)^2≤E := by
    have a := Real.add_one_le_exp u
    have h := mul_self_le_mul_self (by linarith : 0≤u+1) a
    simp only [←Real.exp_add] at h
    have he : Real.exp (u+u)≤E := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg lp u0])
    nlinarith only [h,he]
  have E1 : 1≤E := by nlinarith only [ue,u0,sq_nonneg u]
  have Eu : u≤E := by nlinarith only [ue,u0,sq_nonneg u]
  have E2 : u*u≤E := by nlinarith only [ue,u0]
  have top := WilsonPositionProgramInfraredCircuit.fine D j w (x:=x) (i:=i x) (reach x)
  have side := WilsonPositionProgramSubmittedPeriod.side D (i x)
  have dr : 0<(D.ratio:ℝ) := by exact_mod_cast (show 0<D.ratio from (by decide : 0<3).trans_le D.large)
  have lg : Real.log (((D.step (i x)).p.side.val):ℝ) = Real.log N+(u+D.reserve*u*u)*l := by
    rw [side, Real.log_mul (lt_of_lt_of_le zero_lt_one N1).ne' (pow_pos dr _).ne',Real.log_pow]
    push_cast; rfl
  have base := height C D simple m j w i blocks reach x old
  change Λ (m x+j x) ≤ Λ (m x)+s*(D.reserve*u*u+u) at base
  change Λ (m x)≤u*l at lower
  have inv : ((D.step (i x)).spacing)⁻¹≤E := by
    change (((D.ratio^(i x):ℕ):ℝ)⁻¹)⁻¹≤_
    rw [inv_inv,Nat.cast_pow,←Real.rpow_natCast, Real.rpow_def_of_pos dr]
    exact Real.exp_le_exp.mpr (by dsimp [E,u,l]; nlinarith)
  have mass : 0 ≤ max 0 H+1 := by linarith [le_max_left 0 H]
  have geom : ((D.reserve:ℝ)*u*u+u)≤(1+D.reserve)*E := by
    have r := mul_le_mul_of_nonneg_left E2 (show 0≤(D.reserve:ℝ) by positivity)
    nlinarith only [r,Eu]
  have lg0 : 0≤Real.log N+(u+D.reserve*u*u)*l := by positivity [Real.log_nonneg N1]
  dsimp only [WilsonPositionProgramInfraredMeter.amount]
  rw [top,lg, abs_of_nonneg lg0, div_eq_mul_inv]
  change _≤ A*E
  dsimp only [A]
  nlinarith only [base,lower,mul_le_mul_of_nonneg_right Eu lp,
    mul_le_mul_of_nonneg_left geom sp,mul_le_mul_of_nonneg_left geom lp,
    mul_le_mul_of_nonneg_left E1 (Real.log_nonneg N1),mul_le_mul_of_nonneg_left inv mass,E1]

end YM.Integration.WilsonPositionProgramSubmittedWallet
