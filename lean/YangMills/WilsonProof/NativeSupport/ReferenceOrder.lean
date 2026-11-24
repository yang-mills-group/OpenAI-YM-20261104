import YangMills.WilsonProof.NativeSupport.InletExpenses
import YangMills.WilsonProof.NativeSupport.EveryPattern

/-! A fixed polynomial loss is bought by choosing the reference order after
the inlet width. Finite waiting thresholds may depend on the order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16 PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge}

def lossDegree (W : ℕ) := 20*W+17
def halfOrder (W Q : ℕ) := lossDegree W+2*Q+1

private theorem purchase (x m Q E : ℕ) (Xone : 1≤(x:ℝ)) {C η : ℝ} (cp : 0≤C)
    (arity : 2*(m:ℝ)≤x) (cash : 2*C*4^(E+2*Q+1)≤x) (fee : η≤(4/(x:ℝ))^(E+2*Q+1)) :
    (m:ℝ)*Real.exp (-2*(((Q+1:ℕ):ℝ)*Real.log (x:ℝ)))+C*(x:ℝ)^E*η≤((x:ℝ)^Q)⁻¹^2 := by
  let X:ℝ:=x
  have xp : 0<X := zero_lt_one.trans_le Xone
  have Z : 0<X^Q := pow_pos xp _
  have e : 0<X^E := pow_pos xp _
  have ep : Real.exp (-2*(((Q+1:ℕ):ℝ)*Real.log X))=((X^Q)^2*X^2)⁻¹ := by
    rw [neg_mul,Real.exp_neg,show 2*(((Q+1:ℕ):ℝ)*Real.log X)=(2*(Q+1):ℕ)*Real.log X by push_cast;ring,
      Real.exp_nat_mul,Real.exp_log xp,show 2*(Q+1)=Q*2+2 by omega,pow_add,pow_mul]
  have den : X^(E+2*Q+1)=X^E*(X^Q)^2*X := by
    rw [pow_succ,pow_add,show 2*Q=Q*2 by omega,pow_mul]
  have term1 : (m:ℝ)*Real.exp (-2*(((Q+1:ℕ):ℝ)*Real.log X)) ≤ (X^Q)⁻¹^2/2 := by
    rw [ep]
    field_simp
    nlinarith only [arity,Xone,mul_nonneg xp.le (show 0≤X-1 from sub_nonneg.mpr Xone)]
  have term2 : C*X^E*η ≤ (X^Q)⁻¹^2/2 := by
    calc _ ≤ C*X^E*(4/X)^(E+2*Q+1) := mul_le_mul_of_nonneg_left fee (mul_nonneg cp e.le)
         _ ≤ _ := by rw [div_pow,den];field_simp;linarith only [cash]
  linarith only [term1,term2]

theorem paid_pattern {I : Type} [Fintype I] [DecidableEq I] (R : Run G)
    (simple : G.Simple) {k N per : ℕ} (T : Slices R.family.path.levels per) (hk : k<N)
    (F : I → Config G (R.family.side N per) → ℝ) (a : I → Site (R.family.side N per)) (s W Q x : ℕ)
    (cont : ∀ i,Continuous (F i)) (sym : ∀ i,GaugeInvariant (F i))
    (unit : ∀ i U,|F i U| ≤ 1) (loc : ∀ i,LocalOn (halo s {a i}) (F i))
    (v : ℕ→ℝ) {η : ℝ} (hη : 0≤η) (top : v (traversal T hk.le).depth=0)
    (offset : ∀ j,0<j → j<(traversal T hk.le).depth → |v j| ≤ η)
    (four : 4≤x) (wanted : 1≤Q) (bcap : R.alloy.B.a.clock.hatBeta N ≤ x)
    (expCap : (R.alloy.B.a.budget N).supportExponent+1≤x)
    (dist : scale (traversal T hk.le)≤x^W) (steps : N-k≤W*x)
    (roof : (R.alloy.B.a.budget k).B≤2*x^2)
    (arity : 2*(Fintype.card I:ℝ)≤x)
    (cash : 2*layerCost R.alloy.B.a.clock.kernel.penalty s (Fintype.card I) W Q*4^(halfOrder W Q)≤x)
    (fee : η ≤ (4/(x:ℝ))^(halfOrder W Q)) :
    let d:=traversal T hk.le
    let β:=RGComparison.Core16.line R.family.path per k N
    let Z:=fun U=>∏ i,F i U
    |mean d (WilsonUniformUnmarkedInletSignedResponse.line β v 1) Z 1-mean d β Z 1| ≤ 3*((x:ℝ)^Q)⁻¹ := by
  let m:=Fintype.card I
  let d:=traversal T hk.le
  let κ:=R.alloy.B.a.clock.kernel.penalty
  let L:=roomSize s m W Q x
  let X:ℝ:=x
  let χ:=max (charge m (spacing (R.alloy.B.a.budget k).B L)) (m^4)
  let U:=scale d
  let E:=lossDegree W
  have hn : 1≤x := by omega
  have pr : 1≤X := by dsimp only [X]; exact_mod_cast hn
  have pos:=zero_lt_one.trans_le pr
  have pp : 0<κ := R.alloy.B.a.clock.kernel.penalty_pos
  have ep : 0<(X^Q)⁻¹ := inv_pos.mpr (pow_pos pos _)
  have fourth : (X^Q)⁻¹≤1/4 := by
    rw [inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    exact (show (4:ℝ) ≤ X by dsimp only [X];exact_mod_cast four).trans
      ((pow_one X).symm.le.trans (pow_le_pow_right₀ pr wanted))
  have hL : 0<L := by dsimp [L,roomSize,roomCost]; positivity
  have hD : 0≤((Q+1:ℕ):ℝ)*Real.log X := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg pr)
  apply every_pattern R simple T hk F a s cont sym unit loc v hD hη ep fourth top offset L hL
    (native_room R simple T hk.le s m W Q x hn bcap expCap dist steps)
  have dens : (χ:ℝ) ≤ (densityCost s m W Q:ℝ)*X^(16*W+16) := by
    dsimp only [X,χ,L]; exact_mod_cast density_cap s m W Q x _ hn roof
  have scaleCap : (U:ℝ)^4≤X^(4*W) := by
    rw [show 4*W=W*4 by omega,pow_mul]
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    dsimp only [X,U,d];exact_mod_cast dist
  have stepCap : (d.depth:ℝ)≤W*X := by dsimp only [d,X];rw [traversal_depth];exact_mod_cast steps
  have allC : (χ:ℝ)*(2*(d.depth:ℝ)*(U:ℝ)^4*4*(η*(κ*2))) ≤ layerCost κ s m W Q*X^E*η := by
    calc _ ≤ ((densityCost s m W Q:ℝ)*X^(16*W+16))*(2*((W:ℝ)*X)*X^(4*W)*4*(η*(κ*2))) := by
               gcongr
         _ = _ := by
               rw [show E=(16*W+16)+(4*W)+1 by dsimp [E,lossDegree];omega,pow_succ X,pow_add]
               dsimp only [layerCost]; ring
  have cp : 0≤layerCost κ s m W Q := by dsimp only [layerCost];positivity
  exact (add_le_add_right allC _).trans (purchase x m Q E pr cp arity cash fee)

end YM.Integration.InletSusceptibility.Packet
