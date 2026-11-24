import YangMills.WilsonProof.NativeSupport.OriginalGrowth

/-! Explicit room and replication costs. The degree 20W+17 precedes the
reference truncation order. Here W bounds the logarithmic inlet width. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Finset Lattice RG Wilson RGComparison.Core16 PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G : Gauge}

def stencilCost (s m : ℕ) := 2*s+2*m+1
def radiusCost (s m W : ℕ) := 2*W+4+(stencilCost s m)^4
def roomCost (s m W Q : ℕ) := m*radiusCost s m W+Q+2
def copyCost (s m W Q : ℕ) := 4+20*roomCost s m W Q
def densityCost (s m W Q : ℕ) := 1+m^2*(2*copyCost s m W Q+1)^4+m^4
def layerCost (κ : ℝ) (s m W Q : ℕ) := 16*κ*W*(densityCost s m W Q:ℝ)
def roomSize (s m W Q x : ℕ) := roomCost s m W Q*x^(4*W+2)

theorem native_room (R : Run G) (simple : G.Simple) {k N per : ℕ}
    (T : Slices R.family.path.levels per) (hk : k≤N) (s m W Q x : ℕ)
    (hx : 1≤x) (bcap : R.alloy.B.a.clock.hatBeta N ≤ x)
    (expCap : (R.alloy.B.a.budget N).supportExponent+1 ≤ x)
    (dist : scale (traversal T hk) ≤ x^W) (steps : N-k≤W*x) :
    (m:ℝ)*logLoss R k N (s+scale (traversal T hk)*m)
        +(Q+1:ℕ)*Real.log (x:ℝ) ≤ roomSize s m W Q x := by
  let A:=R.alloy.B.a
  let b:=A.clock.hatBeta N
  let U:=scale (traversal T hk)
  let X:ℝ:=x
  let E:=4*W+2
  have Xone : 1≤X := by dsimp only [X]; exact_mod_cast hx
  have Xpos:=zero_lt_one.trans_le Xone
  have oneW : 1≤X^W := one_le_pow₀ Xone
  have oneE : 1≤X^E := one_le_pow₀ Xone
  have Xbig : X ≤ X^E := by
    calc X=X^1 := (pow_one _).symm
         _ ≤ _ := pow_le_pow_right₀ Xone (by dsimp [E]; omega)
  have ord2 : X^2 ≤ X^E := pow_le_pow_right₀ Xone (by dsimp [E]; omega)
  have ordW : X^(4*W+1) ≤ X^E := pow_le_pow_right₀ Xone (by dsimp [E]; omega)
  have b0 : 0<b := zero_lt_one.trans (A.fits.delayed _)
  have lb : Real.log b ≤ X := (Real.log_le_sub_one_of_pos b0).trans (by linarith only [bcap])
  have logx : Real.log X ≤ X := (Real.log_le_sub_one_of_pos Xpos).trans (by linarith)
  have walker : ((N-k:ℕ):ℝ) ≤ W*X := by dsimp only [X]; exact_mod_cast steps
  have scaleCap : (U:ℝ) ≤ X^W := by dsimp only [U,X]; exact_mod_cast dist
  have localCap : 2*((s:ℝ)+(U:ℝ)*m)+1 ≤ (stencilCost s m:ℝ)*X^W := by
    have base:=mul_le_mul_of_nonneg_left oneW (show 0 ≤ 2*(s:ℝ)+1 by positivity)
    have cg:=mul_le_mul_of_nonneg_right scaleCap (Nat.cast_nonneg m)
    dsimp [stencilCost]; push_cast; nlinarith only [base,cg]
  have local4 := pow_le_pow_left₀ (show 0 ≤ 2*((s:ℝ)+(U:ℝ)*m)+1 by positivity) localCap 4
  have blockPay : ((A.budget N).supportExponent+1)*(2*((s:ℝ)+U*m)+1)^4 ≤
      (stencilCost s m:ℝ)^4*X^E := by
    calc _ ≤ X*((stencilCost s m:ℝ)*X^W)^4 :=
              mul_le_mul expCap local4 (by positivity) Xpos.le
         _ = (stencilCost s m:ℝ)^4*X^(4*W+1) := by rw [mul_pow,show 4*W=W*4 by omega,pow_succ X (W*4),pow_mul]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left ordW (by positivity)
  have datePay : 2*((N-k:ℕ):ℝ)*Real.log b ≤ 2*(W:ℝ)*X^E := by
    have h:=mul_le_mul walker lb (Real.log_nonneg (A.fits.delayed N).le) (by positivity)
    exact (show _≤2*W*X^2 by nlinarith only [h]).trans (mul_le_mul_of_nonneg_left ord2 (by positivity))
  have cut := log_loss_bound R simple k N (s+U*m)
  change logLoss R k N (s+U*m) ≤ 2*((N-k:ℕ):ℝ)*Real.log b+Real.log b/2+
    Real.log 4 + ((A.budget N).supportExponent+1)*(2*(((s+U*m:ℕ):ℝ))+1)^4 at cut
  rw [Nat.cast_add,Nat.cast_mul] at cut
  have rad : logLoss R k N (s+U*m) ≤ (radiusCost s m W:ℝ)*X^E := by
    dsimp only [radiusCost]; push_cast
    linarith only [cut,datePay,blockPay,lb,Xbig,oneE,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)]
  change (m:ℝ)*logLoss R k N (s+U*m)+((Q+1:ℕ):ℝ)*Real.log X ≤ _
  calc _ ≤ (m:ℝ)*((radiusCost s m W:ℝ)*X^E)+((Q+1:ℕ):ℝ)*X^E :=
            add_le_add (mul_le_mul_of_nonneg_left rad (Nat.cast_nonneg _))
              (mul_le_mul_of_nonneg_left (logx.trans Xbig) (Nat.cast_nonneg _))
       _ ≤ _ := by dsimp only [roomSize,roomCost,E]; push_cast; change _ ≤ _*X^(4*W+2)
                   nlinarith only [show 0≤X^(4*W+2) by positivity]

theorem density_cap (s m W Q x M : ℕ) (hx : 1≤x) (hM : M≤2*x^2) :
    max (charge m (spacing M (roomSize s m W Q x))) (m^4) ≤ densityCost s m W Q*x^(16*W+16) := by
  let L:=roomSize s m W Q x
  let E:=4*W+4
  have x2 : 1≤x^2 := Nat.one_le_pow _ _ hx
  have E0 : 1≤x^E := Nat.one_le_pow _ _ hx
  have x2E : x^2≤x^E := Nat.pow_le_pow_right hx (by dsimp [E];omega)
  have first : 2*M+1 ≤ 5*x^2 := by omega
  have sR : spacing M L ≤ copyCost s m W Q*x^E := by
    have m1:=Nat.mul_le_mul_right L first
    have prod : x^2*L=roomCost s m W Q*x^E := by
      dsimp [L,roomSize,E]; rw [show 4*W+4=2+(4*W+2) by omega,pow_add]; ring
    dsimp only [spacing,copyCost]
    nlinarith only [hM,x2E,m1,prod]
  have prep : 2*spacing M L+1 ≤ (2*copyCost s m W Q+1)*x^E := by nlinarith only [sR,E0]
  have four:=Nat.pow_le_pow_left prep 4
  have ee : (x^E)^4=x^(16*W+16) := by rw [←pow_mul]; congr 1; dsimp [E]; omega
  rw [mul_pow,ee] at four
  have big : 1≤x^(16*W+16) := Nat.one_le_pow _ _ hx
  have fund:=Nat.mul_le_mul_left (m^2) four
  apply max_le
  · change 1+m^2*(2*spacing M L+1)^4≤_
    dsimp only [densityCost]
    nlinarith only [fund,big,Nat.zero_le (m^4*x^(16*W+16))]
  · exact (Nat.le_mul_of_pos_right _ big).trans
      (Nat.mul_le_mul_right _ (show m^4 ≤ densityCost s m W Q by dsimp [densityCost];omega))

end YM.Integration.InletSusceptibility.Packet
