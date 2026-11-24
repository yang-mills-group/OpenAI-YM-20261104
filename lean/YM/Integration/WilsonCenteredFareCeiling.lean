import YM.Integration.WilsonCenteredCountertermSlate

/-! A fixed power of the genuine incoming fares controls the physical
two-child invoice. The exponent does not depend on the evaluation order. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredFareCeiling
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
  {d : ℕ} {F : Frame G d}

private def Band (M : ℝ) (k : ℕ) (v : ℝ) : Prop := 0≤v ∧ v≤M^k
private lemma linear {M x : ℝ} (lo : 0≤x) (hi : x≤M) : Band M 1 x := ⟨lo,by simpa only [pow_one]⟩
private lemma multiply {M a b : ℝ} {j k : ℕ} (h : 0≤M) (x : Band M j a) (y : Band M k b) : Band M (j+k) (a*b) :=
  ⟨mul_nonneg x.1 y.1,(mul_le_mul x.2 y.2 y.1 (pow_nonneg h _)).trans_eq (pow_add ..).symm⟩
private lemma raise {M a : ℝ} {j k : ℕ} (h : 1≤M) (x : Band M j a) (le : j≤k) : Band M k a :=
  ⟨x.1,x.2.trans (pow_le_pow_right₀ h le)⟩

private lemma light {M μ η κ a b : ℝ} (p : BudgetPoint) (S : SectionData F) (Y : Hol G)
    (high : 1≤M) (FEE : factor Y S p.supportExponent μ≤M) (cost : Band M 6 a)
    (h₀ : 0≤hitWidth p*η/κ) (h₁ : hitWidth p*η/κ≤1) :
    cartage p Y S μ η κ a b ≤ 3*M^7+b := by
  have priced : factor Y S p.supportExponent μ*a≤M^7 := by
    rw [show M^7=M*M^6 by ring]
    exact mul_le_mul FEE cost.2 cost.1 (by linarith)
  have small: (hitWidth p*η/κ)*a≤M^7 := by
    have upper:=mul_le_mul_of_nonneg_right h₁ cost.1
    exact (upper.trans_eq (one_mul a)).trans (raise high cost (by decide : 6≤7)).2
  have repeatFee : (hitWidth p*η/κ)*(factor Y S p.supportExponent μ*a)≤M^7 := calc
    _ ≤ (hitWidth p*η/κ)*M^7 := mul_le_mul_of_nonneg_left priced h₀
    _ ≤ _ := (mul_le_mul_of_nonneg_right h₁ (pow_nonneg (by linarith : 0≤M) _)).trans_eq (one_mul _)
  unfold cartage
  linarith only [priced,small,repeatFee]

private theorem divided {M u z t κ : ℝ} (_m : 1≤M) (noZero : κ≠0) (room : u≤1)
    (charge : Band M 7 (z*t)) : ((z*(t*κ))+u*(z*(t*κ)))/κ ≤ 2*M^7 := by
  have eqn : ((z*(t*κ))+u*(z*(t*κ)))/κ=(1+u)*(z*t) := by field_simp
  rw [eqn]
  exact mul_le_mul (by linarith) charge.2 charge.1 (by norm_num)

omit [Fintype V] in
theorem original (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (a b c : V)
    (s : R.Mode) (Z : Support n) (rad : ℕ) {E κ η μ M : ℝ} (hw : ∀ j,0<w j)
    (hm : 1≤M) (fee : factor Y S p.supportExponent μ≤M) (paid : 0≤E) (upper : E≤M)
    (hk : 0<κ) (hk1 : κ≤1) (hv : 0≤η) (room : hitWidth p*η≤1) (reclaim : hitWidth p*η/κ≤1)
    (single : stage p rad ({()}:Finset Unit)≤M) (two : stage p rad ({false,true}:Finset Bool)≤M)
    (cover : Real.exp ((p.supportExponent+2)*coverNumber p.B Z)≤M)
    (wa : (w a)⁻¹≤M) (wb : (w b)⁻¹≤M) (pair : (Poly.toll w s)⁻¹≤M) (counter : (Poly.toll w (R.fire c))⁻¹≤M) :
    WilsonCenteredAbsoluteGallery.fare p S Y w a b c s Z rad E κ η μ ≤ 19*M^7 := by
  let z := Real.exp ((p.supportExponent+2)*coverNumber p.B Z)
  let u := hitWidth p*η
  have m : 0≤M := zero_le_one.trans hm
  have u0 : 0≤u := mul_nonneg (by unfold hitWidth;positivity) hv
  have scaled : 0≤u/κ := div_nonneg u0 hk.le
  have zB:=linear (Real.exp_nonneg _) cover
  have eB:=linear paid upper
  have aB:=linear (inv_nonneg.mpr (hw a).le) wa
  have bB:=linear (inv_nonneg.mpr (hw b).le) wb
  have core (j : R.Mode) (l : (Poly.toll w j)⁻¹≤M) : Band M 1 (Poly.toll w j)⁻¹ :=
    linear (inv_nonneg.mpr (prod_nonneg (fun i _=>(hw i).le))) l
  have t1:=linear (zero_le_one.trans (funded p rad ({()}:Finset Unit))) single
  have t2:=linear (zero_le_one.trans (funded p rad ({false,true}:Finset Bool))) two
  have oneFee (j : R.Mode) (wage : (Poly.toll w j)⁻¹≤M) :
      cartage p Y S μ η κ (stage p rad ({()}:Finset Unit)*(z*((Poly.toll w j)⁻¹*E))) 0≤3*M^7 := by
    have head:=multiply m t1 (multiply m zB (multiply m (core j wage) eB))
    simpa only [add_zero] using light p S Y hm fee (raise hm head (by decide)) scaled reclaim (b:=0)
  have pairFee : cartage p Y S μ η κ (stage p rad ({false,true}:Finset Bool)*(z*(((w a)⁻¹*E)*((w b)⁻¹*E)))) 0≤3*M^7 := by
    have head:=multiply m t2 (multiply m zB (multiply m (multiply m aB eB) (multiply m bB eB)))
    simpa only [add_zero] using light p S Y hm fee head scaled reclaim (b:=0)
  have cross (i j : ℝ) (bi : Band M 1 i) (bj : Band M 1 j) :
      ((z*(i*E))*(j*κ)+u*((z*(i*E))*(j*κ)))/κ≤2*M^7 :=
    divided hm hk.ne' room (raise hm (multiply m (multiply m zB (multiply m bi eB)) bj) (by decide))
  have dark (j : R.Mode) (wage : (Poly.toll w j)⁻¹≤M) :
      WilsonCenteredHardMount.bill p Z η ((Poly.toll w j)⁻¹*κ)/κ≤2*M^7 :=
    divided hm hk.ne' room (raise hm (multiply m zB (core j wage)) (by decide))
  have hardPair : WilsonCenteredHardMount.bill p Z η (((w a)⁻¹*κ)*((w b)⁻¹*κ))/κ≤2*M^7 := by
    have left := multiply m aB (linear hk.le (hk1.trans hm))
    rw [show ((w a)⁻¹*κ)*((w b)⁻¹*κ)=(((w a)⁻¹*κ)*(w b)⁻¹)*κ by ring]
    exact divided hm hk.ne' room (raise hm (multiply m zB (multiply m left bB)) (by decide))
  unfold WilsonCenteredAbsoluteGallery.fare
  dsimp only
  linarith only [oneFee s pair,oneFee (R.fire c) counter,pairFee,cross _ _ aB bB,cross _ _ bB aB,
    dark s pair,dark (R.fire c) counter,hardPair]

end YM.Integration.WilsonCenteredFareCeiling
