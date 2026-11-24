import YM.Integration.WilsonOlderSignedOneMarkBooked
import YM.Integration.WilsonOlderSignedOneMarkPlant
import YM.Integration.WilsonCenteredReporterClock

/-! At the actual single occupied root the radius discount in the old regular
quote cancels exactly on restoring its physical mark. The once-divided hard
return spends the radius change at the original clock. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOlderSignedOneMarkTariff
open Filter Finset Lattice Wilson RG QuadraticLocal Marker Planned.GuardedAtom Push.Local
open Source Labels Extra.Histories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {n : Side} {d : ℕ} {F : Frame G d}

def charge (Y : Hol G) (S : SectionData F) :=
  Real.exp ((102:ℝ)*atomTiles S)*(1+5*|readPrice Y F|)

theorem root (p : BudgetPoint) (support : p.supportExponent≤100) (y : Site n) :
    (p.supportExponent+2)*coverNumber p.B {y} ≤ 102 := by
  have ht : coverNumber p.B {y}≤1 := (Corona.cover_mono (Lattice.halo_subset 0 {y}) p.B).trans
    (show coverNumber p.B (Lattice.halo 0 {y})≤_ from by simpa using Corona.tile y 0 p.B p.B_pos)
  have real : (coverNumber p.B {y}:ℝ) ≤ 1 := by exact_mod_cast ht
  calc
    _ ≤ (p.supportExponent+2)*1 := mul_le_mul_of_nonneg_left real (by linarith only [p.exponent_pos])
    _ ≤ _ := by linarith only [support]

theorem restored (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (v : V)
    (Z : Support n) {r κ : ℝ} (wp : 0<w v) (rp : 0<r) (kp : 0<κ) (e a η μ : ℝ) :
    let s:=(Stock.census V).fire v
    let b:=Real.exp ((p.supportExponent+2)*coverNumber p.B Z)
    Poly.toll w s*WilsonOlderSignedSingletonFare.fare p S Y (Stoop.radius w r) s 1 Z 0
      (r⁻¹*e) (a*κ) κ η μ =
      cartage p Y S μ η κ (stage p 0 ({()}:Finset Unit)*(b*e)) ((1+hitWidth p*η)*b*(r*a)) := by
  intro s b
  simp only [WilsonOlderSignedSingletonFare.fare,WilsonCenteredHardMount.bill,cartage,s,Poly.solo_toll,
    Stoop.radius,b,norm_one,one_mul]
  field_simp [wp.ne',rp.ne',kp.ne']

theorem factor_bound (p : BudgetPoint) (S : SectionData F) (Y : Hol G) {x μ : ℝ}
    (hx : 1≤x) (support : p.supportExponent≤100) (hn : 0≤μ) (cap : μ≤4*x^2) :
    factor Y S p.supportExponent μ ≤ charge Y S*x^2 := by
  have one:=one_le_pow₀ hx (n:=2)
  have shelf : Real.exp ((p.supportExponent+2)*atomTiles S)≤Real.exp ((102:ℝ)*atomTiles S) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [support]) (Nat.cast_nonneg _))
  have projected : (1+μ)*readPrice Y F≤(5*x^2)*|readPrice Y F| :=
    (mul_le_mul_of_nonneg_left (le_abs_self (readPrice Y F)) (by linarith only [hn])).trans
      (mul_le_mul_of_nonneg_right (by linarith only [cap,one]) (abs_nonneg _))
  have lookup : atomPrice Y F μ ≤ (1+5*|readPrice Y F|)*x^2 := by
    unfold atomPrice
    linarith only [projected,one]
  unfold factor charge
  exact (mul_le_mul shelf lookup (zero_le_one.trans (atomPrice_ge_one Y F hn)) (Real.exp_nonneg _)).trans_eq
    (mul_assoc ..).symm

theorem point (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (v : V) (y : Site n)
    {r κ x e a η μ : ℝ} (wp : 0<w v) (rp : 0<r) (kp : 0<κ) (hx : 1≤x)
    (support : p.supportExponent≤100) (hn : 0≤μ) (cap : μ≤4*x^2)
    (moved : stage p 0 ({()}:Finset Unit)≤2*x^2) (quiet : 0≤η)
    (room : hitWidth p*η≤1) (reserve : hitWidth p*η/κ≤1) (he : 0≤e) (ha : 0≤a) :
    let s:=(Stock.census V).fire v
    Poly.toll w s*WilsonOlderSignedSingletonFare.fare p S Y (Stoop.radius w r) s 1 {y} 0
      (r⁻¹*e) (a*κ) κ η μ ≤
        2*Real.exp 102*(1+2*charge Y S)*x^4*e+2*Real.exp 102*(r*a) := by
  intro s
  rw [restored p S Y w v {y} wp rp kp]
  let t:=stage p 0 ({()}:Finset Unit)
  let z:=Real.exp ((p.supportExponent+2)*coverNumber p.B {y})
  let c:=hitWidth p*η/κ
  let D:=factor Y S p.supportExponent μ
  let a₀:=t*(z*e)
  have Z0 : 0≤z := Real.exp_nonneg _
  have Z : z≤Real.exp 102 := Real.exp_le_exp.mpr (root p support y)
  have t0 : 0≤t := zero_le_one.trans (funded ..)
  have a0 : 0≤a₀ := mul_nonneg t0 (mul_nonneg Z0 he)
  have D0 : 0≤D := mul_nonneg (Real.exp_nonneg _) (zero_le_one.trans (atomPrice_ge_one Y F hn))
  have c0 : 0≤c := div_nonneg (mul_nonneg (zero_le_one.trans (width_one_le _)) quiet) kp.le
  have c1 : c*a₀≤a₀ := mul_le_of_le_one_left a0 reserve
  have c2 : c*(D*a₀)≤D*a₀ := mul_le_of_le_one_left (mul_nonneg D0 a0) reserve
  have red : D*a₀+((((1+hitWidth p*η)*z*(r*a))+c*a₀)+c*(D*a₀))≤
      (1+2*D)*a₀+(1+hitWidth p*η)*z*(r*a) := by linarith only [c1,c2]
  have fa : 1+2*D≤(1+2*charge Y S)*x^2 := by
    have f:=factor_bound p S Y hx support hn cap
    have one:=one_le_pow₀ hx (n:=2)
    dsimp only [D]
    linarith only [f,one]
  have up : a₀≤(2*x^2)*(Real.exp 102*e) :=
    mul_le_mul moved (mul_le_mul_of_nonneg_right Z he) (mul_nonneg Z0 he) (by positivity)
  have fine : (1+2*D)*a₀ ≤ 2*Real.exp 102*(1+2*charge Y S)*x^4*e :=
    (mul_le_mul fa up a0 (by unfold charge;positivity)).trans_eq (by ring)
  have hard : (1+hitWidth p*η)*z*(r*a)≤2*Real.exp 102*(r*a) :=
    mul_le_mul_of_nonneg_right (mul_le_mul (by linarith only [room]) Z Z0 (by norm_num)) (mul_nonneg rp.le ha)
  exact red.trans (add_le_add fine hard)

end YM.Integration.WilsonOlderSignedOneMarkTariff
