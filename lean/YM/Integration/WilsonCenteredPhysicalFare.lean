import YM.Integration.WilsonCenteredSlateCeiling
import YM.Integration.WilsonCenteredCaptureGeometry

/-! The calibrated centred slate has a fixed inverse-coupling power prior to
all high-order coefficient probes. Its signed weights are charged once. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredPhysicalFare
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms WilsonCenteredLampCapture
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V}
  {d : ℕ} {F : Frame G d}

def degree (seats width : ℕ) := 2*(seats+1)+width+2

def base (S : SectionData F) (Y : Hol G) (α W : ℝ) (seats : ℕ) :=
  3+W+Real.exp ((α+2)*81)+25*(2:ℝ)^(seats+1)+
    Real.exp ((α+2)*atomTiles S)*(1+5*|readPrice Y F|)

theorem original (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ) (a b : V)
    (s : R.Mode) (names : Finset V) (c : V→ℂ) (Z : Support n) (y : Site n) (rad seats width : ℕ)
    {E κ η μ x W α : ℝ} (hw : ∀ j,0<w j) (hx : 1≤x) (hW : 0≤W)
    (support : p.supportExponent≤α) (near : rad≤p.B) (house : Z⊆halo p.B {y})
    (hk : 0<κ) (hk1 : κ≤1) (hv : 0≤η) (room : hitWidth p*η≤1) (divided : hitWidth p*η/κ≤1)
    (motion : WilsonReportRetainedAnchor.reprice p p.B≤2*x^2)
    (paid : 0≤E) (income : E≤25*(2*x^2)^(seats+1)) (μpos : 0≤μ) (read : μ≤4*x^2)
    (wa : (w a)⁻¹≤W*x^width) (wb : (w b)⁻¹≤W*x^width) (pair : (Poly.toll w s)⁻¹≤W*x^width)
    (first : (Poly.toll w (R.fire a))⁻¹≤W*x^width) (rest : ∀u∈names,(Poly.toll w (R.fire u))⁻¹≤W*x^width) :
    WilsonCenteredCountertermSlate.fare p S Y w a b s names c Z rad E κ η μ ≤
      (1+∑v∈names,‖c v‖)*(24*(base S Y α W seats)^7)*x^(degree seats width*7) := by
  let D:=degree seats width
  let B:=base S Y α W seats
  let M:=B*x^D
  let A:=Real.exp ((α+2)*atomTiles S)
  let Z₀:=Real.exp ((α+2)*81)
  let F₀:=A*(1+5*|readPrice Y F|)
  let E₀:=(25:ℝ)*2^(seats+1)
  have xp : 0≤x:=zero_le_one.trans hx
  have Zpos : 0≤Z₀:=Real.exp_nonneg _
  have Fpos : 0≤F₀:=by dsimp [F₀];exact mul_nonneg (Real.exp_nonneg _) (by positivity)
  have Epos : 0≤E₀:=by dsimp [E₀];positivity
  have identity : B=3+W+Z₀+E₀+F₀:=rfl
  have B₁ : 1≤B:=by linarith only [identity,hW,Zpos,Fpos,Epos]
  have one : 1≤M:=one_le_mul_of_one_le_of_one_le B₁ (one_le_pow₀ hx)
  have stage (v : ℝ) (j : ℕ) (cheap : v≤B) (rank : j≤D) : v*x^j≤M :=
    (mul_le_mul_of_nonneg_right cheap (pow_nonneg xp _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx rank) (zero_le_one.trans B₁))
  have at2 : 2*x^2≤M:=stage _ 2 (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,degree];omega)
  have marks:=stage W width (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,degree];omega)
  have zmax : Real.exp ((p.supportExponent+2)*coverNumber p.B Z)≤M :=
    (WilsonCenteredCaptureGeometry.cover p Z y house support).trans (by
      simpa only [pow_zero,mul_one] using stage Z₀ 0 (by linarith only [identity,hW,Zpos,Fpos,Epos]) (Nat.zero_le _))
  have emax : E≤M := income.trans (by
    have yes:=stage E₀ (2*(seats+1)) (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,degree];omega)
    simpa only [E₀,mul_pow,←pow_mul,mul_assoc] using yes)
  have x₂:=one_le_pow₀ hx (n:=2)
  have expBound : Real.exp ((p.supportExponent+2)*atomTiles S)≤A := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith only [support]) (Nat.cast_nonneg _)
  have sold : atomPrice Y F μ ≤ (1+5*|readPrice Y F|)*x^2 := by
    have scaled : (1+μ)*readPrice Y F≤(5*x^2)*|readPrice Y F| :=
      (mul_le_mul_of_nonneg_left (le_abs_self (readPrice Y F)) (by linarith only [μpos])).trans
        (mul_le_mul_of_nonneg_right (by linarith only [read,x₂]) (abs_nonneg _))
    unfold atomPrice
    nlinarith only [scaled,x₂]
  have fmax : factor Y S p.supportExponent μ≤M := by
    calc
      _ ≤ Real.exp ((p.supportExponent+2)*atomTiles S)*((1+5*|readPrice Y F|)*x^2) :=
        mul_le_mul_of_nonneg_left sold (Real.exp_nonneg _)
      _ ≤ A*((1+5*|readPrice Y F|)*x^2) := mul_le_mul_of_nonneg_right expBound (by positivity)
      _ = F₀*x^2 := (mul_assoc ..).symm
      _ ≤ _ := stage F₀ 2 (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,degree];omega)
  have g₁:=(WilsonCenteredCaptureGeometry.motion p near ({()}:Finset Unit) (by simp)).trans (motion.trans at2)
  have g₂:=(WilsonCenteredCaptureGeometry.motion p near ({false,true}:Finset Bool) (by decide)).trans (motion.trans at2)
  have actual:=WilsonCenteredSlateCeiling.original p S Y w a b s names c Z rad hw one fmax paid emax hk hk1 hv room divided
    g₁ g₂ zmax (wa.trans marks) (wb.trans marks) (pair.trans marks) (first.trans marks) (fun u hu=>(rest u hu).trans marks)
  have length : 0≤∑v∈names,‖c v‖:=sum_nonneg (fun _ _=>norm_nonneg _)
  have widen : 24+5*(∑v∈names,‖c v‖)≤24*(1+∑v∈names,‖c v‖):=by linarith only [length]
  calc
    _ ≤ (24+5*(∑v∈names,‖c v‖))*M^7 := actual
    _ ≤ (24*(1+∑v∈names,‖c v‖))*M^7 := mul_le_mul_of_nonneg_right widen (pow_nonneg (zero_le_one.trans one) _)
    _ = _ := by dsimp [M,B,D];rw [mul_pow,←pow_mul];ring

end YM.Integration.WilsonCenteredPhysicalFare
