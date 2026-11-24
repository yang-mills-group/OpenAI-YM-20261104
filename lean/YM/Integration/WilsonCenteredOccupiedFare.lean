import YM.Integration.WilsonCenteredAllMaskCeiling
import YM.Integration.WilsonCenteredPhysicalFare

/-! Cost of any fixed occupied mask on a genuine reporting halo. Each original
marker is paid at its purchased width before the angular orders are chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredOccupiedFare
open Finset Function Lattice RG Wilson Marker QuadraticLocal Ac Source Labels Push.Local
open Planned.GuardedAtom Extra.Trajectories WilsonCenteredFiledAtoms WilsonCenteredPhysicalFare
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {R : Census V}
  {d : ℕ} {F : Frame G d}

theorem original (p : BudgetPoint) (S : SectionData F) (Y : Hol G) (w : V→ℝ)
    (s : R.Mode) (names : Finset V) (c : V→ℂ) (Z : Support n) (y : Site n) (rad seats width r : ℕ)
    {E κ η μ x W α : ℝ} (hw : ∀j,0<w j) (hx : 1≤x) (hW : 0≤W) (load : s.val.card≤r)
    (support : p.supportExponent≤α) (near : rad≤p.B) (house : Z⊆halo p.B {y})
    (hk : 0<κ) (hk1 : κ≤1) (hv : 0≤η) (room : hitWidth p*η≤1) (divided : hitWidth p*η/κ≤1)
    (motion : WilsonReportRetainedAnchor.reprice p p.B≤2*x^2)
    (paid : 0≤E) (income : E≤25*(2*x^2)^(seats+1)) (μpos : 0≤μ) (read : μ≤4*x^2)
    (weights : ∀t:R.Mode,t.val⊆s.val→(Poly.toll w t)⁻¹≤W*x^width)
    (named : ∀j∈names,(Poly.toll w (R.fire j))⁻¹≤W*x^width) :
    WilsonCenteredGalleryCapture.fare p S Y w s names c Z rad E κ η μ≤
      (1+∑j∈names,‖c j‖)*(WilsonCenteredAllMaskCeiling.scale r*(WilsonCenteredPhysicalFare.base S Y α W seats)^(3*r+9))*
        x^(WilsonCenteredPhysicalFare.degree seats width*(3*r+9)) :=by
  let D:=WilsonCenteredPhysicalFare.degree seats width
  let B:=WilsonCenteredPhysicalFare.base S Y α W seats
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
  have at2 : 2*x^2≤M:=stage _ 2 (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,WilsonCenteredPhysicalFare.degree];omega)
  have marks:=stage W width (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,WilsonCenteredPhysicalFare.degree];omega)
  have zmax : Real.exp ((p.supportExponent+2)*coverNumber p.B Z)≤M :=
    (WilsonCenteredCaptureGeometry.cover p Z y house support).trans (by
      simpa only [pow_zero,mul_one] using stage Z₀ 0 (by linarith only [identity,hW,Zpos,Fpos,Epos]) (Nat.zero_le _))
  have emax : E≤M := income.trans (by
    have yes:=stage E₀ (2*(seats+1)) (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,WilsonCenteredPhysicalFare.degree];omega)
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
      _ ≤ _ := stage F₀ 2 (by linarith only [identity,hW,Zpos,Fpos,Epos]) (by dsimp [D,WilsonCenteredPhysicalFare.degree];omega)
  have cost:=WilsonCenteredAllMaskCeiling.original p S Y w hw s names c Z rad r load near one fmax paid emax hk hk1
    hv room divided (motion.trans at2) zmax (fun t ht=>(weights t ht).trans marks) (fun j hj=>(named j hj).trans marks)
  simpa only [M,B,D,mul_pow,←pow_mul,mul_assoc] using cost

end YM.Integration.WilsonCenteredOccupiedFare
