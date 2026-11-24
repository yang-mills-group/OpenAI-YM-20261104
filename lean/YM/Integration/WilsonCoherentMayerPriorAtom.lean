import YM.Integration.FundedCurvatureRayTaylor
import YM.Integration.ActualWilsonPacketGerms

/-! Radial Taylor error of the actual complex token in an occupied rendered mode. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorAtom
open Lattice Wilson RG Marker Progress.DirectedRecipe Source Labels LocalComparison
open Comparison.Density.RenderM Comparison.Density.RenderM.Token
open WilsonMeasuredPathTaylor FundedCurvatureRayTaylor
open scoped Classical BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge} {V:Type} [DecidableEq V] {n:Side} {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {P:MarkedPackets D G n Γ}
    {p:BudgetPoint} {ad:V→Support n}
    {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w:V→ℝ} {g width bank:ℝ} {off slope:ℕ}
    (H:P.Paid p ad region w g width bank off slope)

def fee (width A:ℝ) (j:ℕ) (t:ℝ):ℝ:=(2*A*|t|/width)^(j+1)

def print {k:ℕ} (T:Token G n (fun v=>(D v).Mood) k) (x:TestSpace D)
    (a:Directions G n) (j:ℕ) (t:ℝ):ℂ:=
  polynomial (T.re x) T.root a j t + Complex.I * polynomial (T.im x) T.root a j t

theorem charge {length fall:ℕ} (h:length≤fall) {width A:ℝ} (hw:0<width) (ha:0≤A) (j:ℕ) (t:ℝ):
    bill length A j t ≤ Real.exp (width*fall)*fee width A j t:=by
  have hf:0<((j+1).factorial:ℝ):=by exact_mod_cast Nat.factorial_pos _
  have base:=Real.pow_div_factorial_le_exp (width*(length:ℝ)) (by positivity) (j+1)
  have factor:0≤fee width A j t:=by unfold fee;positivity
  have hle:Real.exp (width*(length:ℝ))≤Real.exp (width*(fall:ℝ)):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast h) hw.le)
  calc
    _ = (width*(length:ℝ))^(j+1)/((j+1).factorial:ℝ)*fee width A j t:=by
      unfold bill fee
      rw [←mul_pow,div_mul_eq_mul_div,←mul_pow]
      congr 2
      field_simp
    _ ≤ _:=mul_le_mul_of_nonneg_right (base.trans hle) factor

include H in
theorem purchased {i:ℕ} {T:Token G n (fun v=>(D v).Mood) (P.rank i)} (ht:P.packet i=some T)
    (x:IndependentTests D) (a:Directions G n) {A:ℝ} (ha:0≤A)
    (available:∀e,speed a e≤A) (j:ℕ) (t:ℝ):
    ‖T.read (testInclusion D x) (field a t)-print T (testInclusion D x) a j t‖≤
      (2*fee width A j t)*(T.coin*Real.exp (width*T.fall)):=by
  let z:=testInclusion D x
  have hm:=(H.coefficient i T ht).2 x
  have r:(T.re z).magnitude≤T.coin:=(Finset.sum_le_sum
    (fun j _=>Complex.abs_re_le_norm (T.gem j z))).trans hm
  have im:(T.im z).magnitude≤T.coin:=(Finset.sum_le_sum
    (fun j _=>Complex.abs_im_le_norm (T.gem j z))).trans hm
  have hl: (T.re z).length≤T.fall:=(H.paths i T ht z).1
  have hb:=charge hl H.width_pos ha j t
  have hmag:0≤bill (T.re z).length A j t:=by unfold bill;positivity
  have hR:=original (T.re z) T.root a ha (fun _ e _=>available e) j t
  have hI:=original (T.im z) T.root a ha (fun _ e _=>available e) j t
  have cost:=mul_le_mul_of_nonneg_left hb (H.coefficient i T ht).1
  have step (c:ℂ):‖Complex.I*c‖=‖c‖:=by simp
  change ‖T.read z _-print T z a j t‖≤_
  rw [T.reading z]
  change ‖((T.re z).unmasked (field a t) T.root:ℂ)+Complex.I*((T.im z).unmasked (field a t) T.root:ℂ) -
    (polynomial (T.re z) T.root a j t + Complex.I*polynomial (T.im z) T.root a j t)‖≤_
  rw [show ∀u v y z:ℂ,u+Complex.I*v-(y+Complex.I*z)=(u-y)+Complex.I*(v-z) from fun _ _ _ _=>by ring]
  apply (norm_add_le ..).trans
  rw [step]
  calc
    _ ≤ T.coin*(Real.exp (width*T.fall)*fee width A j t)+T.coin*(Real.exp (width*T.fall)*fee width A j t):=
      add_le_add (hR.trans ((mul_le_mul_of_nonneg_right r hmag).trans cost))
        (hI.trans ((mul_le_mul_of_nonneg_right im hmag).trans cost))
    _ = _:=by ring

end YM.Integration.WilsonCoherentMayerPriorAtom
