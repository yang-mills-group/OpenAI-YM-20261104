import YM.Integration.WilsonIndependentWardNamedHearing
import YM.Integration.WilsonIndependentMatchedTopWard

/-! Shift through a named peer before coefficient extraction. In particular
the contact term can keep the lower degrees contributed by the Euler variation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentWardRankShift
open Lattice RG Wilson Source Labels PowerSeries PertExtension PertExtension.Orb XSpace FVA2
open FormalOPE.RG10 FormalOPE.RG10.InversionWard
open scoped Classical
variable {G:Gauge}{p:Period}(T:p.Tree)

theorem move (l:ℕ)(A:Bare.Series T G) :
    X^l * Bare.normalized T G A=Bare.normalized T G (X^l*A) := by
  rw [←Bare.normalized_scalar]
  simp [Bare.scalar]

theorem insertion (l:ℕ)(A:Bare.Series T G)(O:Config G p.side→ℝ)
    (ranked:X^l*A=BareOrb.stencil T O)(M:Bare.Series T G) :
    X^l*Bare.normalized T G (M*A)=Bare.normalized T G (M*BareOrb.stencil T O) := by
  rw [move T,←ranked]
  apply congrArg (Bare.normalized T G)
  ring

theorem earned (l:ℕ)(A:Bare.Series T G)(O:Config G p.side→ℝ)
    (ranked:X^l*A=BareOrb.stencil T O)(b:Edge (Site p.side))(Z:Config G p.side→G.Color)
    (h:Direction b Z)(pro:Proxy O)(valid:PreTest O) :
    X^l*(Bare.normalized T G (BareOrb.stencil T (effort b Z)*A) -
      X^2*Bare.normalized T G (BareOrb.stencil T (fallout b Z)*A)) =
    X^2*Bare.normalized T G (BareOrb.stencil T (coupled b Z O)) := by
  have paired:=WilsonIndependentMatchedTopWard.hearing T b Z h pro valid
  rw [WilsonIndependentMatchedTopWard.force,sub_mul,mul_assoc,map_sub,Bare.normalized_scalar] at paired
  rw [mul_sub,mul_left_comm (X^l) (X^2),
    insertion T l A O ranked,insertion T l A O ranked]
  exact paired

theorem clear (l:ℕ)(A:Bare.Series T G)(O:Config G p.side→ℝ)
    (ranked:X^l*A=BareOrb.stencil T O)(b:Edge (Site p.side))(Z:Config G p.side→G.Color)
    (h:Direction b Z)(pro:Proxy O)(valid:PreTest O){S:Set (Site p.side)}
    (supports:LocalOn S O)(apart:off b S) :
    Bare.normalized T G (BareOrb.stencil T (effort b Z)*A)=
      X^2*Bare.normalized T G (BareOrb.stencil T (fallout b Z)*A) := by
  have paired:=WilsonIndependentMatchedTopWard.silent T b Z h pro valid supports apart
  rw [WilsonIndependentMatchedTopWard.force,sub_mul,mul_assoc,map_sub,Bare.normalized_scalar,
    ←insertion T l A O ranked,←insertion T l A O ranked,←mul_left_comm (X^l) (X^2),←mul_sub] at paired
  exact sub_eq_zero.mp ((mul_eq_zero.mp paired).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero))

theorem coefficients (l q:ℕ)(A B C:PowerSeries ℂ)(h:X^l*(A-X^2*B)=X^2*C) :
    coeff q A - (if 2≤q then coeff (q-2) B else 0) = coeff (l+q) (X^2*C) := by
  have get:=congrArg (coeff (l+q)) h
  simpa [coeff_X_pow_mul',Nat.le_add_right] using get

end YM.Integration.WilsonIndependentWardRankShift
