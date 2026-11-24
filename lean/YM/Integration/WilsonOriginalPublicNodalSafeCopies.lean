import YM.Integration.WilsonOriginalPublicNodalPhysicalHelper
import YM.RegulatorIR.Centered.View

/-! A common lattice translate of two allowed strides in the certified safe part of the same bare torus. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalSafeCopies
open Lattice RegulatorIR RegulatorIR.Geometry RegulatorIR.Motion RegulatorIR.Centered
open scoped Classical
variable (P:ℝ)(s:ℕ)(y:Cover)

def shift:Cover:=fun i=>⌈(P/8-(y i:ℝ))/(s:ℝ)⌉
def safe:Cover:=y+s • shift P s y

theorem housed (pos:0<s)(space:(s:ℝ) ≤ P/8):
    slide 1 (safe P s y) ∈ court P:=by
  apply inside.mpr
  intro i
  have hs:0 < (s:ℝ):=by exact_mod_cast pos
  let v:=(P/8-(y i:ℝ))/(s:ℝ)
  have up:=Int.le_ceil v
  have low:=Int.ceil_lt_add_one v
  have h1:P/8-(y i:ℝ) ≤ (⌈v⌉:ℝ)*s:=(div_le_iff₀ hs).mp up
  have h2:(⌈v⌉:ℝ)*s < P/8-y i+s:=by
    have t:=mul_lt_mul_of_pos_right low hs
    dsimp [v] at t ⊢
    rwa [add_mul,div_mul_cancel₀ _ hs.ne',one_mul] at t
  change P/8 ≤ (slide 1 (safe P s y)) i ∧ (slide 1 (safe P s y)) i < P/8+P/8
  have coord:(s • shift P s y) i=(s:ℤ)*⌈v⌉:=by
    change s • (⌈v⌉:ℤ)=_
    exact nsmul_eq_mul ..
  simp only [safe,slide_apply,one_mul,Pi.add_apply,Int.cast_add,coord,Int.cast_mul,Int.cast_natCast]
  constructor <;> nlinarith

theorem cushion (pos:0<s)(space:(s:ℝ) ≤ P/8):
    (1/8:ℝ)*P ≤ Spatial.singular P (slide 1 (safe P s y)):=by
  apply rotation _ _ (housed P s y pos space)
  have :0 < (s:ℝ):=by exact_mod_cast pos
  linarith

theorem common (a b:ℕ)(ha:a ∣ s)(hb:b ∣ s):
    ∃x z:Cover,safe P s y=y+a • x ∧ safe P s y=y+b • z:=by
  obtain ⟨c,hc⟩:=ha
  obtain ⟨d,hd⟩:=hb
  exact ⟨c • shift P s y,d • shift P s y,by simp only [safe,←mul_smul,←hc],
    by simp only [safe,←mul_smul,←hd]⟩

end YM.Integration.WilsonOriginalPublicNodalSafeCopies
end
