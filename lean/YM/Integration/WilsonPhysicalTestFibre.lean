import YM.Integration.WilsonPhysicalReturnedTestDirection

/-! Decomposition of a complete four-dimensional K-torus into its real
coordinate lines. Each site contributes once to each directional trace. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalTestFibre
open Function Finset Lattice WilsonSmoothUnitFiniteGrid
open scoped Classical BigOperators
abbrev Slice (n:Side)(a:Axis):={x:Site n//x a=0}

def chart (n:Side)(a:Axis):Slice n a × Per n ≃ Site n where
  toFun y:=Function.update y.1.val a y.2
  invFun x:=(⟨Function.update x a 0,Function.update_self ..⟩,x a)
  left_inv:=by
    rintro ⟨⟨x,h⟩,t⟩
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases same:j=a
      · subst j;simp [h]
      · simp [Function.update_of_ne same]
    · exact Function.update_self ..
  right_inv x:=by
    funext j
    by_cases same:j=a
    · subst j;simp
    · simp [Function.update_of_ne same]

def point4 {n:Side}(left:Axis → ℝ)(h:ℝ)(x:Site n):Four ℝ:=fun a=>point (left a) h (x a)
def line {n:Side}(φ:Four ℝ → ℝ)(left:Axis → ℝ)(h:ℝ)(a:Axis)(y:Slice n a)(t:ℝ):ℝ:=
  φ (Function.update (point4 left h y.val) a t)

theorem atSite {n:Side}(φ:Four ℝ → ℝ)(left:Axis → ℝ)(h:ℝ)(a:Axis)(y:Slice n a)(z:Per n):
    line φ left h a y (point (left a) h z)=φ (point4 left h (chart n a (y,z))):=by
  apply congrArg φ
  funext b
  by_cases same:b=a
  · subst b;simp [point4,chart]
  · simp [point4,chart,Function.update_of_ne same]

theorem total {n:Side}(F:Axis → Site n → ℂ)(E:(a:Axis) → Slice n a → ℝ)
    (prices:∀a y,‖∑t:Per n,F a (chart n a (y,t))‖≤E a y):
    ‖∑x:Site n,∑a:Axis,F a x‖≤∑a:Axis,∑y:Slice n a,E a y:=by
  rw [sum_comm]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro a _
  have grid:(∑y:Slice n a,∑t:Per n,F a (chart n a (y,t)))=∑x:Site n,F a x:=by
    simpa only [Fintype.sum_prod_type] using Equiv.sum_comp (chart n a) (F a)
  rw [←grid]
  exact (norm_sum_le _ _).trans (sum_le_sum fun y _=>prices a y)
end YM.Integration.WilsonPhysicalTestFibre
