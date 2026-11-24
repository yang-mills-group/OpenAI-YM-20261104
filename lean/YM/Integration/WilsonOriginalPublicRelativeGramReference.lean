import YM.Integration.WilsonOriginalPublicRelativeGramPosted

/-! Reflected coercivity of the full reference panel pays its determinant and
the operator-norm inverse on every direction of the finite label space. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicRelativeGramReference
open Finset Function Matrix Wilson RG Source Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open MS MS.Menus MS.Land MS.Theater Local.Physical
open WilsonPositionProgramPublicContrast (assay)
open WilsonPositionProgramPublicWickGram (reading nodes)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {I:Type}[Fintype I][DecidableEq I]
local notation "n" => (Fintype.card I:ℝ)

theorem eye (M:Matrix I I ℂ)(k:ℝ)(kp:0<k)(bar:∀x:I→ℂ,k*‖x‖^2 ≤ ‖assay x x M‖):
    IsUnit M.det ∧ ‖M⁻¹‖ ≤ ∑_i:I,∑_j:I,n/k:=by
  have expr(x:I→ℂ):assay x x M=∑i,star (x i)*(M*ᵥx) i:=by
    unfold assay Matrix.mulVec dotProduct
    apply sum_congr rfl
    intro i _
    rw [mul_sum]
    exact sum_congr rfl fun j _=>by ring
  have lower(x:I→ℂ):k*‖x‖ ≤ n*‖M*ᵥx‖:=by
    by_cases hx:x=0
    · simp [hx]
    have xp:=norm_pos_iff.mpr hx
    have bound:‖assay x x M‖ ≤ n*(‖x‖*‖M*ᵥx‖):=by
      rw [expr]
      calc
        _ ≤ ∑i,‖star (x i)*(M*ᵥx) i‖ := norm_sum_le ..
        _ ≤ ∑_i:I,‖x‖*‖M*ᵥx‖ := by
          refine sum_le_sum fun i _=>?_
          rw [norm_mul,norm_star]
          exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm _ i) (norm_nonneg _) (norm_nonneg _)
        _ = _ := by simp [nsmul_eq_mul]
    apply (mul_le_mul_iff_of_pos_right xp).mp
    calc
      _ = k*‖x‖^2 := by ring
      _ ≤ _ := (bar x).trans bound
      _ = _ := by ring
  have inj:Injective M.mulVec:=by
    intro x y same
    have zero:=lower (x-y)
    rw [Matrix.mulVec_sub,same,sub_self,norm_zero,mul_zero] at zero
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (le_of_not_gt fun h=>(not_lt_of_ge zero) (mul_pos kp h)) (norm_nonneg _)))
  have rank: IsUnit M.det:=(Matrix.isUnit_iff_isUnit_det M).mp (Matrix.mulVec_injective_iff_isUnit.mp inj)
  refine ⟨rank,WilsonOriginalPublicRelativeGramPanel.entry_bound (fun _ _=>n/k) ?_⟩
  intro i j
  have col:M*ᵥ(fun u=>M⁻¹ u j)=fun u=>(1:Matrix I I ℂ) u j:=by
    funext u; change (M*M⁻¹) u j=_
    rw [Matrix.mul_nonsing_inv _ rank]
  have singleton:‖fun u=>(1:Matrix I I ℂ) u j‖ ≤ 1:=by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro u
    change ‖(1:Matrix I I ℂ) u j‖ ≤ 1
    by_cases e:u=j <;> simp [Matrix.one_apply,e]
  have paid:=lower fun u=>M⁻¹ u j
  rw [col] at paid
  apply (le_div_iff₀ kp).mpr
  calc
    _ = k*‖M⁻¹ i j‖ := by ring
    _ ≤ k*‖fun u=>M⁻¹ u j‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun u:I=>M⁻¹ u j) i) kp.le
    _ ≤ n*1 := paid.trans (mul_le_mul_of_nonneg_left singleton (by positivity))
    _ = _ := mul_one _

theorem original {G:Gauge}{B:Local.Physical.Deck G}{h:ℕ}(a:Axis)(leg:I→Glyph B h)(independent:Injective leg):
    ∃ k δ:ℝ,0<k ∧ 0<δ ∧ ∀M:Matrix I I ℂ,
      ‖(fun i j=>M i j)-reading a (nodes a) leg‖ ≤ δ →
      IsUnit M.det ∧ ‖M⁻¹‖ ≤ ∑_i:I,∑_j:I,n/k:=by
  obtain ⟨k,δ,kp,dp,pass⟩:=WilsonPositionProgramPublicWickGram.original a leg independent
  exact ⟨k,δ,kp,dp,fun M near=>eye M k kp (pass (fun i j=>M i j) near)⟩

end YM.Integration.WilsonOriginalPublicRelativeGramReference
