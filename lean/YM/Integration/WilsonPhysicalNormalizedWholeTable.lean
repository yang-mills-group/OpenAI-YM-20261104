import YM.Integration.WilsonPhysicalNormalizedSignedMenu

/-! The complete active public table is priced before any cutoff-dependent bounded physical vector is inserted. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalNormalizedWholeTable
open Filter Function Finset Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionTargetRows WilsonPhysicalNormalizedSignedMenu
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge}{d n:ℕ}{I:Type}{A:Screen G d}(D:Fray A)(H:A.Prepared)(home:Fin n→I)

def fitted (P:I→Prediction G d)(M:Row G d n):Row G d n:=
  M.compLinearMap (fun j=>stand (D.firstPass H (P (home j))))

def cost (v:Fin n→Sec G d):ℝ:=∑ b:Fin n→Pin G d,‖∏ j, tableD G d (v j) (b j)‖

theorem tested (M W:Row G d n)(v:Fin n→Sec G d):
    ‖M v-W v‖≤cost v*‖rows M-rows W‖:=by
  have actual:=medium v ((M-W).restrictScalars ℝ)
  change M v-W v=∑ b:Fin n→Pin G d, (∏ j,tableD G d (v j) (b j)) • (rows M-rows W) b at actual
  rw [actual]
  calc
    _≤∑ b:Fin n→Pin G d,‖(∏ j,tableD G d (v j) (b j)) • (rows M-rows W) b‖:=norm_sum_le _ _
    _≤∑ b:Fin n→Pin G d,‖∏ j,tableD G d (v j) (b j)‖*‖rows M-rows W‖:=by
      apply sum_le_sum
      intro b _
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (rows M-rows W) b) (norm_nonneg _)
    _=cost v*‖rows M-rows W‖:=(sum_mul ..).symm

theorem original {ι:Type*}(u:Filter ι)[Fintype I]:
    ∃ C:ℝ,0<C ∧ ∀ (P Q:ι→I→Prediction G d)(s:ι→I→Change G d)
      (_:∀ h,D.Via (fun i=>P i h) (u:=u))(_:∀h,D.Via (fun i=>Q i h) (u:=u))
      (_:∀h,Tendsto (fun i=>guide G d (s i h)) u (𝓝 0))(M W:ι→Row G d n),
      ∀ᶠ i in u,‖rows (fitted D H home (P i) (M i))-rows (fitted D H home (Q i) (W i))‖≤
        C*(‖rows (M i)-rows (offered home (s i) (W i))‖+
          ‖docket D (P i)-docket D (retag (s i) (Q i))‖*‖rows (offered home (s i) (W i))‖):=by
  let basis (a:Fin n→Pin G d)(j:Fin n):=Module.finBasis ℝ (Sec G d) (a j)
  have sellers:=fun a:Fin n→Pin G d=>WilsonPhysicalNormalizedSignedMenu.original D H home (basis a) u
  choose K hK purchased using sellers
  let C:=1+∑ a:Fin n→Pin G d,K a
  have leC (a:Fin n→Pin G d):K a≤C:=by
    have s:=Finset.single_le_sum (f:=K) (fun b _=>(hK b).le) (Finset.mem_univ a)
    dsimp [C]
    linarith
  have positive:0<C:=by dsimp [C];have:=sum_nonneg (s:=univ) fun a _=>(hK a).le;linarith
  refine ⟨C,positive,?_⟩
  intro P Q s p q near M W
  have allBasis:=Filter.eventually_all.mpr (fun b=>purchased b P Q s p q near M W)
  filter_upwards [allBasis] with i sold
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg positive.le (add_nonneg
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))).mpr
  intro a
  exact (sold a).trans (mul_le_mul_of_nonneg_right (leC a)
    (add_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))))

end YM.Integration.WilsonPhysicalNormalizedWholeTable
