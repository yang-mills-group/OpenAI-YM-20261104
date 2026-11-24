import YM.Trace2.Quota
import YM.Next.MAXWELL.Beacon
import YM.Pert.Scale.ScaleStress

/-!
RG13: Work using *signed* covariance only in moving frames (cf. Trace2/Quota).
Pay unit loss by exact centering; pull the invariant even scalar to the canonical
space using the same `Spin.morph` representation in Final, **not** a rotation
hypothesis at every UV scale. This also makes mixed offaxis comparisons possible
with no derivative estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.FrontierTrace
open Function Filter Set Analysis Trace Maxwell Maxwell.Free
open UVNext.FreeStress Next.UVStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {G:Gauge} (L:Labels.Frames G)

private lemma dot_preserved (f:Axis→G.Color) (g:Axis→G.Color) (U:Ortho) :
    (∑ i:Axis, ⟪∑ k:Axis,U.val i k • f k, ∑ k:Axis,U.val i k • g k⟫_ℝ) =
    ∑ k:Axis, ⟪f k, g k⟫_ℝ := by
  simp_rw [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,←mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp_rw [←Finset.sum_mul,Maxwell.Free.col_dot]
  simp

private lemma frobenius {A : TaylorTower G} (U:Ortho) :
    (∑ i:Axis,∑ j:Axis,⟪asWave (solutionTurn U (A 0)) i j 0,
             asWave (solutionTurn U (A 0)) i j 0⟫_ℝ) =
      ∑ i:Axis,∑ j:Axis, ⟪asWave (A 0) i j 0, asWave (A 0) i j 0⟫_ℝ := by
   let f := fun i j => asWave (A 0) i j 0
   let F := fun i h=> ∑ k:Axis, U.val i k • f k h
   have ht i j : asWave (solutionTurn U (A 0)) i j 0 =
        ∑ h:Axis, U.val j h • F i h := by
      simp_rw [rot_wave, fieldTurn, F, f, Finset.smul_sum, smul_smul,
        show Ortho.move U⁻¹ 0=0 from map_zero (Ortho.motion U⁻¹)]
      rw [Finset.sum_comm];
      apply Finset.sum_congr rfl
      intro h _
      simp_rw [mul_comm _ (U.val j h)]
   simp_rw [ht]
   have h(i:Axis): (∑ j:Axis, ⟪∑ k:Axis, U.val j k • F i k, ∑ k:Axis, U.val j k • F i k⟫_ℝ)= ∑ j:Axis, ⟪F i j,F i j⟫_ℝ := dot_preserved (F i) (F i) U
   simp_rw [h]
   rw [Finset.sum_comm, Finset.sum_comm (f:=fun (i j:Axis) => inner ℝ (f i j) (f i j))]
   exact Finset.sum_congr rfl (fun j _=> dot_preserved (fun i=>f i j) (fun i=>f i j) U)

theorem scalar_ortho (U:Ortho) : (gear L).act 4 U (scalarLabel L) = scalarLabel L := by
   apply address_inj L 4
   rw [paints_gear, scalar_address]
   apply equalPol; intro A
   rw [reflects_eval]
   simp only [actionScalar,sheetEnergy,map_smul,map_sum,measure_phi,←Complex.ofReal_sum]
   rw [frobenius]

theorem scalar_signed (g:Signed) : (freeTable L).mirror (spin_free L) 4 g (scalarLabel L)=scalarLabel L := by
   rw [← (gear_laws L).signed]; exact scalar_ortho ..

lemma scalar_as_total : scalarLabel L = (4:ℝ)⁻¹ • total L := by rw [scalar_actual]; module

lemma scalar_real : (Model L).conj (spin_free L) 4 (scalarLabel L)=scalarLabel L := by
   rw [scalar_as_total]; have he : (Model L).conj (spin_free L) 4 (total L)=total L:= by
     change (Model L).conj _ _ (∑ i:Axis,panel L i i)= _
     simp_rw [map_sum, panel_star]; rfl
   rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smulₛₗ, he]
   apply congrArg (fun z:ℂ=> z • total L)
   exact Complex.conj_ofReal _

/-- There are two real H-invariant fields (span of unit and scalar rank-2).
For the bound we need that centering removes one. This uses raw tensors from
FREE_STRESS_CERTIFICATE; no matching assumption. -/
theorem center_fixed_dim {v : (freeTable L).Field 4} (hg:G.Simple)
    (hv : ∀ g:Signed,(Model L).mirror (spin_free L) 4 g v=v)
    (hr : (Model L).conj (spin_free L) 4 v=v) :
    ∃ a:ℝ, centering (Model L) 4 v=a • scalarLabel L := by
   let J:=centering (Model L) 4 v
   let X:=splitDiag L (fun _=>J)
   have hX : X ∈ KernelSpace (spin_free L) := by
     refine diagonal_kernel L (spin_free L) _ (fun s _=>?_) (fun _=>?_) (fun _=> centers_field (Maxwell.Free.hierarchy L).laws v)
     · unfold J; rw [mirror_center (Maxwell.Free.hierarchy L), hv]
     unfold J; rw [conj_center (Maxwell.Free.hierarchy L), hr]
   obtain ⟨a,b,c,H⟩:= exhaust L (spin_free L) hg (⟨X,hX⟩:KernelSpace _)
   have hh := paint_sum_any (F:=L) a b c
   rw [← H, scalar_actual] at hh
   change (∑ i:Axis, X i i)=(a+2*b) • (4:ℝ) • scalarLabel L at hh
   have he : (4:ℝ) • J = (a+2*b) • (4:ℝ) • scalarLabel L := by
     rw [show (∑ i:Axis,X i i)=(4:ℝ) • J from ?_] at hh; exact hh
     simp only [X,splitDiag,if_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
     rw [← Nat.cast_smul_eq_nsmul ℝ]; norm_num
   rw [smul_comm (a+2*b)] at he
   exact ⟨a+2*b,smul_right_injective _ (by norm_num : (4:ℝ) ≠ 0) he⟩

open Spec
section Actual
variable {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (F:Final C f S)
/-- Obtained where the Final-sector turns are built (no comparison needed).
Suffices at weight four. Doesn't assert that Φ (constant) sends unit to unit,
because `Tab/mill` didn't require that. -/
def ExactTurns : Prop := ∃ Φ:Spin.change S 4, Spin.realH F.room.kernel.spin (spin_free C.labels) Φ ∧
   ∀ g:Ortho, ∀ u, F.sector.turns.act 4 g (Φ u)=Φ ((gear C.labels).act 4 g u)

variable {v:S.Field 4} (Q : Spin.change S 4)
theorem actual_ortho (he:ExactTurns F) (hg:G.Simple) (hv : ∀ g:Signed, S.mirror F.room.kernel.spin 4 g v=v)
    (hw:S.conj F.room.kernel.spin 4 v=v) : ∀ g:Ortho,F.sector.turns.act 4 g v=v := by
   intro g; obtain ⟨U,hR,hU⟩:= he; obtain ⟨u,rfl⟩:=U.surjective v
   rw [hU]; apply congr_arg U
   obtain ⟨a,H⟩:=center_fixed_dim C.labels hg (v:=u)
      (fun s=> U.injective ((hR.1 s u).trans (hv s))) (U.injective ((hR.2 u).trans hw))
   let L:= C.labels
   have he : u=a • scalarLabel L + expectation _ _ u • (Model L).unit 4 := sub_eq_iff_eq_add.mp H
   apply Eq.trans (congr_arg (fun v=>(gear L).act 4 g v) he)
   conv_rhs=> rw [he]
   rw [map_add,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,map_smul,scalar_ortho,(gear_laws L).identity]

end Actual
end YM.FrontierTrace
