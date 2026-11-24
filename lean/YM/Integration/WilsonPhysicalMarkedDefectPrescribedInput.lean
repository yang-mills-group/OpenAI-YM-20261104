import YM.Integration.WilsonPhysicalMarkedDefectSource
import YM.QuadraticLocal.Tariff.Measure

/-! The independently filed *dressed* library as a scalar Wilson input.
Its full regulated singleton is measurable and bounded before the cutoff or
volume is seen: the one named source site pays the whole sum, even for
coincident supports and an arbitrary countable collection. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.PrescribedInput
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn Ac
open Push.AbsoluteSums Fusion Fusion.Attached ConnectedActivityE6 MergeProof.Accent MeasureTheory
open scoped Classical BigOperators Topology

variable {G : Gauge} {n : Side} {V ι X : Type} [DecidableEq V] [Fintype V]
variable {Γ : Census V} {P : Rep G n} {A : Passport n V} {w : V→ℝ} {b k σ : ℝ}
variable {B : BudgetPoint} {o : V→Site n}

omit [Fintype V] in
/-- Any requested mode is paid at *one* of its true source roots. This uses
the literal sum of the charged signed occurrence values, not the volume. -/
theorem bound (L : Lamps X ι G B o Γ) (hw : ∀v,0<w v) (ha : 0≤σ) (paid : L.Paid w B.B σ b)
    (s : Γ.Mode) (v : V) (hv : v∈s.val) (x : X) (U : Config G n) :
    ‖(L.log x U).part s‖ ≤ (Poly.toll w s)⁻¹*b := by
  obtain ⟨f,hf,bounds,atRoot⟩ := paid.budget
  have wpos := Poly.worth hw s
  have actual : SumBudget (fun i=>Poly.toll w s * ‖(L.frame i x U).part s‖) b := by
    refine budget_mono (atRoot (o v)) (fun i=>mul_nonneg wpos.le (norm_nonneg _)) ?_
    intro i
    by_cases selected : s=L.mode i
    · have rootHit : o v ∈ L.ground i := L.roots i v (selected ▸ hv)
      rw [if_pos rootHit,Lamps.frame,Poly.part_send,if_pos selected]
      dsimp only
      rw [←selected]
      have amount := L.light_size i x U (bounds i x _ (L.address i).anchor)
      have distance : (1:ℝ)≤Real.exp (σ*coverNumber B.B (L.ground i)) :=
        Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))
      exact (mul_le_mul_of_nonneg_left amount wpos.le).trans
        (le_mul_of_one_le_right (mul_nonneg wpos.le (hf i)) distance)
    · simp only [Lamps.frame,Poly.part_send,if_neg selected,norm_zero,mul_zero]
      exact (atRoot (o v)).1 i
  have cost : SumBudget (fun i=>‖(L.frame i x U).part s‖) ((Poly.toll w s)⁻¹*b) := by
    convert budget_scale (inv_nonneg.mpr wpos.le) actual using 1
    funext i
    simp [wpos.ne']
  have series : Summable (fun i => L.frame i x U) := paid.sums ha hw x U
  calc
    _ = ‖∑' i,(L.frame i x U).part s‖ := congrArg norm (Poly.share series s)
    _ ≤ ∑' i,‖(L.frame i x U).part s‖ := norm_tsum_le_tsum_norm cost.2.1
    _ ≤ _ := cost.2.2

omit [Fintype V] in
/-- Real/imaginary signed posterior sources are Borel also when the
engineering catalogue repeats its independently entered supports. -/
theorem measurable [Countable ι] (L : Lamps X ι G B o Γ) (hw : ∀v,0<w v) (ha : 0≤σ)
    (paid : L.Paid w B.B σ b) (s : Γ.Mode) (x : X) :
    Measurable (fun U=>(L.log x U).part s) := by
  have stack : (fun U=>(L.log x U).part s)=
    fun U=>∑' i, (L.frame i x U).part s := by
    funext U;exact Poly.share (paid.sums ha hw x U) s
  rw [stack]
  apply Measurable.tsum
  intro i
  unfold Lamps.frame
  simp only [Poly.part_send]
  split
  · unfold Lamps.light; split
    · exact (L.legal x i).borel
    · exact masked_measurable _ _ _ (L.legal x i).borel
  · exact measurable_const

/-- The true prior Wilson vacuum, including every unmarked partner, is
preserved. The measured ratio is exactly the completely dressed approved
logarithm at the physical coupling on every field. -/
theorem original [Countable ι] (M : ι→Row A Γ G X) (hw : ∀v,0<w v) (ha : 0≤σ)
    (paid : (rendered M P.p (Coat.gStep P.beta)).Paid w P.p.B σ b)
    (hard : Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
    (positive : ∀U,0<P.eval U) (v : V) (x : X) :
    let E := Tint.Patrol.picture M (modelInput A P Γ X hard)
    let φ := fun U=>((E.density x U).part (Γ.fire v))/(P.eval U:ℂ)
    Measurable φ ∧ (∀U,φ U=((rendered M P.p (Coat.gStep P.beta)).log x U).part (Γ.fire v)) ∧
      ∀U, ‖φ U‖ ≤ (w v)⁻¹*b := by
  dsimp only
  have eq (U : Config G n) :
      ((Tint.Patrol.picture M (modelInput A P Γ X hard)).density x U).part (Γ.fire v)/(P.eval U:ℂ) =
      ((rendered M P.p (Coat.gStep P.beta)).log x U).part (Γ.fire v) := by
    have hsum := paid.sums ha hw x U
    have nz : (P.eval U:ℂ)≠0 := by exact_mod_cast (positive U).ne'
    rw [model_input_field M hard hw x U hsum,Poly.part_smul,
      whisper Γ _ (Lamps.quiet_of_hasSum x U hsum) v,mul_div_cancel_left₀ _ nz]
  refine ⟨?_,eq,fun U=>?_⟩
  · have same : (fun U=>((Tint.Patrol.picture M (modelInput A P Γ X hard)).density x U).part (Γ.fire v)/(P.eval U:ℂ)) =
        (fun U=>((rendered M P.p (Coat.gStep P.beta)).log x U).part (Γ.fire v)) := funext eq
    rw [same]
    exact measurable _ hw ha paid (Γ.fire v) x
  · rw [eq];simpa [Poly.toll,Census.fire] using
      bound _ hw ha paid (Γ.fire v) v (by simp [Census.fire]) x U

end YM.Integration.WilsonPhysicalMarkedDefect.PrescribedInput
