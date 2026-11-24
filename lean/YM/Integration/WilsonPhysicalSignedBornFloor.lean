import YM.Integration.WilsonPositionProgramPublicWickGram

/-! Uniform real positivity for the entire uncentered reflected public packet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalSignedBornFloor
open Filter Function Set Finset WilsonPositionProgramPublicContrast WilsonPositionProgramPublicQuadratic
open scoped Topology Classical BigOperators Matrix ComplexOrder
variable {I:Type}[Fintype I]

theorem real_form (q:I→I→ℂ)(pd:(Matrix.of q).PosDef)(x:I→ℂ):
    ‖assay x x q‖=(assay x x q).re:=by
  by_cases zero:x=0
  · simp [zero,assay]
  have eqn:assay x x q=star x ⬝ᵥ (Matrix.of q *ᵥ x):=by
    simp only [assay,dotProduct,Matrix.mulVec,Matrix.of_apply,Pi.star_apply,mul_sum]
    exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>by ring
  have pos:0<assay x x q:=eqn ▸ pd.dotProduct_mulVec_pos zero
  obtain ⟨hp,hi⟩:=Complex.pos_iff.mp pos
  have pinned:assay x x q=((assay x x q).re:ℂ):=Complex.ext rfl (by simpa using hi.symm)
  calc
    _=‖((assay x x q).re:ℂ)‖:=congrArg norm pinned
    _=_:=by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]

theorem neighborhood (q:I→I→ℂ)(pd:(Matrix.of q).PosDef):
    ∃k δ:ℝ,0<k ∧ 0<δ ∧ ∀p:I→I→ℂ,‖p-q‖≤δ →
      ∀x:I→ℂ,k*‖x‖^2≤(assay x x p).re:=by
  obtain ⟨K,hK,original⟩:=gap q pd
  let n := (Fintype.card I:ℝ)
  let D := (1+n)^2
  have hn : 0≤n := Nat.cast_nonneg _
  have dp : 0<D := by dsimp [D]; positivity
  refine ⟨K/2,K/(2*D),half_pos hK,by positivity,?_⟩
  intro p paid x
  have hcharge : charge x ≤ (1+n)*‖x‖ := (charged x).trans <|
    mul_le_mul_of_nonneg_right (by dsimp [n]; linarith) (norm_nonneg _)
  have miss : ‖assay x x p-assay x x q‖ ≤ (K/2)*‖x‖^2 := by
    rw [← subtracted]
    calc
      _ ≤ charge x*charge x*‖p-q‖ := price .. 
      _ ≤ ((1+n)*‖x‖)*((1+n)*‖x‖)*(K/(2*D)) := by
        apply mul_le_mul _ paid (norm_nonneg _) (by positivity)
        exact mul_le_mul hcharge hcharge (Finset.sum_nonneg fun _ _=>norm_nonneg _) (by positivity)
      _ = _ := by dsimp [D]; field_simp
  have held:=Complex.re_le_norm (assay x x q-assay x x p)
  rw [norm_sub_rev] at held
  rw [Complex.sub_re] at held
  have src:=original x
  rw [real_form q pd x] at src
  linarith

open Function Set Filter Finset Lattice Labels Maxwell Maxwell.Free Maxwell.Wick MS MS.Menus MS.Land MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 Local.Physical Extra Extra.FD
open WilsonPositionProgramPublicQuadratic WilsonPositionProgramPublicContrast WilsonPositionProgramPublicWickGram
variable {G:Gauge}{d:ℕ}{B:Local.Physical.Deck G}
theorem original (a:Axis)(leg:I→Glyph B d)(independent:Injective leg):
    ∃k δ:ℝ,0<k ∧ 0<δ ∧ ∀p:I→I→ℂ,‖p-reading a (nodes a) leg‖≤δ →
      ∀x:I→ℂ,k*‖x‖^2≤(assay x x p).re:=by
  have distinct : vertex a ≠ -(vertex a) := by
    intro eq
    have zero := apart a
    have same : vertex a - (-(vertex a)) = 0 := sub_eq_zero.mpr eq
    rw [same] at zero
    have bad := congrArg norm zero
    simp [basis_norm] at bad
  have identity : Matrix.of (reading a (nodes a) leg) =
      Matrix.of (fun i j => duplex (vertex a) (-(vertex a)) (Letters B (leg j)) (Letters B (leg i))) := by
    ext i j
    exact (observed a leg i j).symm
  apply neighborhood
  rw [identity]
  exact FD.reflected_pd distinct _ ((illumined B d).comp leg independent)


end YM.Integration.WilsonPhysicalSignedBornFloor
