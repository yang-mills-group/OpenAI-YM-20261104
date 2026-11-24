import YM.Integration.WilsonSeparatedPrefixCellProfile
/-! A compact smooth test occupies finitely many covering-grid cells before either regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCoverCells
open Function Filter Set MeasureTheory Lattice Extraction
open scoped Classical BigOperators Topology
variable {n:ℕ}(φ:Test n)(a r:ℝ)

def cube (o:Fin n→ Cover):Set (Points n):=(fun x=>r • x) ⁻¹' segment a o

def mass (o:Fin n→ Cover):ℂ:=∫x in cube a r o,φ x

theorem visible (positive:0<a)(o:Fin n→ Cover):MeasurableSet (cube a r o):=
  (measurable_segment positive o).preimage (continuous_const_smul r).measurable

theorem finite (positive:0<a):∃nodes:Finset (Fin n→ Cover),∀x:Points n,φ x≠0→address a (r • x)∈nodes:=by
  classical
  obtain ⟨M,_,_,_,shape⟩:=WilsonSeparatedPrefixCellProfile.shape φ
  let I:Finset ℤ:=Finset.Icc ⌈-((abs r)*M)/a⌉ ⌈((abs r)*M)/a⌉
  let Z:Type:=Fin n→Axis→{z:ℤ //z∈I}
  let nodes:Finset (Fin n→ Cover):=Finset.univ.image (fun y:Z=>fun i k=>(y i k).val)
  refine ⟨nodes,?_⟩
  intro x live
  have inside(i:Fin n)(k:Axis):address a (r • x) i k∈I:=by
    have coord:|x i k|≤M:= (PiLp.norm_apply_le (x i) k).trans ((shape x live).1 i)
    have bound:abs (r*x i k)≤(abs r)*M:=by rw [abs_mul];exact mul_le_mul_of_nonneg_left coord (abs_nonneg _)
    apply Finset.mem_Icc.mpr
    change ⌈-((abs r)*M)/a⌉≤⌈(r*x i k)/a⌉ ∧ ⌈(r*x i k)/a⌉≤⌈((abs r)*M)/a⌉
    exact ⟨Int.ceil_mono (div_le_div_of_nonneg_right (abs_le.mp bound).1 positive.le),
      Int.ceil_mono (div_le_div_of_nonneg_right (abs_le.mp bound).2 positive.le)⟩
  exact Finset.mem_image.mpr ⟨(fun i k=>⟨_,inside i k⟩),Finset.mem_univ _,rfl⟩

theorem tested (positive:0<a)(nodes:Finset (Fin n→ Cover))
    (contains:∀x:Points n,φ x≠0→address a (r • x)∈nodes)(D:(Fin n→ Cover)→ℂ):
    φ.applyTo (fun x=>D (address a (r • x)))=∑o∈nodes,mass φ a r o*D o:=by
  classical
  have regular:Integrable (fun x:Points n=>φ x):=φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  let term:=fun o:Fin n→ Cover=>(cube a r o).indicator (fun x=>φ x*D o)
  have split (x:Points n):φ x*D (address a (r • x))=∑o∈nodes,term o x:=by
    by_cases empty:φ x=0
    · simp [term,Set.indicator_apply,empty]
    · rw [Finset.sum_eq_single_of_mem (address a (r • x)) (contains x empty)]
      · exact (Set.indicator_of_mem (s:=cube a r (address a (r • x))) (show x∈_ from rfl) (fun y:Points n=>φ y*D (address a (r • x)))).symm
      · intro o _ ne
        exact Set.indicator_of_notMem (s:=cube a r o) (fun eq=>ne (Eq.symm eq)) _
  unfold Test.applyTo
  simp_rw [split]
  rw [integral_finsetSum _ (fun o _=>(regular.mul_const (D o)).indicator (visible a r positive o))]
  apply Finset.sum_congr rfl
  intro o _
  dsimp only [term,mass]
  rw [integral_indicator (visible a r positive o),integral_mul_const]
  
end YM.Integration.WilsonMeasuredPublicEntranceCoverCells
end
