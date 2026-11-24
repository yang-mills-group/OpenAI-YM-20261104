import YM.Contact.Trial
import YM.Euclid.Stress

/-! Finite-dimensional physical orbit averages for the full Euclidean rotation group.
No identification of rotation-averaged continuation data at coincident points. -/

noncomputable section
set_option autoImplicit false
open Set Filter Function MeasureTheory TopologicalSpace
open scoped Matrix.Norms.Frobenius Topology ContDiff BigOperators ENNReal
namespace YM.Contacts

theorem ortho_compact : CompactSpace Ortho :=by
  refine isCompact_iff_compactSpace.mp ((isCompact_closedBall (0:M4) 2).of_isClosed_subset isClosed_unitary ?_)
  rintro A h
  have hv : ‖A‖^2 = (A*star A).trace := by
    -- As in YM.Work.A15.sq_frobenius
    rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
    · simp_rw [Real.rpow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
        Real.norm_eq_abs, sq_abs, pow_two]
    simp_rw [Real.rpow_two]
    exact Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>sq_nonneg _
  rw [Metric.mem_closedBall,dist_zero_right]; rw [Matrix.mem_unitaryGroup_iff.mp h,Matrix.trace_one] at hv
  norm_num at hv; nlinarith
scoped instance : CompactSpace Ortho:=ortho_compact
scoped instance : SecondCountableTopology Ortho:=by
  haveI : SecondCountableTopology M4 := inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
  exact inferInstanceAs (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ : Set M4)))
scoped instance : MeasurableSpace Ortho := borel Ortho
scoped instance : BorelSpace Ortho := ⟨rfl⟩

private def orthoSet : PositiveCompacts Ortho:=⟨⟨univ,isCompact_univ⟩,by simp⟩
/-- Normalized Haar (Euclidean rotations, not the gauge group). -/
def spins : Measure Ortho := Measure.haarMeasure orthoSet
scoped instance : spins.IsHaarMeasure := by unfold spins; infer_instance
scoped instance : IsProbabilityMeasure spins:=⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ orthoSet⟩

lemma ortho_movable : Continuous (fun p : Ortho × E4=>Ortho.move p.1 p.2):=by
  change Continuous ((WithLp.toLp 2) ∘ (fun p:Ortho × E4=>fun i:Axis=>∑ j:Axis, p.1.val i j * p.2 j))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi_iff.mpr fun i : Axis=>?_)
  have hv:Continuous (fun p:Ortho× E4=>(p.1.val:Axis→Axis→ℝ)):=continuous_subtype_val.comp continuous_fst
  exact continuous_finsetSum _ fun j _=> (show Continuous (fun p:Ortho×E4=> p.1.val i j) from by
      have hg:Continuous (fun p:Ortho×E4=> p.1.val i):=(continuous_apply i).comp hv;exact (continuous_apply j).comp hg).mul ((PiLp.continuous_apply ..).comp continuous_snd)

variable {G:Gauge}{L:Register G}{S:Table L}
variable {W:DiffPlan S}{R:Table.Rotation S}{H:S.RealSpin}

lemma label_movable (H':R.Laws W H) (d:ℕ): Continuous (fun p:Ortho× S.Field d=> R.act d p.1 p.2):=by
  classical let B:= Module.Free.chooseBasis ℂ (S.Field d)
  have he (p:Ortho × S.Field d): R.act d p.1 p.2 = ∑ i, (B.coord i p.2) • R.act d p.1 (B i) :=by
     conv_lhs=>rw [← B.sum_repr p.2,map_sum]
     refine Finset.sum_congr rfl fun i _=> (R.act d p.1).map_smul ..
  simp_rw [he]; exact continuous_finsetSum _ fun i _=> ((B.coord i).continuous_of_finiteDimensional.comp continuous_snd).smul ((H'.spin d (B i)).comp continuous_fst)

lemma integrate_orbit {d:ℕ}(fun':Ortho→S.Field d) (h:Continuous fun'): Integrable fun' spins:= h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma left_mean {d:ℕ}(K:Ortho)(fun':Ortho→S.Field d): (∫ g:Ortho,fun' (K*g) ∂spins)= ∫ g:Ortho,fun' g ∂spins:=
    (measurePreserving_mul_left spins K).integral_comp (Homeomorph.mulLeft K).measurableEmbedding fun'

end YM.Contacts
