import YM.MSbar.Grid.Real
/-! Cancel all sewing consistency assumptions in integer d dimensions. (Nonphysical integer
dimensions used only algebraically before transfer.) -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Loops
open Function Set MeasureTheory Metric Filter Dim
open scoped Topology BigOperators Classical ENNReal
namespace Snap

lemma euclidean (d : ℕ): Nonempty (Snap (EuclideanSpace ℝ (Fin d)) volume):=by
   induction d with
   | zero =>
      let E:= EuclideanSpace ℝ (Fin 0);change Nonempty (Snap E volume)
      let U(n:ℕ):AddSubgroup E:=⊤
      refine ⟨⟨U,fun _=>{(0:E)},fun _=>1,fun _=>zero_le_one,fun _=> id,fun _ _=> Set.mem_univ _,fun _ _ _=>Set.mem_univ _,?_,?_,?_,?_,fun _=>tendsto_const_nhds⟩⟩
      · intro K h; exact Eventually.of_forall fun _ v _=> Finset.mem_singleton.mpr (Subsingleton.elim ..)
      · intro K h; exact ⟨K,h,Eventually.of_forall fun n=> Subset.refl _⟩
      · intro n i hi; simp
      intro n i hi; change volume _=_;rw [volume_euclideanSpace_eq_dirac]; simp [Subsingleton.elim i 0]
   | succ d ih =>
      let E:= EuclideanSpace ℝ (Fin d); let F:=EuclideanSpace ℝ (Fin (d+1)); let L:= WithLp 2 (E × ℝ)
      let A := WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ
      have h : Module.finrank ℝ F=Module.finrank ℝ L := by rw [A.toLinearEquiv.finrank_eq]; simp [E,F,Module.finrank_prod]
      let e:=((stdOrthonormalBasis ℝ L).equiv (stdOrthonormalBasis ℝ F) (finCongr h.symm))
      let B: (E × ℝ) ≃L[ℝ] F:= A.symm.trans e.toContinuousLinearEquiv
      obtain ⟨V⟩:= ih; obtain ⟨W⟩:= supported; obtain ⟨Z⟩:=V.prod W
      exact Z.lifts B.toLinearEquiv.toAddEquiv B.continuous B.symm.continuous B.symm.continuous.measurable (e.measurePreserving.comp (WithLp.volume_preserving_toLp E ℝ))
variable {M:Type*} [AddCommGroup M] [MeasurableSpace M] [TopologicalSpace M] {μ:Measure M}
lemma mass (B:Snap M μ) (q : ℝ) (hq:0 ≤ q): Nonempty (Snap M (ENNReal.ofReal q • μ)):= by
    refine ⟨{ clan:=B.clan,layer:=B.layer, δ:=fun i=> q*B.δ i, nonneg:= fun i=>mul_nonneg hq (B.nonneg _), snap:=B.snap, mem:=B.mem, sub:=B.sub, eventually:=B.eventually, cover:=B.cover, knows:=B.knows, seq:= B.seq, plays:= fun n i hi=>by rw [Measure.smul_apply, B.plays n i hi, smul_eq_mul, ENNReal.ofReal_mul hq] }⟩
end Snap
end YM.MSbar.Loops
