import YM.Integration.WilsonIndependentConditionedLocatedCell

/-! Uniform variation of the actual point-sampled compact cover quadrature
and every folding onto original finite lattices. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedLocatedMesh
open Function Set Filter MeasureTheory Metric Extraction Lattice
open scoped Classical Topology BigOperators
variable {n:ℕ}

theorem tiles {X:Set (Points n)}(compact:IsCompact X){δ:ℝ}(hp:0<δ)(fit:(4*n:ℝ)*δ≤1)
    (film:Finset (Fin n → Cover))(seen:∀o∈film,tag δ o∈X):
    (film.card:ℝ)*δ^(4*n)≤volume.real (cthickening 1 X):=by
  let zone:=cthickening 1 X
  have born(o:Fin n → Cover):volume.real (segment δ o)=δ^(4*n):=by
    rw [Measure.real,cell_volume hp,ENNReal.toReal_ofReal (pow_nonneg hp.le _)]
  have disj:Set.PairwiseDisjoint (film:Set (Fin n → Cover)) (segment δ):=by
    intro a _ b _ diff
    refine Set.disjoint_left.2 fun x hx hy=>?_
    exact diff (hx.symm.trans hy)
  have routed:(⋃o∈film,segment δ o)⊆zone:=by
    intro x hx
    obtain ⟨o,mem,hx⟩:=mem_iUnion₂.mp hx
    have dist₀:=approximate hp x
    rw [show address δ x=o from hx] at dist₀
    exact mem_cthickening_of_dist_le _ _ _ _ (seen o mem) ((dist_comm x _).trans_le (dist₀.trans fit))
  have bound:=measureReal_mono (μ:=volume) routed compact.cthickening.measure_lt_top.ne
  rw [measureReal_biUnion_finset disj (fun o _=>measurable_segment hp o) (fun o _=>by rw [cell_volume hp];exact ENNReal.ofReal_ne_top)] at bound
  simpa only [born,Finset.sum_const,nsmul_eq_mul] using bound

theorem samples {X:Set (Points n)}(compact:IsCompact X){δ M:ℝ}(hp:0<δ)(fit:(4*n:ℝ)*δ≤1)
    (film:Finset (Fin n → Cover))
    (mode:(Fin n → Cover) → ℂ)(supported:∀o∈film,mode o≠0→tag δ o∈X)
    (mp:0≤M)(cap:∀o∈film,‖mode o‖≤M):
    ∑o∈film,‖((δ^(4*n):ℝ):ℂ)*mode o‖≤M*volume.real (cthickening 1 X):=by
  classical
  let living:=film.filter fun o=>mode o≠0
  have live(o)(h:o∈living):=Finset.mem_filter.mp h
  have count:=tiles compact hp fit living (fun o h=>supported o (live o h).1 (live o h).2)
  calc
    _=∑o∈living,‖((δ^(4*n):ℝ):ℂ)*mode o‖:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset ..)
      intro o hf dead
      have zero:mode o=0:=by
        by_contra non
        exact dead (Finset.mem_filter.mpr ⟨hf,non⟩)
      simp only [zero,mul_zero,norm_zero]
    _≤∑_o∈living,δ^(4*n)*M:=by
      apply Finset.sum_le_sum
      intro o member
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hp.le _)]
      exact mul_le_mul_of_nonneg_left (cap o (live o member).1) (pow_nonneg hp.le _)
    _≤_:=by simpa only [Finset.sum_const,nsmul_eq_mul] using
      (show (living.card:ℝ)*(δ^(4*n)*M)≤M*volume.real (cthickening 1 X) from by
        rw [←mul_assoc,mul_comm _ M];exact mul_le_mul_of_nonneg_left count mp)
end YM.Integration.WilsonIndependentConditionedLocatedMesh
end
