import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.DCompare

/-! Quantitative admission of an actual Wilson angular curve on each original
support collar.  The constants belong to the compact group, before the
period, the positions, the edges and the observing scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.PlaquetteChart
open Function Filter Metric Set Lattice RG Wilson
open scoped Topology Matrix.Norms.Frobenius
variable {G : Gauge}

theorem slope (G : Gauge) : ∃ C δ : ℝ,0<C ∧ 0<δ ∧ ∀v:G.Color,‖v‖≤δ→
    G.chord (G.lieExp v)≤C*‖v‖ := by
  obtain ⟨C,hC,H⟩ := G.expDiff_zero.isBigO_sub.exists_pos
  obtain ⟨δ,hδ,atZero⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (show {x:G.Color|‖G.mat (G.lieExp x)-G.mat (G.lieExp 0)‖≤C*‖x-(0:G.Color)‖} ∈ 𝓝 0 from H.bound)
  have gpos := G.colorScale_pos
  refine ⟨C/G.colorScale,δ,by positivity,hδ,fun v hv=>?_⟩
  unfold Gauge.chord
  change _/G.colorScale≤_
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ gpos.le
  simpa only [G.mat_lieExp_zero,G.mat_one,Set.mem_setOf_eq,sub_zero] using
    (atZero (mem_closedBall_zero_iff.mpr hv))

/-- Only the actual finite neighbourhood of the named support is used. -/
theorem admitted (G : Gauge) :
    ∃ C δ : ℝ,0<C ∧ 0<δ ∧ ∀{n : Side} (X : Support n) (D : Directions G n)
    (_ : ∀ o∈X,∀q:Face (Per n),o∈touched q→∀e:Edge (Site n),separation q.1 e.1≤4→‖D e‖≤1)
    {s t : ℝ},0≤s→s≤δ→4*C*s≤t→Healthy t X (increment 1 (s • D)) := by
  obtain ⟨C,δ,hC,hδ,edge⟩ := slope G
  refine ⟨C,δ,hC,hδ,?_⟩
  intro n X D unit s t hs hin price
  apply Finset.disjoint_left.mpr
  intro o ho bad
  obtain ⟨q,hq,hot⟩ := (flags_spec _ _ _).1 bad
  have near := AnalyticNext.ConnectedActivity.Aff.near_cost (increment 1 (s • D)) q.1
    (square q.2.val.1 q.2.val.2) (mul_nonneg hC.le hs)
    (fun e he=>by
      have val : ‖s • D e‖≤s := by
        rw [norm_smul,Real.norm_of_nonneg hs]
        exact mul_le_of_le_one_right hs (unit o ho q hq e (by simpa [square] using he))
      change G.chord (G.lieExp (s • D e)*1)≤_
      rw [mul_one]
      exact (edge _ (val.trans hin)).trans (mul_le_mul_of_nonneg_left val hC.le))
  have charged : G.chord (faceValue (increment 1 (s • D)) q)≤4*C*s := by
    simpa [faceValue,square,mul_assoc] using near
  exact (not_lt_of_ge (charged.trans price)) hot

end YM.Integration.WilsonPhysicalMarkedDefect.PlaquetteChart
