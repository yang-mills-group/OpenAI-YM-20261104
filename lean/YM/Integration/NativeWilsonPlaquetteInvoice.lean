import YM.CommonPhysical.Plaquette

/-! Global plaquette-chord bounds for the native UV Wilson Taylor remainder
and its actual derivatives on arbitrary original gauge backgrounds. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeWilsonPlaquetteInvoice
open Filter Function Set Metric Lattice Wilson RG Work WilsonStartup Next.Fluctuations
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

/-- The original local Taylor estimate extends to all group-valued plaquettes
and all normalized physical directions, independent of every finite lattice. -/
theorem group (G : Gauge) (J k : ℕ) : ∃ C : ℝ, 0<C ∧
    ∀ (U : Quad.Group G) (a : Fin k → Quad.Dir G), ‖a‖ ≤ 1 →
    ‖Quad.strokes J (List.ofFn a) (Quad.mat U)‖ ≤ C*(G.chord (Quad.read U))^(J+1-k) := by
  obtain ⟨c,b,hc,hb,hlog⟩ := log_chart_cost G
  obtain ⟨v,hv,near⟩ := Quad.unscaled_tail J G k 1
  let E := Metric.closedBall (0 : Fin k → Quad.Dir G) 1 ×ˢ Set.range (@Quad.mat G)
  have hcompact : IsCompact E := (isCompact_closedBall _ _).prod
    (isCompact_range (f:=@Quad.mat G) (by unfold Quad.mat; fun_prop))
  obtain ⟨M,hM⟩ := hcompact.bddAbove_image (Quad.strokes_diff J (G:=G) k).continuous.norm.continuousOn
  let δ := min b c⁻¹
  have hδ : 0 < δ := lt_min hb (inv_pos.mpr hc)
  let big := max 1 M
  have hbig : 0 < big := zero_lt_one.trans_le (le_max_left ..)
  let q := J+1-k
  refine ⟨max (v*c^q) (big/δ^q), (mul_pos hv (pow_pos hc q)).trans_le (le_max_left ..),?_⟩
  intro U a ha
  let y := G.chord (Quad.read U)
  have hy : 0≤y := G.chord_nonneg _
  by_cases hh : y≤δ
  · have hsmall := hlog (Quad.read U) (hh.trans (min_le_left ..))
    have hx : ‖G.plog (Quad.read U)‖ ≤ 1 :=
      hsmall.2.trans ((mul_le_mul_of_nonneg_left (hh.trans (min_le_right ..)) hc.le).trans_eq
        (mul_inv_cancel₀ hc.ne'))
    calc
      _ ≤ v*‖G.plog (Quad.read U)‖^q := near a ha U _ hx hsmall.1
      _ ≤ v*(c*y)^q := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hsmall.2 q) hv.le
      _ = (v*c^q)*y^q := by rw [mul_pow]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) (pow_nonneg hy q)
  · have hm : (a,Quad.mat U) ∈ E := ⟨mem_closedBall_zero_iff.mpr ha,Set.mem_range_self U⟩
    have full : ‖Quad.strokes J (List.ofFn a) (Quad.mat U)‖ ≤ big :=
      (hM (Set.mem_image_of_mem _ hm)).trans (le_max_right ..)
    calc
      _ ≤ big := full
      _ = (big/δ^q)*δ^q := (div_mul_cancel₀ big (pow_ne_zero q hδ.ne')).symm
      _ ≤ (big/δ^q)*y^q := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hδ.le (le_of_not_ge hh) q) (div_nonneg hbig.le (pow_nonneg hδ.le q))
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) (pow_nonneg hy q)

/-- The literal scalar remainder is controlled solely by its plaquette holonomy. -/
theorem unspent (G : Gauge) (J : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ u : G.El,
    ‖WilsonStartup.unspent J u‖ ≤ C*(G.chord u)^(J+1) := by
  obtain ⟨C,hC,h⟩ := group G J 0
  refine ⟨C,hC,fun u => ?_⟩
  let U : Quad.Group G := ![u,1,1,1]
  have hu : Quad.read U = u := by simp [Quad.read,U]
  have hzero : ‖(0 : Fin 0 → Quad.Dir G)‖ ≤ 1 := by rw [norm_zero]; exact zero_le_one
  have e := h U 0 hzero
  simpa only [List.ofFn_zero,Quad.strokes,Function.comp_apply,Quad.read_actual,Quad.tail_actual,
    hu,Nat.sub_zero] using e

/-- Every native left derivative is paid by a power of the true face chord
on the given field, even when arbitrarily many exterior links are large. -/
theorem face (G : Gauge) (J k : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ (n : Side) (p : Cell n)
    (U : Config G n) (a : Fin k → Directions G n), (∀ i j, ‖a i (edges p j)‖ ≤ 1) →
    ‖leftDerivs (leftOver J p) (List.ofFn a) U‖ ≤ C*(G.chord (faceValue U p))^(J+1-k) := by
  obtain ⟨C,hC,h⟩ := group G J k
  refine ⟨C,hC,fun n p U a ha => ?_⟩
  let v : Fin k → Quad.Dir G := fun i => a i ∘ edges p
  have h₀ : ‖v‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i =>
    (pi_norm_le_iff_of_nonneg zero_le_one).mpr (ha i)
  have el : List.ofFn v = (List.ofFn a).map (fun y => y ∘ edges p) := (List.map_ofFn (g:=fun y => y ∘ edges p) (f:=a)).symm
  rw [leftOver_jet,←el,←read_edges]
  exact h (U ∘ edges p) v h₀

/-- Absolute pricing of any finite signed sparse inventory on arbitrary original fields. -/
theorem inventory (G : Gauge) (r : ℕ) : ∃ C : ℝ, 0<C ∧ ∀ (n : Side)
    (A : Finset (Cell n)) (v : Cell n → ℝ) (U : Config G n) (β : ℝ),
    ‖β * ∑ p ∈ A,v p * leftOver (r+2) p U‖ ≤
      ‖β‖ * C * ∑ p ∈ A, ‖v p‖*(G.chord (faceValue U p))^(r+3) := by
  obtain ⟨C,hC,h⟩ := unspent G (r+2)
  refine ⟨C,hC,fun n A v U β => ?_⟩
  rw [norm_mul,mul_assoc,Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul,leftOver]
  exact (mul_le_mul_of_nonneg_left (h (faceValue U p)) (norm_nonneg _)).trans_eq (by ring)

end YM.Integration.NativeWilsonPlaquetteInvoice
end
