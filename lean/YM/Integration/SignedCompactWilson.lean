import YM.Integration.SignedRegulator

/-! Uniform convergence of the original ceil-rounded Wilson moments on compact
separated configurations, with the cutoff limit inside the period limit. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SignedCompactWilson
open Function Filter Set Metric Spec OPE OPE.Orbits PhysMS Extraction Asymptotics
open Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood
open EngineeringWeightedReadout PhysicalMSOPECandidate ActualSignedMSReadout
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {n i D : ℕ}

/-- The corner receipt is uniform on a compact enlargement. The uniform
rounding error then moves the limiting moment back to the original location. -/
theorem rounded_read (F : Final C f S) (hS : Services C f S) (v : Fin n → C.book.Token)
    (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ x ∈ K,
      dist ((StressFlux.Matching.rounded C w.1 w.2).read x v) (S.read x v) < ε := by
  obtain ⟨δ,hδ,hSep⟩ := hK.exists_cthickening_subset_open (conf_open n) hsep
  let L := cthickening δ K
  have hL : IsCompact L := hK.cthickening
  have hc : ContinuousOn (fun x => S.read x v) L :=
    (S.smooth_read F.room.kernel.smooth v).continuousOn.mono hSep
  obtain ⟨σ,hσ,hClose⟩ :=
    Metric.uniformContinuousOn_iff.mp (hL.uniformContinuousOn_of_continuous hc) (ε/2) (half_pos hε)
  have hscale : Tendsto (fun w : ℕ × ℕ => (4*n : ℝ) * C.S.a w.1) f.fuse (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using ((C.S.shrinks.comp (OPE.Cards.largeMesh f)).const_mul (4*n : ℝ))
  have hcorner : ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ a : Fin n → Lattice.Cover,
      tag (C.S.a w.1) a ∈ L →
        dist (lifted C w.1 w.2 v a) (S.read (tag (C.S.a w.1) a) v) < ε / 2 :=
    RGReadout.Literal.cornerLimit hS v L hL hSep _ (half_pos hε)
  filter_upwards [hscale.eventually (gt_mem_nhds (lt_min hδ hσ)), hcorner] with w hs hw x hx
  let a := address (C.S.a w.1) x
  let y := tag (C.S.a w.1) a
  have hy : dist y x < min δ σ := (approximate (C.S.a_pos w.1) x).trans_lt hs
  have hyL : y ∈ L := mem_cthickening_of_dist_le y x δ K hx (hy.le.trans (min_le_left ..))
  have hfin : dist ((StressFlux.Matching.rounded C w.1 w.2).read x v) (S.read y v) < ε/2 :=
    hw a hyL
  have hlim := hClose y hyL x (self_subset_cthickening K hx) (hy.trans_le (min_le_right ..))
  exact (dist_triangle _ (S.read y v) _).trans_lt ((add_lt_add hfin hlim).trans_eq (add_halves ε))

/-- The physical representatives of an arbitrary original labelled word. -/
theorem moment_compact (F : Final C f S) (hS : Services C f S)
    {I A : Type} [Fintype I] [TopologicalSpace A] {d : I → ℕ}
    (v : Labels S d) (K : Set A) (hK : IsCompact K) (X : A → I → E4)
    (hX : ContinuousOn X K) (hsep : ∀ a ∈ K, Injective (X a)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ a ∈ K,
      dist (Orbits.moment (StressFlux.Matching.rounded C w.1 w.2) (X a) v)
        (Orbits.moment S (X a) v) < ε := by
  let Y (a : A) := points (X a ∘ runNames I)
  have hY : ContinuousOn Y K :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr fun j =>
      (continuous_apply (runNames I j)).comp_continuousOn hX)
  have hKY : Y '' K ⊆ conf (Fintype.card I) := by
    rintro z ⟨a,ha,rfl⟩
    exact runs_conf.mpr (hsep a ha)
  filter_upwards [rounded_read F hS (names v ∘ runNames I) (Y '' K)
    (hK.image_of_continuousOn hY) hKY hε] with w hw a ha
  simpa only [Orbits.observed, observe, worded, Table.readAt] using hw (Y a) ⟨a,ha,rfl⟩

/-- The original continuum table is continuous on separated named positions. -/
theorem moment_continuous (F : Final C f S) {I A : Type} [Fintype I] [TopologicalSpace A]
    {d : I → ℕ} (v : Labels S d) (K : Set A) (X : A → I → E4)
    (hX : ContinuousOn X K) (hsep : ∀ a ∈ K, Injective (X a)) :
    ContinuousOn (fun a => Orbits.moment S (X a) v) K := by
  let Y (a : A) := points (X a ∘ runNames I)
  have hY : ContinuousOn Y K :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.mpr fun j =>
      (continuous_apply (runNames I j)).comp_continuousOn hX)
  have h := (S.smooth_read F.room.kernel.smooth (names v ∘ runNames I)).continuousOn.comp hY
    (fun a ha => runs_conf.mpr (hsep a ha))
  simpa only [Function.comp_def, Y, Orbits.observed, observe, worded, Table.readAt] using h

/-- At each fixed radius the whole separated room, including its boundary,
is compact in the original tuple of physical positions. -/
theorem room_compact (n : ℕ) (r M η : ℝ) :
    IsCompact {x : Fin n → E4 | WithinRoom r M η x 0} := by
  have hk : IsCompact (univ.pi (fun _ : Fin n => closedBall (0 : E4) (M*r))) :=
    isCompact_univ_pi fun _ => isCompact_closedBall _ _
  apply hk.of_isClosed_subset
  · have eqs : {x : Fin n → E4 | WithinRoom r M η x 0} =
        {x | (∀ j, ‖x j - 0‖ ≤ M*r) ∧ ∀ a b, a ≠ b → η*r ≤ ‖x a - x b‖} :=
      Set.ext fun _ => ⟨fun h => ⟨h.span,h.spaced⟩, fun h => ⟨h.1,h.2⟩⟩
    rw [eqs]
    simp only [setOf_and, setOf_forall]
    refine IsClosed.inter (isClosed_iInter fun j => ?_) (isClosed_iInter fun a =>
      isClosed_iInter fun b => isClosed_iInter fun _ => ?_)
    · exact isClosed_le ((continuous_apply j).sub continuous_const).norm continuous_const
    · exact isClosed_le continuous_const ((continuous_apply a).sub (continuous_apply b)).norm
  · intro x hx j _
    exact (dist_eq_norm _ _).trans_le (hx.span j)

/-- All detector rows of the original full cluster, before the counter field.
The map is multilinear in independent physical input fields. -/
def productTensor (T : Table C.book) (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (r : ℝ) (x : Fin n → E4) :
    MultilinearMap ℂ (fun _ : Fin n => E C.labels i) (E C.labels D) :=
  (wholeReadout U J r).toLinearMap.compMultilinearMap (MultilinearMap.pi (fun a =>
    let e := fun j => (OPE.tags S (U.listen a) j).1
    let w : Labels S e := fun j => (OPE.tags S (U.listen a) j).2
    (sectionLabels (d := Sum.elim (fun _ : Fin n => i) e) w
      (Orbits.moment T (beside x (OPE.positions S (U.listen a)).ofLp))).compLinearMap
        (fun _ => (J r i).toLinearMap)))

def row (T : Table C.book) (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (r : ℝ) (x : Fin n → E4) (v : Fin n → E C.labels i) (a : Fin U.size) : ℂ :=
  whole T x (Frame.born J r v) (OPE.positions S (U.listen a)).ofLp
    (fun j => (OPE.tags S (U.listen a) j).2)

theorem productTensor_apply (T : Table C.book) (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (r : ℝ) (x : Fin n → E4) (v : Fin n → E C.labels i) :
    productTensor T J U r x v = wholeReadout U J r (row T J U r x v) := by
  apply congrArg (wholeReadout U J r)
  funext a
  let e := fun j => (OPE.tags S (U.listen a) j).1
  let y := (OPE.positions S (U.listen a)).ofLp
  let w : Labels S e := fun j => (OPE.tags S (U.listen a) j).2
  exact sectionLabels_apply w (Orbits.moment T (d := Sum.elim (fun _ : Fin n => i) e)
    (beside x y)) (Frame.born J r v)

/-- Regulator removal for the full product is uniform on the compact
separated set and on all independent input tuples at the fixed radius. -/
theorem product_uniform (F : Final C f S) (hS : Services C f S)
    (J : ℝ → PhysMS.tower S) (U : Detector S D) (r : ℝ)
    (K : Set (Fin n → E4)) (hK : IsCompact K)
    (hs : ∀ x ∈ K, ∀ a, Injective (beside x (OPE.positions S (U.listen a)).ofLp))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ x ∈ K, ∀ v : Fin n → E C.labels i,
      ‖productTensor (StressFlux.Matching.rounded C w.1 w.2) J U r x v -
        productTensor S J U r x v‖ ≤ ε * ∏ j, ‖v j‖ := by
  let l : Filter ((ℕ × ℕ) × K) := comap Prod.fst f.fuse
  let R (w : ℕ × ℕ) := StressFlux.Matching.rounded C w.1 w.2
  let L (a : (ℕ × ℕ) × K) := productTensor (i := i) (R a.1) J U r a.2.val -
    productTensor S J U r a.2.val
  have hRow (v : Fin n → E C.labels i) (j : Fin U.size) :
      Tendsto (fun a : (ℕ×ℕ) × K =>
        row (R a.1) J U r a.2.val v j - row S J U r a.2.val v j) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let y := (OPE.positions S (U.listen j)).ofLp
    let X (x : Fin n → E4) := beside x y
    have hX : Continuous X := continuous_pi fun s => match s with
      | .inl a => continuous_apply a
      | .inr _ => continuous_const
    have h := moment_compact F hS
      (stages (Frame.born J r v) (fun j' => (OPE.tags S (U.listen j) j').2)) K hK X
        hX.continuousOn (fun x hx => hs x hx j) hδ
    apply eventually_comap.mpr
    filter_upwards [h] with w hw a ha
    subst w
    have hd := hw a.2.val a.2.property
    rw [dist_eq_norm] at hd
    rw [dist_zero_right]
    exact hd
  have hF (v : Fin n → E C.labels i) : (fun a => L a v) =o[l] (fun _ => (1 : ℝ)) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    have hp := tendsto_pi_nhds.mpr (hRow v)
    have he := ((wholeReadout U J r).continuous.tendsto 0).comp hp
    rw [map_zero] at he
    apply he.congr' (Eventually.of_forall fun a => ?_)
    change _ = productTensor (R a.1) J U r a.2.val v - productTensor S J U r a.2.val v
    rw [productTensor_apply, productTensor_apply, ← map_sub]
    rfl
  have h := SignedTensor.uniform_of_basis_littleO (RG11.Fields.tower C.labels i).b L
    (fun _ => (1 : ℝ)) (fun _ => hF _) hε
  exact (eventually_comap.mp h).mono fun w hw x hx v => by
    have hv := hw (w, ⟨x,hx⟩) rfl v
    change ‖productTensor (R w) J U r x v - productTensor S J U r x v‖ ≤
      ε * ‖(1 : ℝ)‖ * ∏ j, ‖v j‖ at hv
    simpa only [norm_one, mul_one] using hv

end YM.Integration.SignedCompactWilson
