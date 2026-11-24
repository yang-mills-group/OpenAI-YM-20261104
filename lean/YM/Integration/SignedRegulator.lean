import YM.Integration.SignedUniformReadout

/-! Uniform regulator convergence at a fixed separated configuration. The source
is the normalized Wilson ensemble with the original rounding and detector, and
the bound covers all independent physical input fields and comparison levels. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.SignedRegulator
open Function Filter Spec OPE OPE.Orbits PhysMS Asymptotics
open Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood
open EngineeringWeightedReadout PhysicalMSOPECandidate ActualSignedMSReadout SignedUniformReadout
open scoped Topology BigOperators Classical

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {n i D : ℕ}

/-- Evaluate the two joint marked products with their common macroscopic
exterior in a single moment table, and apply the whole physical inverse. -/
def detectorTensor (T : Table C.book) (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (N : ℕ) (t r : ℝ) (x : Fin n → E4) :
    MultilinearMap ℂ (fun _ : Fin n => E C.labels i) (E C.labels D) :=
  (wholeReadout U J r).toLinearMap.compMultilinearMap (MultilinearMap.pi (fun a =>
    let e := fun j => (OPE.tags S (U.listen a) j).1
    let y := (OPE.positions S (U.listen a)).ofLp
    let w : Labels S e := fun j => (OPE.tags S (U.listen a) j).2
    (sectionLabels (d := Sum.elim (fun _ : Fin n => i) e) w
      (Orbits.moment T (beside x y))).compLinearMap (fun _ => (J r i).toLinearMap) -
    ((upon T D 0 y w).comp (J r D).toLinearMap).compMultilinearMap (formalTensor p Z B N t)))

theorem detectorTensor_apply (T : Table C.book) (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (v : Fin n → E C.labels i) :
    detectorTensor T J U p Z B N t r x v = wholeReadout U J r (fun a =>
      whole T x (Frame.born J r v) (OPE.positions S (U.listen a)).ofLp
        (fun j => (OPE.tags S (U.listen a) j).2) -
      upon T D 0 (OPE.positions S (U.listen a)).ofLp
        (fun j => (OPE.tags S (U.listen a) j).2) (candidate J p Z B v N t r)) := by
  apply congrArg (wholeReadout U J r)
  funext a
  let e := fun j => (OPE.tags S (U.listen a) j).1
  let y := (OPE.positions S (U.listen a)).ofLp
  let w : Labels S e := fun j => (OPE.tags S (U.listen a) j).2
  exact congrArg₂ HSub.hSub
    (sectionLabels_apply w (Orbits.moment T (d := Sum.elim (fun _ : Fin n => i) e)
      (beside x y)) (Frame.born J r v))
    (congrArg (fun c => upon T D 0 y w (J r D c)) (formalTensor_apply p Z B N t v))

/-- Reading the actual rounded table on quotient field representatives gives
exactly the original normalized finite Wilson moment of the unaltered product. -/
theorem rounded_product {I : Type} [Fintype I] {d : I → ℕ}
    (x : I → E4) (v : Labels S d) (cutoff period : ℕ) :
    Orbits.moment (StressFlux.Matching.rounded C cutoff period) x v =
      Wilson.moment (C.beta cutoff period) (WilsonWholeLimit.product x v cutoff period) := by
  rw [Orbits.observed, observe, worded, Table.readAt]
  exact (WilsonWholeLimit.product_read x v cutoff period).symm

theorem finite_eq_tensor (hC : C.Makes) (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (v : Fin n → E C.labels i) (cutoff period m : ℕ) (hm : m ≤ cutoff)
    (hUnit : C.ref 0 ≤ cutoff) :
    finiteReadout J U v r x (candidate J p Z B v N t r) cutoff period m hm =
      detectorTensor (StressFlux.Matching.rounded C cutoff period) J U p Z B N t r x v := by
  rw [finiteReadout_eq hC _ _ _ _ _ _ _ _ _ _ hUnit, detectorTensor_apply]
  apply congrArg (wholeReadout U J r)
  funext a
  rw [WilsonWholeLimit.detectorDiscrepancy_moment]
  change _ = Orbits.moment _ _ _ - Orbits.moment _ _ _
  rw [rounded_product, rounded_product]

theorem continuum_eq_tensor (F : Final C f S) (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (v : Fin n → E C.labels i) :
    weightedMSResidual J U p Z B v N t r x = detectorTensor S J U p Z B N t r x v := by
  rw [detectorTensor_apply]
  apply congrArg (wholeReadout U J r)
  funext a
  exact congrArg (_ - ·) (detector_witness_eq_upon F (U.listen a) (U.awake a) _)

/-- Mesh-before-period convergence at the fixed separated geometry is uniform
over every independent input tuple and every lawful readout level. There is no
finite discrepancy smallness input. The limiting discrepancy itself may be
nonzero. Its full output-frame inverse and finite truncation stay fixed. -/
theorem candidate_uniform (F : Final C f S) (hS : Services C f S)
    (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (hx : ∀ a, Injective (beside x (OPE.positions S (U.listen a)).ofLp)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∀ (v : Fin n → E C.labels i) (m : ℕ) (hm : m ≤ w.1),
      ‖finiteReadout J U v r x (candidate J p Z B v N t r) w.1 w.2 m hm -
        weightedMSResidual J U p Z B v N t r x‖ ≤ ε * ∏ j, ‖v j‖ := by
  let T (w : ℕ × ℕ) := detectorTensor (StressFlux.Matching.rounded C w.1 w.2) J U p Z B N t r x -
    detectorTensor S J U p Z B N t r x
  have hUnit : ∀ᶠ w : ℕ × ℕ in f.fuse, C.ref 0 ≤ w.1 := by
    rw [Extraction.Order.fused, Extraction.Order.late]
    exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop _
  have app (w : ℕ × ℕ) (hw : C.ref 0 ≤ w.1) (v : Fin n → E C.labels i) (m : ℕ) (hm : m ≤ w.1) :
      T w v = finiteReadout J U v r x (candidate J p Z B v N t r) w.1 w.2 m hm -
        weightedMSResidual J U p Z B v N t r x := by
    rw [finite_eq_tensor F.room.cutoff J U p Z B N t r x v w.1 w.2 m hm hw,
      continuum_eq_tensor F J U p Z B N t r x v]
    rfl
  have hpoint (v : Fin n → E C.labels i) :
      (fun w => T w v) =o[f.fuse] (fun _ => (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).mpr
    have lim := (candidate_tendsto F hS J U p Z B v N t r x hx
      (fun w => ⟨w.1, Nat.lt_succ_self _⟩)).sub_const (weightedMSResidual J U p Z B v N t r x)
    rw [sub_self] at lim
    exact lim.congr' (hUnit.mono fun w hw => (app w hw v w.1 le_rfl).symm)
  filter_upwards [SignedTensor.uniform_of_basis_littleO (RG11.Fields.tower C.labels i).b
    T (fun _ => (1 : ℝ)) (fun _ => hpoint _) hε, hUnit] with w hw hunit v m hm
  simpa only [app w hunit v m hm, norm_one, mul_one] using hw v

end YM.Integration.SignedRegulator
