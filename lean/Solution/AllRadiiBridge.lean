import YangMills.WilsonProof.SampledCoordinates
import Solution.AllRadiiMaxwell
import Solution.FixedFieldBridge

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YangMills.AllRadii
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free YM.AllRadiiMaxwell
open Function Filter Set
open scoped Topology BigOperators

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
local notation "B" => maxwellReference g
local notation "T" => hierarchy F Q

private def viewFrame (U : PhysMS.tower S) : Frame B T :=
  fun d => (fields C.labels d).symm.trans (U d)

private def slots {n : ℕ} (q : Fin n → Σ d, (B).sector d)
    (marked : Fin n → Bool) (ab : Fin n → Axis × Axis) (i : Fin n) : Slot C :=
  if marked i then .inr (ab i) else .inl ⟨(q i).1, (fields C.labels _).symm (q i).2⟩

private theorem mixed {U : ℝ → PhysMS.tower S} (h : Law F U)
    (n j : ℕ) (q : Fin n → Σ d, (B).sector d) (marked : Fin n → Bool)
    (ab : Fin n → Axis × Axis) (K : Set (Points n)) (compact : IsCompact K)
    (sep : K ⊆ YangMills.separated n) (ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s, JetBound B T r (viewFrame F Q (U r)) j q marked ab K ε s := by
  let v := slots (C := C) q marked ab
  let physicalTag (r : ℝ) (w : Slot C) : S.Tag := ⟨cap w, ymSlot F U r w⟩
  let polynomial (w : Slot C) := supply C.labels ⟨cap w, wickSlot w⟩
  have physical (r : ℝ) (s : Viewers F) (y : Points n) :
      S.classMoment (spectator F s) (cap ∘ v) (r • y) (fun i => ymSlot F U r (v i)) =
        (T).correlation s (fun i => if marked i then
          ⟨4, ((r^4 : ℝ) : ℂ) • (T).stress (ab i).1 (ab i).2⟩ else
          ⟨(q i).1, viewFrame F Q (U r) _ (q i).2⟩) (r • y) := by
    apply congrArg (S.useAt (spectator F s) (r • y))
      (a₁ := fun i => ⟨cap (v i), ymSlot F U r (v i)⟩)
    funext i
    change physicalTag r (v i) = _
    unfold v slots
    split_ifs <;> rfl
  have free (y : Points n) :
      PhysMS.WickGoal (fun i => wickSlot (v i)) y =
        (B).moment y (fun i => if marked i then ((B).stress (ab i).1 (ab i).2).val else (q i).2.val) := by
    change YM.Ward.disc (fun i => ⟨cap (v i), wickSlot (v i)⟩) y = _
    rw [YM.Ward.disc, display]
    congr 1
    funext i
    change polynomial (v i) = _
    unfold v slots
    split_ifs
    · change address C.labels 4 (-Free.original C.labels _ _) = _
      rw [map_neg,inertia]
      rfl
    · exact congrArg Subtype.val ((fields C.labels _).apply_symm_apply _)
  filter_upwards [h.marked F v j K compact sep ε pos] with r bound s x hx
  have joint := bound x hx s
  rw [funext (physical r s), funext free] at joint
  exact joint.le

private lemma powerBound {Y : Type*} [Norm Y] {f : ℝ → Y} {a : ℝ}
    (h : OPE.RateLE Trace.Pilot.trail Trace.Pilot.LogV f a) (δ : ℝ) (pos : 0 < δ) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ‖f r‖ ≤ r ^ (-a - δ) := by
  filter_upwards [h (a+δ) (by linarith), self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r bound hr
  apply bound.trans_eq
  rw [Trace.Pilot.LogV, Real.log_inv, Real.rpow_def_of_pos hr]
  congr 1
  ring

private theorem bounds (X : Climb.Scaling S) (first : Pert.FirstExtension F X)
    (V : ℝ → PhysMS.tower S) (hV : PhysMS.Leading F V) :
    FrameBounds B T (publicScaling F Q X first) (fun r => viewFrame F Q (V r)) := by
  constructor
  · intro d e he φ kill δ pos
    have annihilates : ∀ v ∈ OPE.Levy.planeAt (U := F.sector.derivatives) e he, φ v = 0 := by
      cases e with
      | zero =>
        intro v hv
        have hv0 : v = 0 := by simpa [OPE.Levy.planeAt] using hv
        rw [hv0]
        exact φ.map_zero
      | succ k =>
        rintro _ ⟨u, rfl⟩
        apply kill k (Nat.lt_succ_self k) u
        exact F.sector.derivatives.stays F.room.kernel.laws.toSymmetric (spectate_ready F none) _ u
    have hr := powerBound (PhysMS.Frame.upper F d V hV e he φ annihilates) δ pos
    let M := (X.U 0 d).symm.toLinearMap.toContinuousLinearMap
    refine ⟨‖M‖, M.opNorm_nonneg, ?_⟩
    filter_upwards [hr, self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with r bound hr u
    rw [neg_neg] at bound
    change ‖φ (V r d ((fields C.labels d).symm ((fields C.labels d) (M u))))‖ ≤ _
    rw [LinearEquiv.symm_apply_apply]
    calc
      _ ≤ ‖PhysMS.Frame.pulling d V φ r‖ * ‖M u‖ := (PhysMS.Frame.pulling d V φ r).le_opNorm _
      _ ≤ r ^ ((e : ℝ) - δ) * (‖M‖ * ‖u‖) :=
        mul_le_mul bound (M.le_opNorm u) (norm_nonneg _) (Real.rpow_nonneg hr.le _)
      _ = _ := by ring
  · intro d δ pos
    have hr := powerBound (PhysMS.Frame.inverse_rate F d V hV) δ pos
    let M := (X.U 0 d).toLinearMap.toContinuousLinearMap
    refine ⟨‖M‖, M.opNorm_nonneg, ?_⟩
    filter_upwards [hr] with r bound u
    change ‖M ((fields C.labels d).symm ((fields C.labels d) ((V r d).symm u)))‖ ≤ _
    rw [LinearEquiv.symm_apply_apply]
    calc
      _ ≤ ‖M‖ * ‖PhysMS.Frame.backward d V r u‖ := M.le_opNorm _
      _ ≤ ‖M‖ * (r ^ (-(d : ℝ) - δ) * ‖u‖) := by
        apply mul_le_mul_of_nonneg_left _ M.opNorm_nonneg
        exact ((PhysMS.Frame.backward d V r).le_opNorm u).trans (mul_le_mul_of_nonneg_right bound (norm_nonneg u))
      _ = _ := by ring

/-- Extend the frame from the sampling radii to all positive radii. -/
theorem extendFrame (X : Climb.Scaling S) (first : Pert.FirstExtension F X) (simple : g.core.Simple)
    (foundation : Foundation F Q) (trace : Trace.Target.Result.{0} F simple)
    (sampled : FixedFields.Laws B T (publicScaling F Q X first)) :
    ∃ J, Laws B T (publicScaling F Q X first) J ∧ FrameBounds B T (publicScaling F Q X first) J := by
  obtain ⟨U, h⟩ := allRadii F simple Q X foundation trace
  let V := YM.Existence.SelectedJets.SparseFrame.splice X U
  have lead := (YM.Existence.SelectedJets.SparseLeading.original F X first U h.1).2
  refine ⟨fun r => viewFrame F Q (V r), ⟨?_, ?_, ?_⟩, bounds F Q X first V lead⟩
  · intro k
    change viewFrame F Q (YM.Existence.SelectedJets.SparseFrame.splice X U (X.r k)) = _
    rw [YM.Existence.SelectedJets.SparseFrame.selected]
    rfl
  · intro i j
    have st := YM.Existence.SelectedJets.SparseFrame.convergence X U
      (fun r W => (W 4).symm (r^4 • F.sector.energy i j)) _
      (h.2.1 i j) (FixedFieldMaxwell.stress_alignment F first i j)
    have target : (fields C.labels 4).symm ((B).stress i j) = Pert.freeStress C.labels i j := by
      apply (fields C.labels 4).injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      change _ = address C.labels 4 (-Free.original C.labels i j)
      rw [map_neg, inertia]
      rfl
    change Tendsto (fun r => X.U 0 4 ((fields C.labels 4).symm
        ((fields C.labels 4) ((V r 4).symm (r^4 • F.sector.energy i j))))) _
      (𝓝 (X.U 0 4 ((fields C.labels 4).symm ((B).stress i j))))
    simp only [LinearEquiv.symm_apply_apply, target]
    exact ((X.U 0 4).toLinearMap.continuous_of_finiteDimensional.tendsto _).comp st
  · intro n j q marked ab K compact sep ε pos
    apply (YM.Existence.SelectedJets.SparseFrame.original X U
      (fun r W => ∀ s, JetBound B T r (viewFrame F Q W) j q marked ab K ε s)
      (mixed F Q h n j q marked ab K compact sep ε pos) ?_).2
    filter_upwards [sampled.allJets n j q marked ab K compact sep ε pos] with k hk s x hx
    exact hk x hx s

end YangMills.AllRadii
