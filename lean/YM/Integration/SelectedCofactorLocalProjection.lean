import YM.Integration.SelectedCofactorChamberMarginal

/-! A marginal of complete original signed packets localized by their distinguished physical flag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorLocalProjection
open Function Finset Set Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained RG3.Forms RG3.Script.Picnic
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags SelectedCofactorChamberMarginal
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V} {J : Request V}
variable {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F} {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)

/-- A fixed finite Wilson history has a positive fieldwise floor at the actual
coarse output. The common partition and the step noise determine the floor. -/
theorem floor (hC : C.Makes) {N p m : ℕ} (hm : m < N) :
    ∃ a : ℝ, 0 < a ∧ ∀ U, a ≤ (C.path.rep N p m).eval U := by
  let S := C.path.levels.clock.op m p
  let b := C.path.β N p (m+1)
  let A₁ := C.path.rep N p (m+1)
  let k := (Push.BetaTransport.noiseCost S |b|)⁻¹
  let Z := partition G (C.side N p) (C.path.β N p N)
  have hk : 0 < k := inv_pos.mpr (Push.BetaTransport.noiseCost_pos S _)
  have hZ : 0 < Z := partition_pos _
  have hstep := (C.path.levels.blocks m p).branches
  have hd (u : Config G (C.side (m+1) p)) (v : Config G (C.side m p)) : k ≤ S.density b u v := by
    calc k = ∑ t, S.likelihood u t * k := by rw [← Finset.sum_mul,S.chosen hstep,one_mul]
         _ ≤ _ := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
           (Push.BetaTransport.noise_bounds S (le_refl |b|) (S.prediction u t) v).1 (S.likelihood_pos u t)
  have hI := (A₁.envelope (hC.wilson.represents N p (m+1) hm).good).integrable (prior G _)
  have hmass : (∫ u, A₁.eval u ∂prior G _) = Z := C.path.partition_eq hC.wilson N p (m+1) hm
  refine ⟨k*Z,mul_pos hk hZ,fun v => ?_⟩
  rw [← hmass,←integral_const_mul,(hC.wilson.steps N p m hm).1]
  exact integral_mono (hI.const_mul k) (StepData.push_slice (C.path.levels.transition_mass ..) v _ hI)
    (fun u => mul_le_mul_of_nonneg_right (hd u v) (Multi.AxisShift.chosen_positive hC.wilson hm u).le)

/-- Retained sites whose incident plaquettes are read entirely inside X. -/
def deep {n : Side} (X : Set (Site n)) : Set (Site n) :=
  {z | ∀ p : Face (Per n), z ∈ touched p → (↑(touched p) : Set (Site n)) ⊆ X}

def readout (S : Chosen K I M) (x : IndependentTests J.tests) (A₀ X : Set (Site n₀))
    (Q : (ℕ × Finset ℕ) → Prop) (L : Poly B →L[ℂ] ℂ) : Config G n₀ → ℂ :=
  projected (links A₀) (W₀).eval (fun U => L (rooted S x X Q U))

private theorem row_env (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta order)
    (x : IndependentTests J.tests) (X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop)
    (L : Poly B →L[ℂ] ℂ) : Envelope (fun U => L (rooted S x X Q U)) := by
  have h := rooted_envelope hC S H x X Q
  obtain ⟨b,hb⟩ := h.cost
  exact ⟨L.continuous.measurable.comp h.meas,‖L‖*b,
    fun U => (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb U) (norm_nonneg _))⟩

/-- The projected signed insertion has an original physical Wilson representative
on exactly the retained chamber links. Its moment includes every exterior partner. -/
theorem realization (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta order)
    (x : IndependentTests J.tests) (A₀ X : Set (Site n₀)) (Q : (ℕ × Finset ℕ) → Prop)
    (L : Poly B →L[ℂ] ℂ) :
    LocalOn A₀ (readout S x A₀ X Q L) ∧ Envelope (readout S x A₀ X Q L) ∧
      (∫ U, (W₀).eval U • readout S x A₀ X Q L U ∂prior G n₀) =
        ∫ U, L (rooted S x X Q U) ∂prior G n₀ := by
  have hP := (W₀).envelope (hC.wilson.represents _ _ _ datum.below.le).good
  have hF := row_env hC S H x X Q L
  obtain ⟨a,ha,hl⟩ := floor hC (p := datum.period) datum.below
  exact ⟨projected_local _ _ _,projected_env _ hP hF ha hl,pairing _ hP hF ha hl⟩

/-- A nonzero conditional marginal still detects a genuine local hot plaquette.
Only the distinguished site lies in X. Every spectator may lie outside the chamber. -/
theorem hot (S : Chosen K I M) (x : IndependentTests J.tests) (A₀ X : Set (Site n₀))
    (hX : X ⊆ deep A₀) (Q : (ℕ × Finset ℕ) → Prop) (L : Poly B →L[ℂ] ℂ)
    {t : ℝ} (ht : t ≤ S.output.carrier.rep.p.threshold) (U : Config G n₀)
    (hn : readout S x A₀ X Q L U ≠ 0) : ∃ z ∈ X, z ∈ flags t U := by
  let A₁ := links A₀
  let u := ((cut G A₁) U).1
  have hw : ∃ y : Fields G A₁ᶜ, L (rooted S x X Q ((cut G A₁).symm (u,y))) ≠ 0 := by
    by_contra! hz
    apply hn
    change (marginal A₁ (W₀).eval u)⁻¹ • ∫ y, L (rooted S x X Q ((cut G A₁).symm (u,y))) ∂sheet G A₁ᶜ = 0
    simp only [hz,integral_zero,smul_zero]
  obtain ⟨y,hy⟩ := hw
  let V₀ := (cut G A₁).symm (u,y)
  have he : Agrees A₀ V₀ U := by
    intro e hx he
    exact congr_fun (congrArg Prod.fst ((cut G A₁).apply_symm_apply (u,y))) (⟨e,hx,he⟩ : A₁)
  obtain ⟨z,hz,hf⟩ := rooted_flag S x X Q L ht V₀ hy
  obtain ⟨p,hzp,hp⟩ := (flags_spec _ _ _).1 hf
  have hc := hX hz p hzp
  have hface : faceValue V₀ p = faceValue U p := by
    apply travel_local
    intro e he₁ he₂
    exact he e (hc (by simpa only [Finset.mem_coe,touched,List.mem_toFinset,Set.mem_setOf_eq] using he₁))
      (hc (by simpa only [Finset.mem_coe,touched,List.mem_toFinset,Set.mem_setOf_eq] using he₂))
  exact ⟨z,hz,(flags_spec _ _ _).2 ⟨p,hzp,hface ▸ hp⟩⟩

end YM.Integration.SelectedCofactorLocalProjection
end
