import YM.Integration.FiniteHorizonGram
import YM.Integration.WilsonWholeLimit

/-! Uniform inversion of the actual finite normalized Wilson two-point
Gram matrix, in the measured running coordinates before regulator removal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedWilsonProbeInverse
open Function Filter Set Spec Climb OPE PhysMS Trace.Pilot Pert.Position
open FiniteHorizonGram Push.FiniteDetection.Free
open scoped Topology Classical

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hS : Services C f S) (D : ℕ)

def gram (T : Table C.book) (r : ℝ) : E C.labels D →ₗ[ℂ] (ProbeIndex C D → ℂ) :=
  LinearMap.pi fun b =>
    ((OPE.Levy.linear₂ (S.classMoment T (fun _ : Fin 2 => D) (r • detectors))).flip
      (J r D (probeBasis C D b))).comp (J r D).toLinearMap

theorem gram_apply (T : Table C.book) (r : ℝ) (z : E C.labels D) (b : ProbeIndex C D) :
    gram J D T r z b =
      S.classMoment T (fun _ : Fin 2 => D) (r • detectors) ![J r D z,J r D (probeBasis C D b)] := rfl

abbrev regulated (r : ℝ) (a : ℕ × ℕ) := gram J D (StressFlux.Matching.rounded C a.1 a.2) r

include hJ hS in
theorem limit (z : E C.labels D) : Tendsto
    (fun a : ℝ × (ℕ × ℕ) => regulated J D a.1 a.2 z) (trail.curry f.fuse) (𝓝 (freeProbes C D z)) := by
  apply tendsto_pi_nhds.mpr
  intro b
  have outer := tendsto_pi_nhds.mp (runningProbes_tendsto F D J hJ z) b
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply eventually_curry_iff.mpr
  filter_upwards [Metric.tendsto_nhds.mp outer (ε/2) (half_pos hε),self_mem_nhdsWithin] with r hr hp
  have inner : Tendsto (fun s : ℕ × ℕ => regulated J D r s z b) f.fuse
      (𝓝 (runningProbes D (J r) r z b)) :=
    WilsonWholeLimit.rounded_tendsto_separated F hS
      (Orbits.names (d := fun _ : Fin 2 => D) ![J r D z,J r D (probeBasis C D b)])
      (r • detectors) (Work.A05.smul_conf hp detectors_in)
  filter_upwards [Metric.tendsto_nhds.mp inner (ε/2) (half_pos hε)] with a ha
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add ha hr).trans_eq (add_halves ε))

def decode (r : ℝ) (a : ℕ × ℕ) : (ProbeIndex C D → ℂ) →ₗ[ℂ] E C.labels D :=
  if h : Bijective (regulated J D r a) then (LinearEquiv.ofBijective (regulated J D r a) h).symm.toLinearMap else 0

include hS hJ in
/-- One finite-volume inverse constant for all source fields and all
observational data.  The inverse is the one of this very finite matrix. -/
theorem inverse : ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ r in trail, ∀ᶠ a : ℕ × ℕ in f.fuse,
    Function.Bijective (regulated J D r a) ∧
    ∀ (z : E C.labels D) (u : ProbeIndex C D → ℂ),
      decode J D r a (regulated J D r a z) = z ∧
      regulated J D r a (decode J D r a u) = u ∧
      ‖decode J D r a u - z‖ ≤ K * ‖u - regulated J D r a z‖ := by
  obtain ⟨K,hK,h₀⟩ := Measuring.priced (limit F J hJ hS D) (freeProbes_injective C D)
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_curry_iff.mp h₀] with r hr
  filter_upwards [hr] with a h
  let A := regulated J D r a
  have hi : Injective A := by
    intro z y e
    have hz := (h (z-y)).2
    change ‖z-y‖ ≤ K*‖A (z-y)‖ at hz
    rw [map_sub,e,sub_self,norm_zero,mul_zero] at hz
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)
  have hd : Module.finrank ℂ (E C.labels D) = Module.finrank ℂ (ProbeIndex C D → ℂ) :=
    (probeBasis C D).equivFun.finrank_eq
  have hb : Bijective A := ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hi⟩
  refine ⟨hb,fun z u => ?_⟩
  let B := LinearEquiv.ofBijective A hb
  have h₁ : decode J D r a (A z) = z := by rw [decode,dif_pos hb]; exact B.symm_apply_apply z
  have h₂ : A (decode J D r a u) = u := by rw [decode,dif_pos hb]; exact B.apply_symm_apply u
  refine ⟨h₁,h₂,?_⟩
  have hz := (h (decode J D r a u - z)).2
  change _ ≤ K*‖A (decode J D r a u-z)‖ at hz
  simpa only [map_sub,h₂] using hz

end YM.Integration.SignedWilsonProbeInverse
