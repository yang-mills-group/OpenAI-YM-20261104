import YM.Integration.WilsonPositionHomogeneousLeading
import YM.Work.A04
/-! Finite fixed-field detection at the original radii with all issued
spectators in the very same frame as the numerical matching measurement. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOneFrameFixedReadings
open Filter Set Function Lattice Wilson RG Source OPE Spec Table Climb Ward Maxwell PhysMS Trace.Pilot
open PhysicalNext.Repeat.Legato XSpace XSpace.Normalize FVA2 FVA2.Register WilsonPositionHomogeneousFrame
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)
    (radii:Scaling S)
local notation "C" => R.family

def ruler : Scaling S := {radii with U := fun k => homogeneous F J Z (radii.r k)}
local notation "X" => ruler F J Z radii
include lead owed simple in
private theorem point {n : ℕ} (q : Fin n → (Bel R.family.book).Tag) {x : Points n} (hx : x ∈ conf n) :
    Tendsto (fun k => disc ((ruler F J Z radii).pins k ∘ q) ((ruler F J Z radii).r k • x)) atTop (𝓝 (disc q x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  have along : Tendsto radii.r atTop trail :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ radii.drips (Eventually.of_forall radii.positive)
  have jets := WilsonPositionHomogeneousLeading.jets F J Z lead owed simple (fun i => (q i).1)
    (fun i => (q i).2) 0 isCompact_singleton (singleton_subset_iff.mpr hx) (half_pos pos)
  filter_upwards [along.eventually jets] with k hk
  have hh := hk x (mem_singleton _)
  rw [dist_eq_norm]
  simp only [iteratedFDeriv_zero_eq_comp,comp_apply,←map_sub,LinearIsometryEquiv.norm_map] at hh
  exact hh.trans_lt (half_lt_self pos)

def mixedRow (d : ℕ) (e : Exterior (standard R.family.labels)) (k : ℕ) (a : S.Field d) : ℂ :=
  disc (Fin.cons (α := fun _ : Fin (e.n+1) => S.Tag) ⟨d,a⟩
    ((ruler F J Z radii).pins k ∘ ((freeTable R.family.labels).classTokens ∘ e.letter))) ((ruler F J Z radii).r k • e.point)

include lead owed simple in
open Work.A04 in
theorem original (d : ℕ) : ∃ D : Finset (Exterior (standard R.family.labels)),
    Injective (LinearMap.pi (fun e : D => row (freeTable R.family.labels) d e.val)) ∧
    ∀ (a : ℕ → S.Field d) (v : (freeTable R.family.labels).Field d),
    (∀ e ∈ D, Tendsto (fun k => mixedRow F J Z radii d e k (a k)) atTop (𝓝 (row (freeTable R.family.labels) d e v))) →
    Tendsto (fun k => ((ruler F J Z radii).U k d).symm (a k)) atTop (𝓝 v) := by
  classical
  obtain ⟨D,hD⟩ := finite_faithful _ (row_faithful (freeTable R.family.labels) d)
  refine ⟨D,hD,fun a v readings => ?_⟩
  apply tendsto_of_fitted (fun k => LinearMap.pi (fun e : D => approxRow X d e.val k)) _ hD
  · intro p
    apply tendsto_pi_nhds.mpr
    intro e
    change Tendsto (fun k => approxRow X d e.val k p) atTop (𝓝 (row (freeTable R.family.labels) d e.val p))
    simp_rw [approxRow_eq,row_eq (table_sym _)]
    exact point F J Z lead owed simple radii (Work.A04.tags _ e.val p) e.val.clear
  · apply tendsto_pi_nhds.mpr
    intro e
    change Tendsto (fun k => approxRow X d e.val k (((ruler F J Z radii).U k d).symm (a k))) atTop (𝓝 (row (freeTable R.family.labels) d e.val v))
    have eqn (k : ℕ) : approxRow X d e.val k (((ruler F J Z radii).U k d).symm (a k)) = mixedRow F J Z radii d e.val k (a k) := by
      rw [approxRow_eq]
      unfold Work.A04.tags mixedRow
      rw [Fin.comp_cons]
      simp only [Scaling.pins,LinearEquiv.apply_symm_apply]
    simpa only [eqn] using readings e.val e.property

end YM.Integration.WilsonOneFrameFixedReadings
end
