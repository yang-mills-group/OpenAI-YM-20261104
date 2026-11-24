import YM.Integration.WilsonOrdinaryThermalExperiment

/-! Positions of the physical position-coupling measurement. Each finite
leg uses the true running temperature of its own regulator, including
every enrolled correction. The mesh is the original spatial mesh. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerCells
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE OPE.Orbits RG12 RG17 SharpGram Climb PhysMS
open PhysicalNext.Repeat.Legato
open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2
open RegulatorIR.FVAAlt2.Lodge Cells Push.GridApprox
open WilsonOrdinaryThermalSource WilsonOrdinaryThermalPortfolio WilsonOrdinaryThermalExperiment
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Final R.family f S}
variable (L : Layout F) (cal : Calendar L) (Q : MS.Land.Prescription (Press.portDeck G))
variable {n : ℕ} (p : Fin n → MS.Rake.Label (Press.portDeck G)) (k : Fin n → ℕ) (b : Fin n → ℝ) (r : ℝ)

/-- The particular cutoff's actual physical Haar measurement, on its
literal original lattice addresses. -/
def measured (z : UVIndex) (x : Points n) : ℂ :=
  sample L Q p k b r z (address (R.family.S.a z.1) x)

/-- The corresponding exact continuum correlation of the thermal fields
on this same run and measuring calendar. -/
def physical (x : Points n) : ℂ :=
  S.classMoment S (fun i => (p i).h) x (field L cal Q p k b r)

theorem continuous :
    ContinuousOn (physical L cal Q p k b r) (conf n) := by
  let v (i : Fin n) : S.Tag := ⟨(p i).h,field L cal Q p k b r i⟩
  exact (S.class_smooth (spectator F none) (spectate F none).smooth v).continuousOn

/-- Uniformity on the actual separated spatial array, with the same cutoff
for every smooth test position. Each finite leg may have its own grade,
price date and finite thermal order. -/
theorem cells (hG : G.Simple) (admit : ∀ i (a : Term p k i),R.family.ref a.2.size ≤ L.level r)
    {K : Set (Points n)} (hk : IsCompact K) (sep : K ⊆ conf n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in (cal.cuts : Filter UVIndex),∀ x∈K,
      ‖measured L Q p k b r z x - physical L cal Q p k b r x‖ < ε := by
  obtain ⟨s,hs,cover⟩ := hk.exists_cthickening_subset_open (conf_open _) sep
  let U := cthickening s K
  have cu : IsCompact U := hk.cthickening
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp
    (cu.uniformContinuousOn_of_continuous ((continuous L cal Q p k b r).mono cover)) (ε/2) (half_pos he)
  have atTop' : Tendsto (fun z : UVIndex=>z.1) (cal.cuts : Filter UVIndex) atTop :=
    tendsto_atTop.mpr fun j => (large_mesh f j).filter_mono (cal.prior.trans L.certified)
  have small : Tendsto (fun z : UVIndex => (4*n : ℝ)*R.family.S.a z.1)
      (cal.cuts : Filter UVIndex) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (4*n : ℝ))).mul (R.family.S.shrinks.comp atTop')
  have bank := WilsonOrdinaryThermalExperiment.original L cal Q p k b r hG admit U cu cover (ε/2) (half_pos he)
  filter_upwards [bank,small.eventually (gt_mem_nhds (lt_min hs hδ))] with z paid mesh x hx
  let c := address (R.family.S.a z.1) x
  let y := tag (R.family.S.a z.1) c
  have near : dist y x < min s δ := (Extraction.approximate (R.family.S.a_pos z.1) x).trans_lt mesh
  have hy : y ∈ U := mem_cthickening_of_dist_le y x s K hx (near.le.trans (min_le_left _ _))
  have first : dist (measured L Q p k b r z x) (physical L cal Q p k b r y) < ε/2 := paid c hy
  have second := move y hy x (self_subset_cthickening K hx) (near.trans_le (min_le_right _ _))
  rw [← dist_eq_norm]
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add first second).trans_eq (add_halves ε))

end YM.Integration.WilsonPositionThermometerCells
