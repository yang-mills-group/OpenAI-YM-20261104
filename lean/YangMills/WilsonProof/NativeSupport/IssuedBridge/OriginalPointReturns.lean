import YangMills.WilsonProof.NativeSupport.IssuedBridge.PhysicalPeriodUniform
import YangMills.WilsonProof.NativeSupport.IssuedBridge.FinalVolumeRecord
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFixedStencils
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCompactVolumes
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace IssuedBridge.OriginalPointReturns
open YangMills YangMills.Wilson YM.Integration
open YM.Extraction YM.FullVolume YM.PhysicalNext.Repeat.Legato
open Filter Function Set MeasureTheory
open scoped Topology
open IssuedBridge.PhysicalPeriodNodes
universe u
variable {g : GaugeGroup} {R : Run g.core} {T : YM.PhysicalNext.Repeat.Legato.Campaign R}
    {W : YM.PhysicalNext.Repeat.Legato.Campaign.Pillars R T}

theorem rows {axis : YM.Axis} {simple : g.core.Simple} {ε : ℝ}
    {schedule : WilsonOriginalAllOrderCourse.Schedule g.core}
    (paid : WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε schedule R T W) :
    ∃ row : (m n : ℕ) → (Fin n → R.family.book.Token) → YM.Points n → ℂ,
      FixedPointReturns (wilsonFamily R.family) (appoint R.family row) ∧
      ∀ (m n : ℕ) (v : Fin n → R.family.book.Token),
        Cluster R.family .full m n (fun N => lifted R.family N m v) (row m n v) := by
  obtain ⟨_,row,read⟩ :=
    WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicFixedStencils.original paid
  have cluster (m n : ℕ) (v : Fin n → R.family.book.Token) :
      Cluster R.family .full m n (fun N => lifted R.family N m v) (row m n v) :=
    ((read m n v).2.2 []).2.1
  refine ⟨row, ⟨?_, ?_, ?_⟩, cluster⟩
  · intro m n v
    exact continuousOn_iff_continuous_restrict.mp ((read m n v).1.continuousOn.mono (fun _ hz => safe R.family hz))
  · intro m n v t st
    rw [← test R.family row m n v t st]
    simp_rw [smear_eq]
    exact (read m n v).2.1 t st
  · intro m n v K compact inside ε pos
    exact PhysicalPeriodUniform.compact R.family row m n v (cluster m n v) K compact inside ε pos

theorem outer (simple : g.core.Simple) {order : YM.Extraction.Order} {S : YM.Table R.family.book}
    (F : YM.Spec.Final R.family order S) (Q : YM.OPE.Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (row : (m n : ℕ) → (Fin n → R.family.book.Token) → YM.Points n → ℂ)
    (cluster : ∀ (m n : ℕ) (v : Fin n → R.family.book.Token),
      Cluster R.family .full m n (fun N => lifted R.family N m v) (row m n v))
    (n : ℕ) (v : Fin n → R.family.book.Token) (K : Set (YM.Points n))
    (compact : IsCompact K) (sep : K ⊆ WilsonFamily.separated n) (ε : ℝ) (positive : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ z ∈ K,
      dist (periodValue (appoint R.family row) (order.per.choose k) v z)
        ((hierarchy F Q).correlation none ((hierarchy F Q).project ∘ v) z) < ε := by
  have measured := WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicCompactVolumes.comparison
    simple F v (fun m => row m n v) (fun m => cluster m n v) compact sep (half_pos positive)
  filter_upwards [measured,order.per.cofinal.eventually (room R.family.S compact)] with k seen interior
  intro z hz
  have inPatch : z ∈ periodPatch (wilsonFamily R.family) (order.per.choose k) n :=
    ⟨sep hz,interior hz⟩
  rw [appointment R.family row (order.per.choose k) n v inPatch]
  have identify : (hierarchy F Q).correlation none ((hierarchy F Q).project ∘ v) z = S.read z v := by
    change S.useAt S z (S.classTokens ∘ v) = S.read z v
    rw [S.at_project S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) (sep hz)]
  rw [identify]
  exact (seen z hz).trans_lt (half_lt_self positive)

theorem original (axis : YM.Axis) (hg : g.IsSimple) (B : Maxwell.Reference g)
    {ε : ℝ} (positive : 0 < ε) (σ : WilsonOriginalAllOrderCourse.Schedule g.core) :
    ∃ run : Construction g, WilsonRegularity run.family ∧ WilsonTrajectory B run.family ∧
      run.originalPointReturns ∧ ∃ D : WilsonData B run.family, ∀ (p : ℕ → ℕ) (hp : StrictMono p),
        let chosen := run.refine p hp
        D.AdjointOn chosen.hierarchy ∧ run.family.Converges (p ∘ chosen.indices)
          (fun v => chosen.hierarchy.correlation none (chosen.hierarchy.project ∘ v)) := by
  obtain ⟨R,T,W,D0,trajectory,restored,banks,paid,bank,lamp,paths,low,oldRows,whole,make⟩ :=
    IssuedBridge.SelectedQuotient.original.{0} axis hg B positive σ
  obtain ⟨row,fixed,cluster⟩ := rows paid
  obtain ⟨selected,every⟩ := make (fun _ => True) (by intros; trivial)
  let D := IssuedRuns.FinalWilsonData.original R.family R.makes hg B
  refine ⟨FinalVolumeRecord.original R selected, D.regular, trajectory, ⟨appoint R.family row, fixed, ?_⟩, D, ?_⟩
  · intro p hp n v K compact inside ε pos
    let packet := selected ⟨p,hp⟩
    exact outer (GaugeGroup.coreSimple hg) packet.theory packet.reader row cluster n v K compact inside ε pos
  · intro p hp
    obtain ⟨adjoint,limit,_⟩ := every ⟨p,hp⟩
    exact ⟨adjoint,limit⟩

end IssuedBridge.OriginalPointReturns
end
