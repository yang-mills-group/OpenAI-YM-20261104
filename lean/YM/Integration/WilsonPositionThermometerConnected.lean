import YM.Integration.WilsonPositionThermometerCells
import YM.Integration.WilsonReportSubroster
import YM.Integration.WilsonFundedPositionConnected

/-! The position thermometer's connected triple uses all seven original
subset moments at the same physical locations and the same regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerConnected
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open Next.Rank Next.UVStress OPE RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2 RegulatorIR.FVAAlt2.Lodge Cells Push.GridApprox
open WilsonOrdinaryThermalSource WilsonOrdinaryThermalPortfolio WilsonOrdinaryThermalExperiment
open WilsonReportSubroster XSpace.Rose
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Final R.family f S}
variable (L : Layout F) (cal : Calendar L) (Q : MS.Land.Prescription (Press.portDeck G))
variable (p : Fin 3 → MS.Rake.Label (Press.portDeck G)) (k : Fin 3 → ℕ) (b : Fin 3 → ℝ) (r : ℝ)

/-- This is the original thermometer's exact polynomial in its subset
moments, evaluated on constants. -/
theorem original_polynomial (A : Badge → ℂ) :
    PowerSeries.constantCoeff (b3 (fun s => PowerSeries.C (A s))) = value A := by
  simp [b3,value,Algebra.smul_def]

def cut (z : UVIndex) (x : Points 3) (s : Badge) : ℂ :=
  WilsonPositionThermometerCells.measured L Q (p ∘ pick s) (k ∘ pick s) (b ∘ pick s) r z (window s x)

def continuum (x : Points 3) (s : Badge) : ℂ :=
  WilsonPositionThermometerCells.physical L cal Q (p ∘ pick s) (k ∘ pick s) (b ∘ pick s) r (window s x)

/-- Every one of these subset moments is a marginal of the single original
positive law, with the actual complete corrected fields. -/
theorem integral (z : UVIndex) (x : Points 3) (s : Badge) :
    cut L Q p k b r z x s =
      ∫ A,∏ i∈s,factor L Q p k b r z (address (R.family.S.a z.1) x) i A
        ∂(Wilson.law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2)) := by
  unfold cut WilsonPositionThermometerCells.measured WilsonOrdinaryThermalExperiment.sample
  congr 1
  funext A
  rw [Finset.prod_subtype s (fun _=>Iff.rfl)
    (fun i=>factor L Q p k b r z (address (R.family.S.a z.1) x) i A)]
  exact Fintype.prod_equiv (order s) _ _ (fun _ => rfl)

theorem continuous_roster {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) :
    ContinuousOn (continuum L cal Q p k b r) K := by
  apply continuousOn_pi.mpr
  intro s
  exact ((WilsonPositionThermometerCells.continuous L cal Q (p ∘ pick s) (k ∘ pick s) (b ∘ pick s) r).mono
    (geometric s hk sep).2).comp (continuous_window s).continuousOn (fun x hx => ⟨x,hx,rfl⟩)

/-- Same-cutoff convergence of the entire original signed connected triple,
uniformly on compact separated arrays before the position test is applied. -/
theorem original (hG : G.Simple) (admit : ∀ i (a : Term p k i),R.family.ref a.2.size ≤ L.level r)
    {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in (cal.cuts : Filter UVIndex),∀ x∈K,
      ‖value (cut L Q p k b r z x) - value (continuum L cal Q p k b r x)‖ < ε := by
  let A := continuum L cal Q p k b r
  let B := cut L Q p k b r
  let V := A '' K
  have vc : IsCompact V := hk.image_of_continuousOn (continuous_roster L cal Q p k b r hk sep)
  let W := cthickening (1:ℝ) V
  have wc : IsCompact W := vc.cthickening
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp
    (wc.uniformContinuousOn_of_continuous continuous_value.continuousOn) ε he
  have dpos : 0 < min 1 δ := lt_min one_pos hδ
  have allm : ∀ᶠ z : UVIndex in (cal.cuts : Filter UVIndex),∀ s : Badge,∀ x∈K,
      dist (B z x s) (A x s) < min 1 δ := by
    apply Filter.eventually_all.mpr
    intro s
    obtain ⟨compact,apart⟩ := geometric s hk sep
    have hs := WilsonPositionThermometerCells.cells L cal Q (p ∘ pick s) (k ∘ pick s) (b ∘ pick s) r hG
      (fun j t => admit (pick s j) t) compact apart dpos
    filter_upwards [hs] with z hz x hx
    simpa only [dist_eq_norm,A,B,cut,continuum] using hz (window s x) ⟨x,hx,rfl⟩
  filter_upwards [allm] with z hz x hx
  have near : dist (B z x) (A x) < min 1 δ := (dist_pi_lt_iff dpos).mpr (fun s => hz s x hx)
  have av : A x ∈ V := ⟨x,hx,rfl⟩
  have bw : B z x ∈ W := mem_cthickening_of_dist_le (B z x) (A x) 1 V av
    (near.le.trans (min_le_left _ _))
  simpa only [dist_eq_norm] using
    move (B z x) bw (A x) (self_subset_cthickening V av) (near.trans_le (min_le_right _ _))

end YM.Integration.WilsonPositionThermometerConnected
