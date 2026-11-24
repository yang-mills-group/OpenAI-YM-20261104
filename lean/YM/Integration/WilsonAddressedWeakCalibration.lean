import YM.Integration.WilsonAddressedWeakPointGram
import YM.Integration.WilsonAddressedWeakAncestor

/-! The two-site weak detector at actual projected ancestors. Its free
comparison tolerates the genuine fine-cell displacement of both probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonAddressedWeakCalibration
open Function Filter Set Metric MeasureTheory Lattice Wilson RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Next.Rank Edition Baler Value Glyph Thirst Alarm
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone
open Extraction Table Spec OPE OPE.Orbits PhysMS XSpace XSpace.Normalize Trace Trace.Pilot
open WilsonThermometerOffsetTrajectory WilsonAddressedWeakPointCells
open scoped Classical BigOperators Topology

variable {G : Gauge} (R : Run G) {B : Local.Physical.Deck G} {O : Booked B}
variable (M : MS_Data G O) {D k N p : ℕ}

def lifts (live : k ≤ N) (ρ : ℝ) (hr : 0 < ρ) (x : Points 2) :=
  (WilsonAddressedWeakAncestor.original R N p k live ρ hr x).choose

def projected (live : k ≤ N) (ρ : ℝ) (hr : 0 < ρ) (x : Points 2) : Points 2 :=
  ρ⁻¹ • tag (R.family.S.a k) (lifts R (p:=p) live ρ hr x)

theorem actual (live : k ≤ N) (ρ : ℝ) (hr : 0 < ρ) (x : Points 2) :
    (∀ i, (R.family.S.toDepth live p).parent (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x i) =
      wrap (R.family.side k p) (lifts R (p:=p) live ρ hr x i)) ∧
    dist (projected R (p:=p) live ρ hr x) x ≤ 16 * (R.family.S.a k / ρ) :=
  (WilsonAddressedWeakAncestor.original R N p k live ρ hr x).choose_spec

private theorem window (φ : Test 2) (μ τ : ℝ) (tp : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ tsupport φ, ∀ y : Points 2, dist y x < c →
      ∀ a b : Glyph B D, ‖MSDeckProbeGram.raw M ![a,b] y μ 0 - MSDeckProbeGram.raw M ![a,b] x μ 0‖ ≤ τ := by
  let K := tsupport φ
  let F (z : Points 2) (u : Glyph B D × Glyph B D) := MSDeckProbeGram.raw M ![u.1,u.2] z μ 0
  obtain ⟨v,hv,room⟩ := φ.hasCompactSupport.exists_cthickening_subset_open (conf_open 2) φ.tsupport_subset
  let J := cthickening v K
  have compact : IsCompact J := φ.hasCompactSupport.cthickening
  have smooth : ContinuousOn F J := by
    apply continuousOn_pi.mpr
    intro u z hz
    have chart : Continuous (Fountain.metric (m:=2)) := by
      apply continuous_pi
      intro i
      exact Theater.out.toLinearMap.continuous_of_finiteDimensional.comp
        ((continuous_apply i).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E4)).continuous)
    have legal : Injective (Fountain.metric z) := Theater.out.injective.comp (room hz)
    exact ((Dial.contin M (labelAt B ∘ ![u.1,u.2]) (Fountain.metric z) legal Finset.univ 0 μ).1.comp
      chart.continuousAt).continuousWithinAt
  obtain ⟨δ,hd,compare⟩ := Metric.uniformContinuousOn_iff.mp
    (compact.uniformContinuousOn_of_continuous smooth) τ tp
  refine ⟨min v δ,lt_min hv hd,?_⟩
  intro x hx y hit a b
  have hy : y ∈ J := mem_cthickening_of_dist_le y x v K hx ((lt_min_iff.mp hit).1.le)
  have hx' : x ∈ J := mem_cthickening_of_dist_le x x v K hx (by simpa using hv.le)
  have cmp : ‖F y - F x‖ ≤ τ := by
    simpa only [dist_eq_norm] using (compare y hy x hx' (lt_min_iff.mp hit).2).le
  exact ((pi_norm_le_iff_of_nonneg tp.le).mp cmp) (a,b)

theorem original (V : Warehouse G) (D : ℕ) (μ : ℝ) {v : E4} (away : (0:E4) ≠ v)
    (room : Set (Points 2)) (near : room ∈ 𝓝 (Extra.FD.couple 0 v)) (ε : ℝ) (hp : 0 < ε) :
    ∃ (φ : Test 2) (η c : ℝ), tsupport φ ⊆ room ∧ (∫ x, φ x)=1 ∧ 0 < η ∧ 0 < c ∧
      let K := MSSeparatedTestGram.matrix M D μ 0 φ
      IsUnit K ∧ ∀ (d : Fin 2 → ℕ) (k N p : ℕ) (live : k ≤ N)
        (Y : Glyph B D → Glyph B D → PointSites R N p → (i : Fin 2) → Palette R.family (d i))
        (U : Glyph B D → Glyph B D → PointSites R N p → (i : Fin 2) → Emblems R.family (d i))
        (face : (Stock.census (Fin 2)).Mode) (ρ : ℝ) (hr : 0 < ρ), 16*(R.family.S.a k/ρ) < c →
        (∀ (a b : Glyph B D) (x : Points 2), φ x ≠ 0 →
          let o := WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x
          ‖reading R d o (Y a b o) (U a b o) live face -
            MSDeckProbeGram.raw M ![a,b] (projected R (p:=p) live ρ hr x) μ 0‖ ≤ η) →
        let A := WilsonAddressedWeakPointGram.measured R d live Y U face φ ρ
        IsUnit A ∧ ∀ a b, ‖A⁻¹ a b - K⁻¹ a b‖ < ε := by
  obtain ⟨φ,t,hs,hm,ht,good,allowed⟩ := WilsonAddressedWeakPointGram.original R M V D μ away room near ε hp
  obtain ⟨c,hc,hits⟩ := window M (D:=D) φ μ (t/2) (half_pos ht)
  refine ⟨φ,t/2,c,hs,hm,half_pos ht,hc,good,?_⟩
  intro grades k N p live Y U face ρ hr mesh hearing
  apply allowed grades k N p live Y U face ρ
  intro a b x hx
  let y := projected R (p:=p) live ρ hr x
  have close : dist y x < c := ((actual R (p:=p) live ρ hr x).2).trans_lt mesh
  have first := hearing a b x hx
  have second := hits x (subset_closure hx) y close a b
  calc _ ≤ _ := norm_sub_le_norm_sub_add_norm_sub _ (MSDeckProbeGram.raw M ![a,b] y μ 0) _
       _ ≤ t := by linarith only [first,second]

end YM.Integration.WilsonAddressedWeakCalibration
