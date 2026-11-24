import YM.Integration.WilsonMatrixTicketLanesMirrorAccuracy
import YM.Integration.ActualRelativeProfileTrial

/-! Complete coefficients at a prefiled physical reporting level on the original ordered regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedProfiles
open Filter Lattice RG FVA2 FVA2.CityHistory FVA2.Both.Passage FVA2.Both.Passage.Cohort
open FormalOPE.RG10.BlockGauge MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge WilsonMatrixTicketLanesMirrorClock
open scoped Topology Classical BigOperators
variable {G : Gauge} {B : Deck G} {I : Type}

/-- The history is the retained physical segment at this period, including the original slice choices. -/
def panel (R : Run G) (b : ℕ) (depth : I → ℕ)
    (σ : (w : ActualOuterQuarterProfile.Cutoffs I) → Picks R.family.path w.2.2) (w : ActualOuterQuarterProfile.Cutoffs I) :
    Fabric G (dimT (ActualOuterQuarterProfile.lengths R.family.S (fun i => b+depth i)) w) := by
  change Fabric G (periodN (ActualCoarseQuarterProfile.halfSide R.family.S (b+depth w.1) w.2.2))
  exact (ActualCoarseQuarterProfile.dimension R.family.S (b+depth w.1) w.2.2).symm ▸
    segment R.family.path w.2.2 b (σ w) (depth w.1)

private theorem cast_exhibit {m n : Side} (he : m=n) (L : Fabric G m) (paid : Long L) (E : Exhibit L)
    (stock : ∀ V : Warehouse G, CapReady.Article V L E paid) :
    ∃ (p : Long (he ▸ L)) (e : Exhibit (he ▸ L)), e.chart=E.chart ∧ e.quotes=E.quotes ∧
      ∀ V : Warehouse G, CapReady.Article V (he ▸ L) e p := by
  subst n
  exact ⟨paid,E,rfl,rfl,stock⟩

/-- The unshifted relative locations are the native right-ceil probe locations. The order of the UV and period limits is preserved. -/
theorem original (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B)
    (matched : TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) B) A) (simple : G.Simple) :
    ∀ᶠ b : ℕ in atTop, ∀ (l : Filter I) (f : Extraction.Order) (u : Filter (ℕ×ℕ)), u ≤ f.fuse →
      ∀ (depth : I → ℕ) (σ : (w : ActualOuterQuarterProfile.Cutoffs I) → Picks R.family.path w.2.2)
        (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a), Tendsto θ l atTop → ∀ (μ : ℝ) (n : ℕ)
        (z : I → Fin n → MS.Tone.QP) (K η : ℝ), 0 ≤ K → 0 < η →
        (∀ a i, ‖z a i‖ ≤ K) → (∀ a i j, i ≠ j → η ≤ ‖z a i-z a j‖) →
        (∀ a, 4*Real.exp (-θ a) ≤ η) →
        let P := ActualRelativeProfileTrial.trial R (fun a => b+depth a) θ hθ μ z
        let L := panel R b depth σ
        ∃ (paid : ∀ i, Long (L i)) (E : ∀ i, Exhibit (L i)),
          (∀ i, (E i).chart=R.metals.O ∧ (E i).quotes=quotes R.family.path i.2.2 b (depth i.1) ∧
            ∀ V : Warehouse G, CapReady.Article V (L i) (E i) (paid i)) ∧
          ∀ (v : Fin n → Label B) (s : Finset (Fin n)) (q : ℕ),
            PeakT.twin (l.curry u) P.profile mildG
              (fare (Label.h ∘ v) P.profile (WilsonMatrixTicketLanesMirrorAccuracy.receipts
                (WilsonMatrixTicketLanesNativePrices.warehouse R) P A μ v L E) s q)
              (fun i => Dial.tour M v μ (testP P i) s q) := by
  filter_upwards [WilsonMatrixTicketLanesMirrorFabric.original R] with b funded l f u hu depth σ θ hθ hd μ n z K η hK hη hz hsep mesh
  let N := fun a => b+depth a
  let P := ActualRelativeProfileTrial.trial R N θ hθ μ z
  let L := panel R b depth σ
  have stock (w : ActualOuterQuarterProfile.Cutoffs I) : ∃ (p : Long (L w)) (E : Exhibit (L w)),
      E.chart=R.metals.O ∧ E.quotes=quotes R.family.path w.2.2 b (depth w.1) ∧
      ∀ V : Warehouse G, CapReady.Article V (L w) E p := by
    obtain ⟨p,E,chart,beta,_,loans⟩ := funded w.2.2 (depth w.1) (σ w)
    obtain ⟨p',E',hchart,hbeta,hloans⟩ := cast_exhibit
      (ActualCoarseQuarterProfile.dimension R.family.S (N w.1) w.2.2).symm _ p E loans
    exact ⟨p',E',hchart.trans chart,hbeta.trans beta,hloans⟩
  choose paid E hE using stock
  refine ⟨paid,E,hE,?_⟩
  intro v s q
  have originalUse := ActualRelativeProfileTrial.uses R l f N θ hθ hd μ z K η hK hη hz hsep mesh
  have below : l.curry u ≤ ActualOuterQuarterProfile.nested l f := by
    intro s hs
    exact eventually_curry_iff.mpr ((eventually_curry_iff.mp hs).mono fun _ h => hu h)
  have used : Uses P (l.curry u) μ := ⟨originalUse.total, originalUse.knit, originalUse.reality,
    originalUse.upright.mono_left below, fun h => below (originalUse.super h), originalUse.clear, originalUse.wind⟩
  exact WilsonMatrixTicketLanesMirrorAccuracy.original R M A matched simple P μ v (l.curry u) used L paid E
    (fun i => (hE i).2.2 _) s q

end YM.Integration.WilsonMatrixTicketLanesReportedProfiles
