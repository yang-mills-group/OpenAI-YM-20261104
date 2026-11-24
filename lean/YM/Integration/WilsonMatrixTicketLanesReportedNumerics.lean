import YM.Integration.WilsonMatrixTicketLanesReportedCurrency
import YM.Integration.ActualRelativeProfileTrial

/-! Convert the paid signed finite RG10 to MS coefficient into every power of the true running coupling along the original eventual UV and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesReportedNumerics
open Filter Lattice RG FVA2 FVA2.CityHistory FVA2.Both.Passage FVA2.Both.Passage.Cohort
open FormalOPE.RG10.BlockGauge MS MS.Rake MS.Land MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Local.Physical
open PhysicalNext.Repeat.Legato RegulatorIR.FVAAlt2.Lodge WilsonMatrixTicketLanesMirrorClock
open scoped Topology Classical BigOperators
variable {G : Gauge} {B : Deck G} {I : Type}

private theorem later (f : Extraction.Order) (m : ℕ) : ∀ᶠ w in f.fuse, m ≤ w.1 := by
  rw [Extraction.Order.fused, Extraction.Order.late]
  exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually (eventually_ge_atTop m)

/-- Each level is filed before the ultraviolet and period limits. All marked labels, coefficient orders,
requested suppression orders and positive fees follow the same original funded finite forest. -/
theorem original (R : Run G) {O : Booked B} (M : MS_Data G O) (A : Prescription B)
    (matched : TaylorOKPl M (FVAAlt2.Lobby.Table (basisR R) B) A) (simple : G.Simple) :
    ∀ᶠ b : ℕ in atTop, ∀ (l : Filter I) (f : Extraction.Order) (u : Filter (ℕ×ℕ)), u ≤ f.fuse →
      ∀ (m : I → ℕ), Tendsto m l atTop → ∀ (c : ℝ), 1 < c →
      ∀ (depth : I → ℕ) (σ : (w : ActualOuterQuarterProfile.Cutoffs I) → Picks R.family.path w.2.2)
        (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a), Tendsto θ l atTop → (∀ᶠ a in l, (RG16.Lambda R.family.path.levels (m a))^c ≤ θ a) → ∀ (μ : ℝ) (n : ℕ)
        (z : I → Fin n → MS.Tone.QP) (K η : ℝ), 0 ≤ K → 0 < η →
        (∀ a i, ‖z a i‖ ≤ K) → (∀ a i j, i ≠ j → η ≤ ‖z a i-z a j‖) →
        (∀ a, 4*Real.exp (-θ a) ≤ η) →
        let P := ActualRelativeProfileTrial.trial R (fun a => b+depth a) θ hθ μ z
        let L := WilsonMatrixTicketLanesReportedProfiles.panel R b depth σ
        ∃ (paid : ∀ i, Long (L i)) (E : ∀ i, Exhibit (L i)),
          (∀ i, (E i).chart=R.metals.O ∧ (E i).quotes=quotes R.family.path i.2.2 b (depth i.1) ∧
            ∀ V : Warehouse G, CapReady.Article V (L i) (E i) (paid i)) ∧
          ∀ (v : Fin n → Label B) (s : Finset (Fin n)) (q : ℕ),
            ∀ (order : ℕ) (fee : ℝ), 0 < fee → ∀ᶠ w in l.curry u,
              ‖fare (Label.h ∘ v) P.profile (WilsonMatrixTicketLanesMirrorAccuracy.receipts
                (WilsonMatrixTicketLanesNativePrices.warehouse R) P A μ v L E) s q w -
                Dial.tour M v μ (testP P w) s q‖ ≤ fee *
                Pert.Asymptotics.regulatorRun R.family w.2.1 w.2.2 (m w.1) ^ order := by
  filter_upwards [WilsonMatrixTicketLanesReportedProfiles.original (I:=I) R M A matched simple] with
    b budget l f u hu m hm c hc depth σ θ hθ hd rent μ n z K η hK hη hz hsep mesh
  obtain ⟨paid,E,authentic,promised⟩ := budget l f u hu depth σ θ hθ hd μ n z K η hK hη hz hsep mesh
  refine ⟨paid,E,authentic,?_⟩
  intro v s q order fee hfee
  obtain ⟨C,hC,estimate⟩ := (promised v s q).2
  have convert := hm.eventually (WilsonMatrixTicketLanesReportedCurrency.paid R simple hc mild_p hC.le hfee order)
  have billed : ∀ᶠ w in l.curry u,
      C * Real.exp (-mildG * θ w.1) ≤ fee * Pert.Asymptotics.regulatorRun R.family w.2.1 w.2.2 (m w.1) ^ order := by
    apply eventually_curry_iff.mpr
    filter_upwards [convert,rent] with a funded gap
    filter_upwards [hu (later f (m a))] with raw old
    exact funded (θ a) gap raw.1 raw.2 old
  filter_upwards [estimate,billed] with w near cash
  exact near.trans cash

end YM.Integration.WilsonMatrixTicketLanesReportedNumerics
