import YM.Integration.WilsonPositionSeparatedProfileMayerThermalElection

/-! One jointly elected original reporting book for all eligible thermal degrees and finite registered rosters. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerElection
open Function Filter Set Lattice Wilson Pressure RG Tree Precision Marker
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.JointLoad.Heir.Suite
open PhysicalNext.JointLoad.Psalm Supply Input Org Testing
open Push Push.PriceCompiler Push.SectorMeasure Next.Scheduling
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open QLocalRequestedHeirQuote QLocalRequestedHeirPurchase QLocalRequestedSectorSale
open scoped Topology BigOperators Classical

variable {G:Gauge} {V:Type} (J:Request V)

open WilsonPositionSeparatedProfileMayerThermalElection (Sales)
abbrev Demand (G:Gauge):=∀{P:Teller G},ConnectedActivityE6.Target G P→Patch→Booking G→ℕ→ℝ→Prop
def Mature (test:Demand G):Prop:=∀{P:Teller G} (Q:ConnectedActivityE6.Target G P) (D:Patch) (b:Booking G) (j:ℕ),
  ∀ᶠx:ℝ in atTop,test Q D b j x

def plus (u v:Demand G):Demand G:=fun t d b j x=>u t d b j x ∧ v t d b j x
theorem paired {u v:Demand G} (hu:Mature u) (hv:Mature v):Mature (plus u v):=
  fun Q D b j=>(hu Q D b j).and (hv Q D b j)

private theorem all_fields {P:Teller G} (Q:ConnectedActivityE6.Target G P) (D:Patch) (b:Booking G) (j:ℕ):∀ᶠ x:ℝ in atTop,Sales J Q D b j x:=by
  classical
  by_cases geometry:D.Branches (teller J P).bind G
  · apply Filter.eventually_all.2;intro n;apply Filter.eventually_all.2;intro d;apply Filter.eventually_all.2;intro p
    exact WilsonPositionSeparatedProfileMayerThermalOrder.before (fun i=>(d i).val) (teller J P) D.L D geometry b.order p.val j _ (by positivity)
  exact Eventually.of_forall fun x n d p run c f S T R Q' μ C H same=>False.elim (geometry (same ▸ H.laws.data.funds.funds.kernel))

variable (Δ : Daisy.Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)

def Commissioned (test:Demand G) : Prediction G := fun {M} {D} {A} H =>
  ∃ b : ℕ → ℕ → Booking G,
    (∀ j i, StepStages j i → Earlier J M.p M.K extra j i (D.L j).val) ∧
    ∀ j x, A.delay.betaEntry j≤x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
      QLocalRequestedSectorSale.Window J Δ (H.target j i) (libretto J M.p M.K j i) (b j i)
        (Clockwork.patch D st fr) x γ ∧ Thermal G (D.L j) j (extra (M.p.profile i) i) x ∧
      Sales J (H.target j i) (Clockwork.patch D st fr) (b j i) j x ∧ test (H.target j i) (Clockwork.patch D st fr) (b j i) j x

theorem projected (test:Demand G) {R:Run G} (sold:Commissioned J Δ extra γ test R.kit):
    WilsonPositionSeparatedProfileMayerThermalElection.Commissioned J Δ extra γ R.kit:=by
  obtain ⟨b,early,ready⟩:=sold
  exact ⟨b,early,fun j x h i st fr=>let z:=ready j x h i st fr;⟨z.1,z.2.1,z.2.2.1⟩⟩

theorem prepaid (test:Demand G) (due:Mature test) (hG : G.Simple) (hγ : -(1/2:ℝ)<γ) (s : Sheet G) (K : MapPrices) :
    Prepaid (Commissioned J Δ extra γ test) s K := by
  intro Q E c C₀ z₂ b hW
  obtain ⟨u,_,_,h⟩ := collect_upper s.floorL
    (fun j L => ∀ i, StepStages j i → Earlier J s K extra j i L ∧ floor J (Q j i) Δ≤L)
    (fun j => eventually_transitions j _ _ (fun i _ =>
      (earlier J s K extra j i).and (eventually_ge_atTop (floor J (Q j i) Δ))))
  refine ⟨u,fun l hl D _ _ _ _ _ _ _ _ V' _ => ?_⟩
  have gate (j i) (st : StepStages j i) := h j (D.L j).val ((hl j).trans (D.large j).need) i st
  have rows (j i : ℕ) : ∃ b : Booking G, ∀ᶠ x : ℝ in atTop,
      ∀ (st : StepStages j i) (fr : s.first ≤ i),
        QLocalRequestedSectorSale.Window J Δ (Q j i) (libretto J s K j i) b (Clockwork.patch D st fr) x γ ∧
          Thermal G (D.L j) j (extra (s.profile i) i) x ∧
          Sales J (Q j i) (Clockwork.patch D st fr) b j x ∧ test (Q j i) (Clockwork.patch D st fr) b j x := by
    by_cases h : (StepStages j i ∧ (s.first ≤ i))
    · obtain ⟨b,hb⟩ := QLocalRequestedSectorSale.sale J hG Δ (Q j i) (Clockwork.patch D h.1 h.2)
        (libretto J s K j i) (s.has _) (gate j i h.1).1.seam (gate j i h.1).2
        (calibrated J s K j i).2.2 γ hγ
      exact ⟨b,(hb.and ((thermal_after G (D.L j) j (extra (s.profile i) i)).and ((all_fields J (Q j i) (Clockwork.patch D h.1 h.2) b j).and (due (Q j i) (Clockwork.patch D h.1 h.2) b j)))).mono fun _ hx _ _ => hx⟩
    exact ⟨vacant G,Eventually.of_forall fun _ st fr => (h ⟨st,fr⟩).elim⟩
  choose b hb using rows
  obtain ⟨β,_,hv,hβ⟩ := collect_upper V'.betaEntry _
    (fun j => eventually_transitions j _ _ (fun i _=>hb j i))
  refine ⟨{V' with betaEntry:=β},⟨hv,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W hW K' I' hp B' B η q E' X J' K'' b' hZ hY hm
  exact ⟨b,fun j i st => Earlier.raised J s K (gate j i st).1 l,
    fun j x hx i st fr => hβ j x ((hW.beta j).trans hx) i st st fr⟩

theorem original {M:Metals G} {D} {A} {H} (test:Demand G) (earned:Commissioned J Δ extra γ test (M:=M) (D:=D) (A:=A) H):
    QLocalRequestedSectorCalendar.Paid J Δ extra γ H:=by
  obtain ⟨b,early,windows⟩:=earned
  exact ⟨b,early,fun j x hx i st fr=>⟨(windows j x hx i st fr).1,(windows j x hx i st fr).2.1⟩⟩

end YM.Integration.WilsonCoherentMayerElection
