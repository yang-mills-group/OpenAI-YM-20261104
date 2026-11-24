import YM.Integration.WilsonMatrixTicketLengthsCatalog
import YM.OPE.Compatible.Brou.Pole
import YM.OPE.Compatible.Aq.Hack

/-! The complete retained sheet and the independently issued finite-frame price book on its original catalogue. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLengths
open Function Filter Lattice RG Source Wilson Precision RG.Supply Input
open PhysicalNext PhysicalNext.ThroughLaunch Further.StrongStartup Extra.Histories
open Next.Foundations Org OPE
open scoped Topology BigOperators Classical
variable {G : Gauge}

/-- All fields except the requested future block sequence are chosen on the
one retained sheet. The original kinetic invoice retains its own free and
stationary sectors. -/
structure Offer (G : Gauge) (K : KernelChoices) (v : Orders) (C : ℕ → ℝ) where
  sheet : Sheet G
  price : MapPrices
  sponsor : Votive.Sponsor G
  season : Votive.Seasons sponsor
  ledger : Stroke.PriceBook (chart_ok G) season
  slope : ℕ → ℝ
  worth : Bid.Worth
  kernel : sheet.kernel = K
  stage : WithStage sheet v
  issued : Votive.Lend sheet season
  invoices (fees : Tariffs) (scope : Extra.Multi.Scope) :
    ∃ f : ℕ → ℕ, Perceived sheet sponsor.X price sponsor.l slope C worth fees scope f

/-- The director freezes its frame sources and their prices on the same
sheet before requesting a length, startup tariff, scope or extraction. -/
theorem available {K : KernelChoices} (simple : G.Simple) (branches : ∀ P : Patch, P.Branches K G)
    {v : Orders} (plan : Draft v) (C : ℕ → ℝ) (hC : ∀ i, 1 ≤ C i) :
    Nonempty (Offer G K v C) := by
  obtain ⟨s,O,T,l,γ,w,⟨x,b,free,clip⟩,hk,stage,invoice⟩ :=
    WilsonMatrixTicketLengthsCatalog.purchase simple branches plan C hC
  let H : Votive.Sponsor G := ⟨K,O,l,x,b,free,branches⟩
  obtain ⟨A,widths,paths,book⟩ := Stroke.forge H (chart_ok G) simple
    (fun i => (s.profile i).width) (fun i => (s.profile i).paths)
    (fun i => (s.profile i).width_pos)
  exact ⟨⟨s,T,H,A,book,γ,w,hk,stage,⟨hk,clip,widths,paths⟩,invoice⟩⟩

end YM.Integration.WilsonMatrixTicketLengths
