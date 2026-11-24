import YM.UVNext.COMMON_GRADE_ASSEMBLY.Coordinates
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Stage
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Tables

/-!
# Grade estimates on a common Wilson family

`Recorder` takes a calibrated family and requests the center bound,
relay costs, detectors, rank and grid estimates on the indicated
refinements. `Instruments` states these inputs in terms of persistent,
on-demand estimates. The construction uses the periods of the given
family throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Push.Common Snap Push.CutoffProjectors Dash
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {b : Presentation C}

/-- Requirements on a fixed presentation and extraction order. On refinements, the relay and detector estimates share their indicated stage, while rank, grid and exterior inputs retain their own hypotheses. -/
structure Recorder (C : Family G) (b : Presentation C) (f : Extraction.Order) : Prop where
  active : C.Makes
  calibrated : Calibrated C
  center : CenterPort C f
  fee : Affordable b f
  after_snap (g : Extraction.Order) (w : Snap C) : First w b (f.refine g) →
    Stationed (f.refine g) (fun d r => RelayCosts b r d ∧ Detector b r d)
  rank (g : Extraction.Order) (w : Snap C) (u : Upper w) : Risen u b (f.refine g) →
    Push.Common.Stock b u.T (f.refine g)
  grid (g : Extraction.Order) (w : Snap C) (u : Upper w) (D : Holder u.T) : Risen u b (f.refine g) → D.Income b (f.refine g) →
    GrillInputs C (f.refine g)
  approaches (g : Extraction.Order) (w : Snap C) (u : Upper w) : Risen u b (f.refine g) → AfterHost u b (f.refine g)







/-- On-demand estimates for one presentation, fixed free data and the indicated extraction order. The cutoff, rank, heat and grid clauses below specify the additional inputs to the assembly. -/
structure Instruments {T : Table C.book} (A : Campaign C) (X : Offers T) (a : FreeInput C) (f : Extraction.Order) : Prop where
  center : CenterPort C f
  relay : OnDemand f fun d u => RelayCosts A.presentation u d
  search : OnDemand f fun d u => Detector A.presentation u d
  -- No separate fee/d-upper estimate IF injective at physical cutoff &
  -- RFREE residual problem solved. Use `Cardinal` (outer period threshold
  -- before eventual mesh), not necessarily all cutoffs.
  at_cut : Cardinal A f
  freeInputs : (∀ d, Maxwell.residual G d = ⊥) ∧ a.Divergence
  estimates : EarlyRank X f
  heat : Study C f
  -- weak estimates here already *persistent*, can be ordered earlier or later.
  base : OnDemand f (WeakBill C a.kernels.spin)
  -- need actual shell estimates whenever asked after entering compatible Base (Born)
  -- could postpone even further as in `AfterHost`. Supplies even conditional on
  -- the existence of centered nonzero current as in main campaign; use
  -- ProbeDemand (can buy m,y estimates on finer stations).
  asks : ∀ g (w : Snap C) (u : Upper w) (H : Risen u A.presentation (f.refine g)),
    (∃ J : u.T.Stress, J ∈ KernelSpace H.base.kernel.spin ∧ J≠0 ∧ Conserved u.V H.base.kernel.spin J) →
    ProbeDemand (f.refine g) H.base.kernel u.V

private lemma owns {ι : Type*} [Countable ι] {P U : ι → Extraction.Order → Prop} (h : OnDemand f P)
    (p : OnDemand f U) (H : ∀ i b c,Tails c b → P i b → P i c) : Stationed f fun i u => P i u ∧ U i u := by
  apply OnDemand.stations; intro i k
  obtain ⟨x,hx⟩ := h i k
  obtain ⟨y,hy⟩ := p i (k.refine x)
  exact ⟨x.refine y,H _ _ _ (Tails.refine ((f.refine k).refine x) y) hx,hy⟩

theorem projector_clocks {T : Table C.book} (A : Campaign C) (X : Offers T) (a : FreeInput C)
    (h : Instruments A X a f) (hc : Calibrated C) : Recorder C A.presentation f where
  active := A.cutoff
  calibrated := hc
  center := h.center
  fee := A.costs f
  after_snap _g _w _p := owns (demand_persists h.relay (Tails.refine ..))
    (demand_persists h.search (Tails.refine ..)) (fun _ _ _ t e => t.relay e)
  rank _g _w _u p := h.estimates.jobs p (Tails.refine ..)
    (Cardinal.comparison A (h.at_cut.persists (Tails.refine ..)) p h.freeInputs.1)
  grid _g _w _u _D p _ := charges_grid h.heat p (Tails.refine ..)
  approaches g w u p := posts a h.freeInputs.2 p.base.kernel ⟨demand_persists h.base (Tails.refine ..),h.asks g w u p⟩ _





end YM.UVNext.Grade
