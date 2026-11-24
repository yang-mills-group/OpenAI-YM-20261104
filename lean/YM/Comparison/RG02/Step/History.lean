import YM.Comparison.RG02.Step.Record
import YM.Pert.Asymptotics.RawAxis
/-!
# Same physical step. Ready for local reader at beta of History itself.

 All costs per-argument. Keep `sample` domain in old units. To use with analytic seam/tail estimates
 choose additional window according to **same History**; can compare at every output represented
 by V' here, no carrying a virtual statement to physical step without separate adapter. The log
 re-expression applies EVERY t at chosen temperatures; doesn't assert Clustering/OPE etc. Quantified
 over Family.Makes and the Chain of formal lower steps there. `Floral` supplies from that C; even
 though `.Ord` might hold for another choice etc need not compare to it. Unit test & source bridge
 separately. Can use normalization/log formula with independent upper horizon analytic packets
 afterward. Error support budgets (quantitative contract qev/qelt, leading denominator ratio
 bounds with relative schedules etc.) to RG01/03.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Local.RealStep
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Marker YM.Multi YM.Comparison.RG02.Order Integral Actual
open YM.Extra.Trajectories (connected pass_connected connected_quiet)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}
-- output can bind even if input only measurable gauge, no analytic hypothesis here
lemma pushed {c f : Side} {S : StepData c f} {F : Config G f→ℂ}
    (h : Envelope F) (H : S.patch.Branches S.kernel G) (β : ℝ): Envelope (S.push β F) := by
   apply Envelope.compactC; apply continuous_iff_continuousAt.mpr; intro u
   obtain ⟨C,HC⟩:=h.cost; have he:=h.integrableC (prior G f)
   rw [← continuousWithinAt_univ]; exact  (YM.Push.BetaTransport.push_continuousWithinAt S H (b:=fun _=> β) (F:=fun _=>F) (M:=fun _=> C) continuousWithinAt_const (V:=id) continuousWithinAt_id he (by filter_upwards with a using he.aestronglyMeasurable) (by filter_upwards with a using continuousWithinAt_const) (integrable_const _) (by filter_upwards with z; exact Eventually.of_forall HC) (y:=u)).2
variable {V : Type} [DecidableEq V] [Fintype V] {C : Census V}
    (X : Family G) (N q m : ℕ)
    (L : Bulk.Chain X.path) (hm : m<N)
-- names are in locals so re-imported worker uses reducibility
local notation "H"=> X.path
local notation "R'"=> X.path.rep N q m
local notation "R"=> X.path.rep N q (m+1)
local notation "g"=> YM.Pert.Asymptotics.regulatorRun X N q (m+1)
local notation "g'"=> YM.Pert.Asymptotics.regulatorRun X N q m
local notation "S"=> X.path.levels.clock.op m q
local notation "K"=> L.step N m q hm
-- careful with letbind expand notation
variable (Z : Lit C (Config G (X.side (m+1) q)))
    (W : Bulk.Colors C G (X.side (m+1) q)) (F : Forest (X.path.levels.clock.op m q).ratio) (t : (X.path.levels.clock.op m q).Choices)
    (x : fieldDir G (X.side m q) 1)
variable (hX : X.Makes)
include hX
lemma actual_positive (h : m≤N) : 0 < (R').beta := (half_pos (zero_lt_one.trans ((H).levels.fits.delayed m))).trans_le (hX.wilson.represents N q m h).band.1
lemma coupling_pos (h : m≤N) : 0<g' := inv_pos.mpr (Real.sqrt_pos.mpr (actual_positive X N q m hX h))
lemma trajectory (h : m≤N) : temperature g'=(R').beta := by
   unfold temperature YM.Pert.Asymptotics.regulatorRun; rw [inv_pow, inv_inv, Real.sq_sqrt (by exact (actual_positive X N q m hX h).le : 0 ≤ (H).β N q m)]
include hm
lemma kindred (x : Config G (X.side m q)) : settled R S x=(R').eval x := (congrFun ((hX.wilson.steps N q m hm).1) x).symm
omit [Fintype V] in
theorem opened (h : Floor R Z) (hx : Bulk.Well W) : Opened R K Z g W := by refine ⟨h,Normal.actual _ hX.wilson N q (m+1) hm,hx,coupling_pos X N q _ hX hm,(trajectory X N q _ hX hm).symm⟩

omit [Fintype V] in
theorem advance (h : Floor R Z) : Floor R' (yield R Z S) := by
    have hs s : Actual.atMark s (yield R Z S)=(S).push (R).beta (Actual.atMark s Z):= funext fun i=> congrFun (Actual.grades ..) s
    have hp s : Envelope (Actual.atMark s Z) := h.safe s
    refine ⟨fun y=>?_, fun s=>?_,fun t x=>?_⟩
    · unfold yield; rw [← Normal.scan_actual S (R).beta y Z ((H).levels.blocks m q).branches h.safe, ← kindred X N q m hm hX y]
      exact Normal.scan_bare S _ y _ (R).eval (Normal.actual _ hX.wilson N q (m+1) hm) ((H).levels.blocks m q).branches (fun _=> h.vacancy)
    · change Envelope (Actual.atMark s (yield R Z S)); rw [hs]; exact pushed (hp s) ((H).levels.blocks m q).branches _
    ext i
    change Actual.atMark i (yield R Z S) _ = Actual.atMark i (yield R Z S) _; rw [hs]
    exact Step.push_gauge _ m q (Actual.atMark i Z) ((hp i).integrableC _) (fun p b=>congrArg (·.part i) (h.gauges p b)) _ _ _

omit [Fintype V] in
omit hm hX in
lemma still_full (h : Floor R Z) : charge (prior G _) (yield R Z S)=charge (prior G _) Z := by
   ext i
   rw [Actual.components,Actual.components]; unfold yield
   have he x := show Actual.atMark i (Actual.Push S (R).beta Z) x=_ from congrFun (Actual.grades ..) i
   have hu := (H).levels.transition_mass m q (R).beta
   exact (integral_congr_ae (Eventually.of_forall he)).trans (StepData.push_integral hu _ ((h.safe i).integrableC _))

-- physical endpoint identity, quantities pointwise & no restriction to V healthy
variable (h : Floor (X.path.rep N q (m+1)) Z) (hx : Bulk.Well W)
include h hx
local notation "v"=> sample g x
local notation "F'"=> Bulk.Fk K F t W x
local notation "U" => opened X N q m L hm Z W hX h hx
-- choose any mask window not necessarily at canonical radius
variable (r n : ℕ) (H' : ∀ j:C.Mode,j.val.card ≤ n)

include H' in
/-- Identity on true construction -- analytic comparison uses all the quantities of this step.
 Costs paid separately (WAIT).
 Uses normalized full physical denominator and canonical log model, factorized even at finite r.
 Error terms computed from tabulated `K,office,Fk` & a mask access candidate per V
 and t, plus the named full-charge older & gas/tail inputs, and division defects. No estimates
 presupposed. -/
theorem genuine (y : (S).Choices → Set (F.Slice G)) (hy : ∀ t,MeasurableSet (y t)) (hY : ∀ t, y t⊆zone K (R).p F g x) :
   (R').eval v= office K F t g (levelScalar R) x * Real.exp (exponentPrice (F' r) g + vacuumError R Z K g F t W y x r) ∧
   normalized R Z S v=value (g:ℂ) (Order.ratio (F' r)) + normalizeError R Z K g F t W y x r ∧
   Local.cumulant R Z S v = value (g:ℂ) (logMarked (F' r)) + markingError R Z K g F t W y x r n ∧
   Actual.Push S (R).beta Z v = Complex.ofReal ((R').eval v) • (Local.cumulant R Z S v).pass := by
   rw [← kindred X N q m hm hX v]; refine ⟨(U).unmarked_price F t y x r hy hY,(U).normalized_eq F t y x r hy hY,(U).marked_eq F t y x r hy hY n H',?_⟩
   change yield _ _ _ _=_; rw [(U).receipt F t y x r hy hY n H', (U).unmarked_price F t y x r hy hY, (U).marked_eq F t y x r hy hY n H']

omit h hx in
/-- Specialize at a field stream in reset coordinates (already chosen actual coupling). No
    `β-hat` replacement, much less a solution for the needed formula counter. -/
lemma reflow : sample g ((g'/g) • x)=sample g' x := by
   unfold sample; rw [smul_smul, mul_div_cancel₀ ..]; exact (coupling_pos X N q (m+1) hX hm).ne'
end YM.Comparison.RG02.Local.RealStep
