import YM.GapsContact.Slab.Receipt
import YM.GapsContact.PhaseTrace
/-!
# A Wilson theory with homogeneous trace calibration admits a **uniformly bounded log-price**
short slab through every prescribed finite horizon.

Beyond the conditional `Workplace`-style estimates, we apply it here to the real physical
calibration already known (cap four parity sector X — not the kcert scheme). None of the fields
are replaced in the analytic continuation or when evaluating actor phases. `FieldComparison`
gives the matching-to-leading and trace/E prediction data in EXACTLY this frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact
open Function Filter Set Extraction Table Spec Trace Trace.Target TraceExtension Trace.Pilot
open Trace.Terrace Trace.Over Trace.Pith Climb Spin Ascent EveryPhase Next.UVStress Boundary
open Analysis MeasureTheory Push.FiniteDetection.Free
open scoped Topology BigOperators InnerProductSpace Classical NNReal ContDiff
universe u
variable {G: Gauge} {C: Family G} {f:Extraction.Order} {S:Table C.book}
variable (F : Final C f S) (hG:G.Simple)
variable {H:(Climb.Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C} {P P':ℝ→change S 4}{κ d e:ℝ→ℝ}
local notation "D"=>Bel C.book

-- A price interface that applies also to other post-position beam suppliers later. Enough to
-- exhibit a normalized adjoint Euclidean mate pair at fixed shape in this geometry. In the
-- Trace comparison the coupling step is `glo`; unchanged here even for a character estimate.
def Measured (F:Final C f S) (d:ℕ)(v:ℝ→S.Field d) := ∃ A:ℝ,0 < A∧∀ᶠ r in trail,cost F d r (v r) ≤ A

include hG
open OPE.Levy in
lemma positions4 (hp: FieldComparison F H Z P P' κ d e) (x:(Bel C.book).Field 4) : Measured F 4 (fun t=>P' t x):= by
  let f:= OPE.Levy.reflect (C:=C) 4 x; let v : Fin 2 → (Bel C.book).Field 4 := ![x,f]
  let y:Points 2:=detectors; let a:= (D).classMoment (D) (fun _=>4) y v
  refine ⟨Real.sqrt (1+‖a‖),by positivity,?_⟩
  filter_upwards [hp.alignment.spun, Trace.Pilot.jets F.room.kernel H P' hp.positions v 0 _ isCompact_singleton (Set.singleton_subset_iff.mpr detectors_in) 1 one_pos] with t he ht
  have hF : P' t f = flipField F 4 (P' t x):= by
    unfold f reflect flipField
    -- signed action matches real O
    rw [← F.phase.transport.spots.signed,← (baseRights (C:=C) (H:=H) hG).signed]
    rw [he.align.axis,he.align.real]
  unfold Ascent.cost; rw [← hF]; apply Real.sqrt_le_sqrt
  let y' (x:Points 2):= S.classMoment S (fun _=>4) (t • x) (fun i=>P' t (v i)); let U(x:Points 2):= (D).classMoment (D) (fun _=>4) x v
  have hc:= ht y rfl; change ‖iteratedFDeriv ℝ 0 y' y-iteratedFDeriv ℝ 0 U y‖ < 1 at hc
  rw [show iteratedFDeriv ℝ 0 y' y- iteratedFDeriv ℝ 0 U y=iteratedFDeriv ℝ 0 (y'-U) y by ext; simp,norm_iteratedFDeriv_zero,Pi.sub_apply] at hc
  rw [show valTwo S 4 _ _ _ = y' y from ?_]
  swap
  · unfold valTwo y'; apply DFunLike.congr_arg; ext1 i; fin_cases i<;> rfl
  calc
    _ ≤ ‖y' y-U y‖+‖U y‖:= (le_of_eq (congrArg norm (sub_add_cancel ..).symm)).trans (norm_add_le ..)
    _ ≤ _:=add_le_add_left hc.le _

structure Roll (F: Final C f S) (h:G.Simple) (L:Almanac F) : Prop extends Flight.{u} F h L where
    slabs (d:ℕ) : ∃ (R:ℝ)(A:ℝ)(m:ℕ),0<R∧1≤A ∧ OpenSky F d R A m
    calibration : ∀ H Z P P' κ d e, FieldComparison F H Z P P' κ d e →
       ∀ x:(Bel C.book).Field 4, Measured F 4 (fun t=>P' t x)

lemma Roll.ofFlight {L:Almanac F}(A: Flight.{u} F hG L) : Roll.{u} F hG L := by
  obtain ⟨H,Z,l,h,-,-⟩:= A.trace.stress
  exact ⟨A, opened_sky F hG h, fun _ _ _ _ _ _ _=> positions4 F hG⟩

-- strict consumer
omit hG in
theorem haveSlab (G : Gauge) (h : G.Simple) (b : ℝ) (hb : 0 < b) (p : Extraction.Order) :
    ∃ C : Family G, C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧
      Extraction.Wcmain C ∧ ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Spec.Final C (p.refine q) S) (L : Almanac F), Roll.{u} F h L := by
  obtain ⟨C,H,U,K,T,q,S,F,L,R⟩:= everyTrace.{u} G h b hb p
  exact ⟨C,H,U,K,T,q,S,F,L,Roll.ofFlight F h R⟩
end YM.GapsContact
