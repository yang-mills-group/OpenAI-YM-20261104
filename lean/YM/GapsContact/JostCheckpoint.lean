import YM.GapsContact.Series.Connect

/-!
# Physical endpoint: cp3 + all-real Jost functions and bounds there; exact all-order continuation consumer

Comparison uses HETEROGENEOUS finite fields in the actual physical labels. To claim an
all-order comparison requires that `Fan` be supplied *in the measured frame & trajectory*
of the construction. Not asserting that premise here: provide this conditional result PLUS
instantiate the unconditional continuation-side supplier on our common PhaseTrace choices,
running cp2 and cp3. All tempered boundary claims & leading spectral already achieved are
still included on these choices. This improves smrel on the way to the full goals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact
open Function Filter Set MeasureTheory Metric Boundary Analysis Tunnel Jost Ascent EveryPhase
open Pattern Work.C20 Spec Next.BOUNDARY Trace Trace.Pilot Trace.Terrace Climb
open scoped Topology BigOperators ContDiff InnerProductSpace Classical
open Craft hiding focus
universe u
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S} (L:Almanac F)
variable {n:ℕ}{D:∀ _:Survey F,∀ n, Blanket n}
variable (X:∀ i:Survey F, (Survey.reads L i).world.Aurora (D i))
variable {hG:G.Simple} {g:ℝ→ℝ}
variable {d:Fin n→ℕ}(v:∀ i:Fin n,ℝ→ S.Field (d i)) (hv:∀ i,Measured F (d i) (v i))
local notation "ℵ" => Craft.focus F
variable (P:Scheme n)(B:∀ j:Fin n, Blade F (d j) P.e)

structure JetCosts (F:Final C f S)(g:ℝ→ℝ)(n:ℕ)(Z:Index F→ Full n→ ℂ)(U:Set (Full n)) : Prop where
   degree : ∃ k:ℕ,∀ j:ℕ, Scoped (Craft.focus F) (fun i=> iteratedFDeriv ℂ j (Z i)) U (fun i=> (g i.1)⁻¹^k)

structure Hinge (n:ℕ) (F:Final C f S) (L:Almanac F) {D:∀ _:Survey F,∀ n, Blanket n}
     (X:∀ i:Survey F, (Survey.reads L i).world.Aurora (D i))(g:ℝ→ℝ){d:Fin n→ℕ}
     (v:∀ i:Fin n,ℝ→ S.Field (d i)) : Prop where
    first : JetCosts F g n (ship L X v) (tube n)
    through (P:Scheme n)(B:∀ j:Fin n, Blade F (d j) P.e) : JetCosts F g n (cargo L X v P B) (transit P)
    reads (i:Survey F) (r:ℝ)(hr:0<r)(P:Scheme n)(B:∀ j:Fin n,Blade F (d j) P.e)(φ:Joint n) (hx:HasCompactSupport ⇑φ)(hh: MapsTo (fun x=>glow x 0) (tsupport φ) P.zone):
       (Survey.reads L i).world.W n (ink v r) (TraceExtension.condense r⁻¹ φ)=∫ x,cargo L X v P B (r,i) (glow x 0) * φ x
    formal (U:ℕ→ Points n→ℂ) (hp: Fan (Craft.focus F) (metric F g) (eu S F v) U (ordered n)) :
       ∃ J:ℕ→ Full n→ ℂ, Alliance F L X g v U J

include hv in
lemma Hinge.actual (Z: Roll.{u} F hG L) (hg:Coupling G g) : Hinge n F L X g v:=by
   have hp := (walk F).eventually hg.positive
   have hu (k:ℕ) : ∀ᶠ i in Craft.focus F, 0 ≤ (g i.1)⁻¹^k:=hp.mono fun i hi=>pow_nonneg (inv_pos.mpr (show 0<g i.1 from hi)).le k
   obtain ⟨k,hk⟩:= ship_expense hg L X v hv Z
   refine ⟨⟨k, fun j=> hk.jet (hu k) (south n) (ship_motion L X v) j⟩,fun P B=> ?_,fun i r hr P B φ hφ he=> ?_,fun U hp=> propagate L X Z hg v hv U hp⟩
   · obtain ⟨k,hk⟩:= transit_estimate L X Z hg v hv P B; exact ⟨k,fun j=> hk.jet (hu k) (transit_open P) (bridge_hol L X v P B) j⟩
   apply (real_panel L i (X i) P B _ hr φ hφ he).2.trans
   apply integral_congr_ae; filter_upwards with x; by_cases h: φ x=0; simp [h]
   exact congr_arg (·*φ x) (latter L X v P B (r,i) hr (he (subset_tsupport _ h))).symm

-- strengthening of consumer conclusion over common family. Rigor on calibrated choices
-- DOES NOT assert general scheme reexpressions or the all-order real inputs.
structure Wing (F:Final C f S)(h:G.Simple)(L:Almanac F) : Prop extends Wind.{u} F h L where
    jetReaction (n:ℕ) {D:∀ _:Survey F,∀ n, Blanket n}
      (X:∀ i:Survey F, (Survey.reads L i).world.Aurora (D i))(g:ℝ→ℝ) (hg:Coupling G g)
      (d:Fin n→ℕ)(v:∀ i:Fin n,ℝ→ S.Field (d i))(hv:∀ i,Measured F (d i) (v i)): Hinge n F L X g v
variable {L} in
lemma Wing.ofWind (H:Wind.{u} F hG L):Wing.{u} F hG L:= ⟨H,fun _ _ X _ hg _ v hv=>Hinge.actual L X v hv H.toRoll hg⟩

lemma Wing.traceNest (X : Wing.{u} F hG L): ∃ (H : (Bel C.book).Hierarchy), ∃ Z l χ P P' κ d e,
    Bliss F l Z H ∧ Trace.Target.XScheme F hG H l P P' χ ∧ Trace.Target.FieldComparison F H Z P P' κ d e ∧
    (∀ i,Trace.Target.FieldComparison (focus X.complete i) H Z P P' κ d e) ∧
    ∀ D:∀ _:Survey F,∀ n, Blanket n, ∀ W:∀ i:Survey F, (Survey.reads L i).world.Aurora (D i),
     ∀ n:ℕ, ∀ v:Fin n→(Bel C.book).Field 4,Hinge n F L W (Trace.Sundial.glo P') (d:=fun _=>4) (fun i r=>P' r (v i)):=by
    obtain ⟨H,Z,l,χ,P,P',κ,d,e,a,b,c,g⟩:= X.commonFrame
    exact ⟨H,Z,l,χ,P,P',κ,d,e,a,b,c,g,fun D W n v=> X.jetReaction n W (Trace.Sundial.glo P') c.coupling _ _ (fun i=>X.calibration H Z P P' κ d e c (v i))⟩

theorem haveJost (G : Gauge) (h : G.Simple) (b : ℝ) (hb : 0 < b) (p : Extraction.Order) :
    ∃ C : Family G, C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧
      Extraction.Wcmain C ∧ ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Spec.Final C (p.refine q) S) (L : Almanac F), Wing.{u} F h L := by
  obtain ⟨C,H,U,K,T,q,S,F,L,R⟩:= haveTube.{u} G h b hb p
  exact ⟨C,H,U,K,T,q,S,F,L,Wing.ofWind R⟩
end YM.GapsContact
