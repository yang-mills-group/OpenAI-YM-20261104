import YM.GapsContact.Tube.Sidecar
/-!
# Actual consumer: smrel tempered bounds and the full interior bound, using any normalized labels

Power bonds PLUS Trace position normalization through its cap-four scheme. Gives actual
all real relative poly-log temperance in that frame. No new premise (and real, threshold free
of phase and choice of supplier). A stronger interface goes by Gram bound which is scheme-independent.
Does NOT assert asymptotic comparison yet (except for exact TRACE agreement as in EveryTrace);
perturbative normalization remainders for full `kcert` equivalent scheme not inputs or claims here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact
open Function Set Filter Boundary Analysis Distribution MeasureTheory Trace Trace.Pilot TraceExtension
open Ascent Ascent.Survey EveryPhase Next.BOUNDARY Spec Probe Tunnel Climb Trace.Target
open scoped Topology BigOperators Classical
universe u
variable {G:Gauge}{C:Family G} {S:Table C.book} {f:Extraction.Order}
variable {F:Final C f S}{hG:G.Simple}{L:Almanac F}

-- Pole formula along ALL `fields n` (time axis last, Euclidean slope cost proof;
-- this definition is stronger than the fixed-slope boundary convention).
structure WindCard (L: Almanac F)(i:Survey F)(D:∀ n, Blanket n)(X:(Survey.reads L i).world.Aurora D) : Prop where
   ambient : Bid.cones (Survey.reads L i).world ∧ X.FullBody (Survey.reads L i).waves
   allSlope (n:ℕ)(v:Fin n→ S.Union)(r:ℝ)(hr:0<r)(φ:Joint n) : AnalyticOnNhd ℂ (weather X v r) (tube n) ∧
     (∀ y ∈ fields n, Integrable (fun x=> weather X v r (glow x y)* φ x)) ∧
     Tendsto (fun y=> ∫ x,weather X v r (glow x y)* φ x) (𝓝[fields n] 0)
       (𝓝 ((Survey.reads L i).world.W n v (condense r⁻¹ φ)))
   relative (n:ℕ)(v:Fin (n+1)→ S.Union)(r:ℝ)(hr:0<r)(φ:Joint n) (x: Probe E4) (hx:(∫ z,x z)=1) : Tendsto
     (fun y=> ∫ z,aurora_sides L i X v r y z * φ z) (𝓝[shelter n] 0) (𝓝 (readingsTest L i x r v φ))
lemma WindCard.actual (L: Almanac F)(i:Survey F)(D:∀ n, Blanket n)(X:(Survey.reads L i).world.Aurora D): WindCard L i D X :=by
  obtain ⟨h,Y⟩:= observe L i X
  refine ⟨⟨h,Y⟩, fun n v r hr g => ⟨hollow X Y v r hr, fun _ hy=> weather_int X Y v hr g hy,cascade _ v X h Y g hr⟩, fun n v r hr g a h => ?_⟩
  rw [reading_eq L i hr]; exact owned_limit L i X hr g a h v

structure Wind (F:Final C f S)(h:G.Simple)(L: Almanac F) : Prop extends Roll.{u} F h L where
   body : ∃ D: ∀ n, Blanket n, ∀ i:Survey F, ∃ X:(Survey.reads L i).world.Aurora D, WindCard L i D X
   words (n:ℕ)(d:Fin n→ℕ)(v: ∀ i: Fin n, ℝ→ S.Field (d i)) (hv:∀ i,Measured F (d i) (v i)):
    ∃ A:ℝ,0≤A ∧ ∃ m:ℕ,∀ᶠ r in trail, Temperate L (fun r j=> S.pin _ (v j r)) m A r
lemma Wind.ofRoll (H:Roll.{u} F hG L):Wind.{u} F hG L:=by
  refine ⟨H,⟨fun n:ℕ=> Classical.choice (Integrated.reconstructionArcs.cK n),fun i=>?_⟩,fun n _ v hv=> Temperate.core H v hv⟩
  exact ⟨Classical.choice (Next.BOUNDARY.visible ..), WindCard.actual ..⟩
-- no ifs (Run with the common data in everyTrace)
lemma Wind.traceWords (H:Wind.{u} F hG L):∃ (Z : (Climb.Bel C.book).Hierarchy), ∃ U l χ P P' κ d e,
    Bliss F l U Z ∧ XScheme F hG Z l P P' χ ∧ FieldComparison F Z U P P' κ d e ∧
    (∀ i,FieldComparison (focus H.complete i) Z U P P' κ d e) ∧
    ∀ (n:ℕ) (v:Fin n→(Bel C.book).Field 4), ∃ A:ℝ,0≤A ∧ ∃ m:ℕ,∀ᶠ r in trail,Temperate L (fun r j=>S.pin 4 (P' r (v j))) m A r:=by
  obtain ⟨Z,U,l,χ,P,P',κ,d,e,a,b,c,g⟩:= H.commonFrame; exact ⟨Z,U,l,χ,P,P',κ,d,e,a,b,c,g,fun n v=> H.words n _ (fun i r=> P' r (v i)) (fun i=> H.calibration Z U P P' κ d e c (v i))⟩

theorem haveTube (G : Gauge) (h : G.Simple) (b : ℝ) (hb : 0 < b) (p : Extraction.Order) :
    ∃ C : Family G, C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧
      Extraction.Wcmain C ∧ ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Spec.Final C (p.refine q) S) (L : Almanac F), Wind.{u} F h L := by
  obtain ⟨C,H,U,K,T,q,S,F,L,R⟩:= haveSlab.{u} G h b hb p
  exact ⟨C,H,U,K,T,q,S,F,L,Wind.ofRoll R⟩
end YM.GapsContact
