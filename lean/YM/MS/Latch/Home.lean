import YM.MS.Latch.Gully
/-!
# Rank-local processing of Past for leases. Literal data at any timespan. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Belt
open scoped Topology ContDiff Interval
variable {I E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {G:Gauge}{S:Scale I} {J:Belt I}{b c:Bool}{t h:ℤ}{n r m:ℕ}{A B C:I→ℝ}{F H X : I→Law G}
-- drafts travels
abbrev Lens (b:Bool)(S:Scale I)(F:I→Law G)(A:I→ℝ)(r:ℕ): Prop:= ∀ (E:Type)[ NormedAddCommGroup E ][ NormedSpace ℝ E ], ∀ w: Wire (BH G) E QP, List.length w=r → Course b w → Cape S F A w
abbrev Here (b:Bool)(c:Bool) (J:Belt I)(F:Moments I (Law G))(A:J.time→ℝ):= Lease b c J.price (plug F) A
abbrev coinF (b:Bool)(Qz:Belt I)(F: Moments I (Law G))(A:Qz.time→ℝ)(r:ℕ):= Lens b Qz.price (plug F) A r
lemma pinch (h:Lease b c S F A)(hv:fig c r): Lens b S F A r:= fun E _ _ w hr hW=> h E w hW (hr ▸ hv)
lemma poses (h:∀ r,fig c r→Lens b S F A r): Lease b c S F A := fun E _ _ w hW hu=> h _ hu E w rfl hW
lemma reaches (h:Lens b S F A r)(he:∀ i (w:Legs (Lane4 G)), Course b w→w.length=r→ H i w = F i w): Lens b S H A r:= by intro E _ _ w hp hx; rw [Cape, show Plane.Chart H w= Plane.Chart F w from funext (fun i=> funext (fun x=> he i _ (sail_course x hx) (( sail_len .. ).trans hp) )) ]; exact h E w hp hx
lemma Lens.plus (h: Lens b S F A r)(he:Lens b S H A r): Lens b S (F+H) A r:= fun E _ _ w hv ht=> Cape.plus (h E w hv ht) (he E w hv ht)
lemma Lens.up (h:Lens b S F A r)(hv:∀ i,A i≤B i): Lens b S F B r:= fun E _ _ w hP hx=> Cape.up (h E w hP hx) hv
lemma stepOver (h:Lens b S F A r)(hv:nn A) : Lease b false S (fun i=> Book.mask r (F i)) A:= by
   intro E _ _ w hw _; by_cases hx:List.length w=r; · exact ( reaches h (H:=fun i=>Book.mask r (F i)) (fun i w hW hr=> Book.enough _ (by omega))) E w hx hw
   unfold Cape; rw [show Chart (fun i=> Book.mask r (F i)) w=(fun i:I=> fun x:E=> (0:ℂ)) from funext fun i=> funext fun q=> Book.strange (sail w q) (by rw [sail_len]; omega)]; exact Costs.zero fun i _ _=> pos_nn A hv S i
lemma cycle_mask (K:Edge G)(μ:Measure QP){F:Law G}{w:Legs (Lane4 G)} (hv:w.length=r): cycle K μ F w=cycle K μ ( Book.mask (r+2:ℕ) F ) w := by unfold cycle; simp_rw [at_trc, show ∀ i j:Lane4 G, Book.mask (r+2:ℕ) F (i::j::w)=F (i::j::w) from fun _ _=> Book.enough _ (by rw [List.length_cons,List.length_cons,hv])];  -- β
lemma penny {μ:I→Measure QP}{d:ℕ}{K:I→Edge G} (h: Lens b S F A (r+2))(ht:nn A)(hp: Sheet S B K)(he:nn B)(hu: glob S μ d)(h0: Mint S μ d): Lens b S (fun i=>cycle (K i) (μ i) (F i)) (B*A) r:= reaches (pinch ( planC ((stepOver h ht)|>.highp) hp hu h0 ht he) (fun b=> Bool.noConfusion b)) (fun i _ _ h=> cycle_mask (K i) (μ i) h)
section
variable {A Z: J.time→ℝ}{F H:Moments I (Law G)}{B: J.time→ Law G}
-- only pointwise moment equality, coast term. Valid for any Rank.C.V.C.Stencils
abbrev Dash (b:Bool)(J:Belt I)(F H:Moments I (Law G))(B:J.time→ Law G): Prop:= ∀ t:J.time,∀ u:Legs (Lane4 G),Course b u→ F t.1 t.2 u=B t u+ ∫ s,H t.1 s u ∂Mu t
def Stroll (b:Bool)(F: Moments I (Law G)): Prop:= ∀ i u,Course b u→Continuous (fun t=> F i t u)
-- feeds via per-r ghosts.
lemma marching (hp:Walk J)(hx: nn A)(hf: Stroll b H)(hs:Dash b J F H B)(hb: Lease b c J.price B A)(hv: ∃ r:ℕ,∀ i,Upper b r (plug (J:=J.slot) F i)) (hh:∀ r:ℕ, fig c r→ coinF b J F A ( r+2 ) →∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E],∀ w: Wire (BH G) E QP,List.length w=r→Course b w→ ∃ P:J.time→ℝ,∃ ε:ℝ,0<ε∧ Bound J.price (Chart (plug H) w) P ∧ Slide J ε P (Qbud w J.price A)): Here b c J F A := by
   obtain ⟨M,hv⟩:= hv; apply poses; suffices he:∀ k:ℕ,∀ r, M≤ k+r →fig c r→ coinF b J F A r from fun r=> he M r (by omega); intro k; induction k using Nat.strong_induction_on with
   | h k ih=>
    intro r he hC; by_cases ht:M<r; · refine reaches (pinch (Lease.zero (b:=b) (S:=J.price) hx) hC) (fun i v hw hz=>?_); exact hv i v (by exact hw) (by omega)
    intro E _ _ w hW hK; refine factorS (b:=b) (fun k=> k=r) J.price (plug F) A (fun E _ _ _ w hW hK=> ?_) w hW hK; -- case equality M=r,k=0 recurrence ih not possible h'+2 cap; handle explicitly
    have hg : coinF b J F A (r+2):= by
       by_cases hM:M< r+2; · refine reaches (pinch ( Lease.zero (G:=G) (b:=b) (c:=c) hx ) (fun _=> by omega)) ( fun i v hh hl=> ?_ ); exact hv i v hh (by omega)
       exact ih (k-1) (by omega) (r+2) (by omega) (fun _=> by omega)
    obtain ⟨P,ε,hε,h0,hL⟩:= hh r hC hg E w hW hK; let f i t: E→ℂ:= fieldVal ( H i t ) w; unfold Cape; rw [show Plane.Chart (plug F) w=(fun i p=>(Chart B w) i p+ past J f i p ) from funext fun i=> funext fun p=> hs i _ ( sail_course p hK ) ] -- f ext simp
    exact Costs.add ( hb E w hK (hW ▸ hC)) (pastCost (f:=f) h0 hp hL hε (fun p i=> ( hf p.1 _ ( sail_course i hK ) ).aestronglyMeasurable))
end
end YM.MS.Latch.Job
