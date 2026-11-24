import YM.GapsContact.DuskCheckpoint
import YM.GapsContact.Power.Grade

/-! Emit cp5 + market authority on this same wing; precise supplier -/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact
open Function Filter Lattice RG MeasureTheory Spec Trace Trace.Target Trace.Pilot Trace.Terrace Dusk MergeProof Org Next.Extract
open Power Ascent Frontier6
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
universe u
structure Stones (F : Final C f S)(h:G.Simple)(L:EveryPhase.Almanac F) : Prop extends Wing.{u} F h L where
    interest (d:ℕ)(ε:ℝ): 0<ε →∃ R B:ℝ,∀ e≤d, Market F e ε R B
    meso : Grille C f S
variable {F:Final C f S}{h:G.Simple}{L:EveryPhase.Almanac F} {d:ℕ}
lemma Stones.earth (T:Stones.{u} F h L) {v:ℝ → S.Field d} (he:Measured F d v) {e:ℕ}(hg:e≤d):Measured F e (fun r=>weight F e (projectBelow F hg (v r))) := by
   obtain ⟨R,B,hX⟩:= T.interest d 1 one_pos; obtain ⟨c,hc,hL⟩:=he; have hr:= (hX d le_rfl).road; have hp:0<B:= zero_lt_one.trans_le (hX d le_rfl).budget
   refine ⟨B*(B*c),mul_pos hp (mul_pos hp hc),?_⟩
   have hk : ∀ᶠ r in trail,0<r:= self_mem_nhdsWithin; filter_upwards [hL,hk,(ge_mem_nhds hr).filter_mono nhdsWithin_le_nhds] with r hz hx hr
   exact ((hX e hg).uniform_top r ⟨hx,hr⟩ _).trans (mul_le_mul_of_nonneg_left (((hX d le_rfl).tier e hg r ⟨hx,hr⟩ _).trans (mul_le_mul_of_nonneg_left hz hp.le)) hp.le)

theorem haveMarket (G:Gauge)(h:G.Simple)(b:ℝ)(hb:0<b)(f:Extraction.Order) : ∃ C:Family G,
    C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧
    ∃ (g:Extraction.Order) (S:Table C.book) (F:Final C (f.refine g) S) (L:EveryPhase.Almanac F), Stones.{u} F h L:=by
  obtain ⟨C,hC,hM,hL,hB,g,S,F,L,W,hR⟩:= haveGrill.{u} G h b hb f
  obtain ⟨H,Z,l,χ,P,P',κ,d,e,hχ,-⟩:= W.commonFrame
  exact ⟨C,hC,hM,hL,hB,g,S,F,L,W,marketplace F h hχ,hR⟩
end YM.GapsContact
