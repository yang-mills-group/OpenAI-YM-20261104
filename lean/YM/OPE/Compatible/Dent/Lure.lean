import YM.OPE.Compatible.Dent.Nimbus
/-!
# Real Path mass Reps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset WilsonStartup
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m d M: ℕ} {W a r t σ E Λ μ x κ w C s ε D: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
def acid (R:Rep G f):Deckery R AnalyticBridge.VerifiedReset.Low:=⟨Low.length R.path, fun x i=> Low.home R.path i R.p x,fun _ _=> Low.small_home .., fun x i=> Low.live R.path R.clip i R.p x, fun x i U=>Low.mark R.path R.clip i*Low.plain R.path i x U⟩
set_option linter.unusedVariables true in
lemma acidic (h:Decent R.clip R.p)(hh:R.Lawful σ C Λ E w)(hp: AnalyticBridge.VerifiedReset.Geo.Width R.p R.clip σ):
 ∃ w,Decked R (acid R) (3*σ/4) ((2*R.p.threshold)*AnalyticBridge.VerifiedReset.Geo.lowerSize R.clip C) AnalyticBridge.VerifiedReset.Geo.lowCount w:=by
    let d i:= |Low.mark R.path R.clip i| *(2*R.p.threshold * Real.exp (↑((acid R).len i)/R.clip.relaxation))
    have he:=AnalyticBridge.VerifiedReset.Geo.kept_debit G R.p R.path hp hh.paths -- check implicit G
    have hb:= budget_scale (mul_nonneg zero_le_two R.p.threshold_pos.le) he
    refine ⟨d, ⟨?_,fun x i V=> Low.shapeBound ..,fun x i U V H=>?_,fun x i U V h' _=> Low.live_local R.path R.clip i h x U V h',fun x i=> Low.live_gauge _ _ _ _,fun x i=>Low.live_meas _ _ _ _ _,fun x i U hV=> Low.live_plain R.path R.clip i h x hV,fun x i=>?_⟩⟩
    · convert! hb using 1; funext i; unfold d acid; dsimp only; ring
    · exact congr_arg (Low.mark R.path R.clip i*·) ((Low.plain_local R.path i R.p h.radius x) U V H)
    exact_mod_cast AnalyticBridge.VerifiedReset.Geo.low_geometry R.p R.path i x
open Extra.Iteration.Derivs

def emberY (R:Rep G f) (X:ℕ→ Atom G d):Deckery R ℕ:=⟨fun i=> (X i).length, fun x i => (X i).footprint x,fun x i=>by unfold Atom.footprint; exact mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩,fun x i U=>(X i).placed R.p U x, fun x i U=> (X i).unmasked U x⟩
lemma soundsE (X:ℕ→ Atom G d)(hp:∀ i,(X i).Invariant) (hh:SumBudget (fun i=> (X i).budget σ) C) :
 ∃ w, Decked R (emberY R X) σ (2^d*C) (1+d*2) w:=by
    let v i:=(X i).magnitude *2^d
    have he:= budget_scale (x:=2^d) (f:=fun i=> (X i).budget σ) (by positivity) hh
    refine ⟨v, ?_,fun _ i _=> (X i).placed_bound R.p _ _,?_,?_,?_,fun _ i=>masked_measurable _ _ _ ((X i).unmasked_cont ..|>.measurable),fun x i U h=>masked_eq R.p.threshold _ (fun u=>(X i).unmasked u x) U h,?_⟩
    · convert! he using 1; funext i; unfold v Atom.budget emberY; dsimp only; ring
    · intro x i; exact (atom_local (X i) x)
    · intro x i; let k:= X i; change UsesFinal _ (k.footprint x) (masked _ _ (fun U=> k.unmasked U x)); intro U V hx h; unfold masked Set.indicator; dsimp only; have he: Healthy R.p.threshold (k.footprint x) U ↔ Healthy R.p.threshold (k.footprint x) V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,h,Finset.disjoint_iff_inter_eq_empty]
      split
      next h=> rw [if_pos (show V ∈ {U|Healthy R.p.threshold ((X i).footprint x) U} from he.1 h)]; exact (atom_local k x U V hx)
      next h=> exact (if_neg (show V ∉ {U|Healthy R.p.threshold ((X i).footprint x) U} from mt he.2 h)).symm
    · intro x i t U; unfold emberY Atom.placed masked Set.indicator; dsimp only; split
      next h=>
        have he : U ∈ {U|Healthy R.p.threshold ((X i).footprint x) U}:=by simpa only [Set.mem_setOf_eq,Healthy,RG.gauge_flags] using h
        rw [if_pos he];exact ((canonical_regular _ x R.p (hp i)).symmetry t U)
      next h=> rw [if_neg (by intro hv; apply h; simpa only [Set.mem_setOf_eq,Healthy,RG.gauge_flags] using hv)]
    intro x i; have hx:= Next.Scheduling.Wages.traversed (X i) x R.p.B R.p.B_pos
    apply le_trans (show (R.p.B:ℝ)*(coverNumber R.p.B ((X i).footprint x)) ≤ ((R.p.B + (d*(2*R.p.B)+(X i).length):ℕ):ℝ) from by exact_mod_cast hx); push_cast; unfold emberY; dsimp only; linarith
end YM.PhysicalNext.Repeat.Aroma
