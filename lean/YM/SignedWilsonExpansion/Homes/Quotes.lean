import YM.SignedWilsonExpansion.Homes.ProbeA
import YM.TraceExtension.Prom.Zoom.Mast

/-! Harvested cap book of continuum projections. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.SignedWilsonExpansion.Homes
open Function Filter Set MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East
open scoped Topology BigOperators Classical ContDiff
variable {n:ℕ} {ι : Type*}
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}

-- aligned estimates *from* checked receipt, below the indicated ordered period
structure HouseT (Hs:S.Hierarchy) (H:(Bel C.book).Hierarchy) (r:ℝ)(D:ℕ)(P:Panel S) : Prop where
   ticket (d:Fin (D+1)) : StraightAt Hs.spin H.spin P d ∧ P d ((Bel C.book).unit d)= S.unit d
   tests (n:ℕ)(hn:n≤ D)(d:Caps n)(v:MaxwellSlots C d)(hv:∀ i,d i ≤ D)(t:Test n) (ht:tsupport t ⊆ Scaling.window (sizeHint D) n) (M:ℝ)(hm: 0<M) (hy: ∀ x, ‖t x‖ ≤ M):
        ‖t.applyTo (tested r P (hang d v)) - t.applyTo (WickGoal v)‖ ≤ costHint D * Next.UVStress.Station.charge (hang d v) * M

theorem fan (Hs:S.Hierarchy) (Hf:f.Ordered C S) (H:(Bel C.book).Hierarchy) (P:C.Makes)
   {k:ℕ} (V:Vane C k) (hz:V.checked f H k) (𝓛:Ultrafilter (ℕ×ℕ))(hℓ:(𝓛:Filter _) ≤ f.fuse) :
   ∃ Y : Lifts C k,Tendsto V.wheel.atCut (𝓛:Filter _) (𝓝 Y) ∧ ∃ U:Panel S,
   (∀ d:Fin (k+1),∀ x,U d x=S.project d (Y d x)) ∧ HouseT Hs H V.wheel.r k U := by
   have hq(d:Fin (k+1)): ∀ᶠ j:ℕ×ℕ in f.fuse, V.wheel.atCut j d ((Bel C.book).unit d)= C.book.scalar d:= by
      filter_upwards [large_mesh f (V.k+1)] with j hj
      change Next.Rank.East.ladd C _ _ _ _ _ _ (Further.CorrectedLift.ladder C d ((Bel C.book).unit d))=_
      rw [Further.CorrectedLift.ladder_unit]; exact Next.Rank.East.pure_start P (hz.early d) (Nat.le_of_lt hj) _ _ ((hz.rate _ _ hj).1 d).1
   obtain ⟨U,Y,hY,hQ,hu,hD,hθ⟩:= harvestedSky Hs Hf H.spin V.wheel.toStation hz.fares 𝓛 hℓ hq
   exact ⟨Y,hY,U,hQ,fun d=> ⟨hu d (Nat.le_of_lt_succ d.isLt),hD d (Nat.le_of_lt_succ d.isLt)⟩, fun n hn d v hv=> hθ n hn (hang d v) hv⟩

abbrev Coast {n:ℕ}{d:Caps n} (P:Panel S) (r:ℝ) (v:MaxwellSlots C d): Points n→ℂ:=
   fun x=> S.classMoment S d (r • x) (fun i=>P _ (v i))

lemma lateX {L:Filter ι} {r:ι→ℝ} {D:ι→ℕ}(hd:Tendsto D L atTop)
    {Hs:S.Hierarchy}{H:(Bel C.book).Hierarchy}{P:ι→Panel S} (h: ∀ᶠ i in L, HouseT Hs H (r i) (D i) (P i))
    (d:Caps n)(v:MaxwellSlots C d)(t:Test n):
    Tendsto (fun i=> t.applyTo (Coast (P i) (r i) v)) L (𝓝 (t.applyTo (WickGoal v))) := by
   obtain ⟨M,hM,hΩ⟩ := Order.testSup t; let x:=M+1
   have hx:0<x:=by dsimp [x]; linarith
   let z:= Next.UVStress.Station.charge (hang d v)
   have hh : Tendsto (fun i => costHint (D i) * z * x) L (𝓝 0) := by simpa only [Function.comp_apply, zero_mul] using ((cost_clears.comp hd).mul_const z).mul_const x
   apply Metric.tendsto_nhds.mpr; intro ε ep
   filter_upwards [h,hd.eventually_ge_atTop n,eventually_all.mpr (fun j=>hd.eventually_ge_atTop (d j)),
     hd.eventually (size_ascends.eventually (Work.A05.compact_fits t.hasCompactSupport t.tsupport_subset)),hh.eventually (gt_mem_nhds ep)] with i hi hp H' ha hz
   rw [dist_eq_norm]; exact (hi.tests n hp d v H' t ha x hx fun _=> (hΩ _).trans (lt_add_one _).le).trans_lt hz

end YM.SignedWilsonExpansion.Homes
