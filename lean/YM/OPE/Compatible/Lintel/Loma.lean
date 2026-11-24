import YM.OPE.Compatible.Lintel.Dais
/-! # Raw slots (no extra factorial costs). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff
variable {I J E:Type}{G:Gauge}{n m c f:Side} {r d:ℕ}{p q:Clip}{R T:PathData G} {u v s:ℝ}
namespace Script
open Page Virgin
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][Fintype I]
def Voice (p:Script I r)(F:E→L[ℝ] deck I c)(Y:E→ℝ):Prop:=∀ v: Fin r→E, library c p (F∘v) = iteratedFDeriv ℝ r Y 0 v
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] in
abbrev expose (p:Script I r):Script I r:= (r.factorial:ℝ) • p
omit [Fintype I] in
lemma soothe (p:Script I r)(F:E→L[ℝ] deck I c)(Y:E→ℝ)(h:Talent p F Y):Voice (expose p) F Y:=by intro v; rw [expose,libScale,h]
end
abbrev voteV (P:Patch)(K:KernelChoices)(R:PathData G)(p:Clip)(n:ℕ):= expose (Penna P K R p n)
abbrev inkV (R:PathData G)(p:Clip)(n:ℕ):= expose (polyV R p n)
abbrev leafV (R:PathData G)(r:ℕ):= expose (trailV R r)
section
variable (S:StepData c f)(hp:Odd S.ratio.count.val)
local notation "F" => forest S.ratio hp
abbrev dance (G:Gauge): vertP S.ratio hp G→L[ℝ] deck (Tile G S.ratio.count) c:= (paintV S.ratio hp G).toContinuousLinearMap
lemma vote_here (h:S.patch.Branches S.kernel G)(t:S.Choices)(p:Clip)(R:PathData G)(he:R.Bounds p s u v)(n:ℕ):Voice (voteV S.patch S.kernel R p n) (dance S hp G) (pane F t p R) := soothe _ _ _ (penne_at S hp h t p R he n).2
end
-- stability of canonical adds scales
lemma idemScale (p:Script I r)(k:ℝ)(h:p.Idem): (k • p).Idem:=by
    refine ⟨fun i hi=> h.1 i fun hh=>hi (by simp [hh]),fun i=>?_⟩; rw [show swing i (k • p)=k • swing i p from rfl,silt_scale,h.2]
lemma idemAdd (p q: Script I r)(h:p.Idem)(hx:q.Idem)(hp:Summable p)(hq:Summable q) : (p+q).Idem:=by
    refine ⟨fun i hi=>?_,fun i=>?_⟩
    · by_cases hb:p i=0; swap; exact h.1 i hb
      apply hx.1 i; intro hh; apply hi; simp [hb,hh]
    rw [show swing i (p+q)=swing i p+swing i q from rfl, silt_add (swing_sum p hp i) (swing_sum q hq i),h.2,hx.2]
lemma leafSongs (R:PathData G)(p:Clip)(n:Side)(r k:ℕ)(he:R.Bounds p s u v): (leafV R r).Idem ∧ (∃ c,soot k (leafV R r) c)∧ Voice (leafV R r) (spool G n).toContinuousLinearMap (swornY R (n:=n)):=by
    have hh:= inkY R p n r he; exact ⟨idemScale _ _ hh.1,⟨_,Sack.scale_line (hh.2.1 k).choose_spec _⟩, soothe _ _ _ hh.2.2⟩
lemma inkSongs (R:PathData G)(p:Clip)(n:Side)(r k:ℕ)(he:R.Bounds p s u v): (inkV R p r).Idem ∧ (∃ c,soot k (inkV R p r) c)∧ Voice (inkV R p r) (spool G n).toContinuousLinearMap (swornV p R (n:=n)):=by
    have hh:= inkX R p n r he; exact ⟨idemScale _ _ hh.1,⟨_,Sack.scale_line (hh.2.1 k).choose_spec _⟩, soothe _ _ _ hh.2.2⟩
end Script
end YM.OPE.Flume
