import YM.OPE.Compatible.Basin.Vogue
/-! # Talent reached. Lowering syntax ... -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type*} {G:Gauge}{n m c f:Side}{S:StepData c f} {p q:Clip} {R:PathData G}{U V a s:ℝ} {k r:ℕ}
namespace Script
open Virgin
abbrev drill (w:Script (Shade G) r)(f:Bid.Dir G n→ℝ):Prop:=w.Idem ∧ (∀ k,∃ C,soot k w C)∧ Talent w (spool G n).toContinuousLinearMap f
lemma inkX (R:PathData G)(p:Clip)(n:Side)(r:ℕ)(h:R.Bounds p s U V): drill (polyV R p r) (swornV p R (n:=n)):=by
    have he m:∃ c,Earn r m (oathV R p) (oathX R p r) c:=by obtain ⟨C,H⟩:= oath_earn G p s U h.width r m;exact ⟨C,H R V h⟩
    obtain ⟨b,hB⟩:=he 0; have hp:=Prom.yield hB; refine ⟨hp.fixed,fun k=>⟨_,(Prom.yield (he k).choose_spec).stone⟩,talent _ _ _ (chartK R p n h).1 (sootS hp.stone) hp.fixed (fun v=>?_)⟩
    change _=narrate n _ (spool G n v); rw [← hp.Fire]; unfold swornV; congr 1; funext i; rw [← map_smul (spool G n), primora,oath_main _ h]; rfl
lemma inkY (R:PathData G)(p:Clip)(n:Side)(r:ℕ)(h:R.Bounds p s U V): drill (trailV R r) (swornY R (n:=n)):=by
    have he m:∃ c,Earn r m (oathL R) (oathY R r) c:=by obtain ⟨C,H⟩:=oathLoop G s h.width r m; exact ⟨_, H p R U V h⟩
    obtain ⟨b,hB⟩:= he 0; have hp :=Prom.yield hB; refine ⟨hp.fixed,fun k=>⟨_,(Prom.yield (he k).choose_spec).stone⟩,talent _ _ _ (tubesY R p n h).1 (sootS hp.stone) hp.fixed (fun v=>?_)⟩; change _=narrate n _ (spool G n v);rw [←hp.Fire]; unfold swornY; congr 1; funext i; rw [← map_smul (spool G n), primora,oath_trail _ h];rfl
-- sums across crew. 
lemma libScale (p:Script I r)(u:Fin r→deck I c)(a:ℝ): library c (a • p) u=a*library c p u:=by unfold library; rw [mul_sum];exact Finset.sum_congr rfl fun _ _=> score_scaled ..
lemma libAdd [Fintype I](p q:Script I r)(h:Summable p)(he:Summable q)(v:Fin r→deck I c): library c (p+q) v= library c p v+library c q v:=by unfold library; rw [← Finset.sum_add_distrib]; refine sum_congr rfl fun i _=>?_; unfold scribe; simp_rw [Pi.add_apply,add_mul]; exact (instruments p h _ _).summable.tsum_add (instruments q he ..).summable
section
variable [Fintype I]{X Y:Type*}[NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y][NormedSpace ℝ Y]
omit [Fintype I] in
lemma talentMove (A:X→L[ℝ] deck I c)(p:Script I r){q:X→ℝ}(h:Talent p A q)(hp:ContDiffAt ℝ r q 0)(D:Y→L[ℝ] X): Talent p (A ∘L D) (q∘D):=by intro v;rw [jets_linear D hp];exact h _
lemma issueTal {w z:Script I r}{p q:X→ℝ}(L:X→L[ℝ] deck I n)(h:Talent w L p)(hs:Summable w)(he:Talent z L q)(hk: Summable z)(hf:ContDiffAt ℝ (r:WithTop ℕ∞) p 0)(hv:ContDiffAt ℝ (r:WithTop ℕ∞) q 0):Talent (w+z) L (p+q):=by intro v; rw [libAdd _ _ hs hk, iteratedFDeriv_add_apply hf hv,_root_.add_apply,h v, he v,mul_add]
omit [Fintype I] in
lemma raisesTal {w:Script I r}{p:X→ℝ}(L:X→L[ℝ] deck I n)(h:Talent w L p)(hf:ContDiffAt ℝ (r:WithTop ℕ∞) p 0)(x:ℝ): Talent (x • w) L (x • p):=by intro v; rw [libScale, iteratedFDeriv_const_smul_apply hf,_root_.smul_apply,smul_eq_mul,h];ring
end
def draftY (p:Clip)(R:PathData G)(b:ℝ): Script (Shade G) 2:= b • polyV R p 2 + trailV R 2
lemma draftTal (R:PathData G)(p:Clip)(n:Side)(b:ℝ)(h:R.Bounds p s U V): Talent (draftY p R b) (spool G n).toContinuousLinearMap (draft b R p):=by
     have hx:= inkX R p n 2 h; have hp:=inkY R p n 2 h
     have he:= chartK R p n h; have hi:=tubesY R p n h; let L:=(spool G n).toContinuousLinearMap; apply issueTal (p:=b • swornX R p) (q:=swornY R) L _ _ hp.2.2 (sootS (hp.2.1 0).choose_spec) ((hi.2.const_smul b).of_le le_top) (hi.1.of_le le_top)
     · refine raisesTal L (fun v=> by rw [← he.2]; exact hx.2.2 v) (hi.2.of_le le_top) b
     exact sootS (Sack.scale_line (hx.2.1 0).choose_spec b)
end Script
end YM.OPE.Flume
