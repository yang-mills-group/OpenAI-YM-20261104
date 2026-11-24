import YM.OPE.Compatible.Atrium.Palm
/-! # Patch tensor inventory -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody Next.Foundations Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K: KernelChoices} {k r:ℕ}
namespace Script
open Virgin Page
def stationCall (P:Patch)(K: KernelChoices)(G:Gauge)(r:ℕ): Script (Tile G P.L) r:= ∑ i:Axis,servo (theatre G P) (yodel G P K i) r
lemma callCost (P:Patch)(K:KernelChoices)(G:Gauge)(r m:ℕ):∃ c,soot m (stationCall P K G r) c:=by
   choose c H using fun i:Axis=> ser_s (theatre G P) (yodel G P K i) m r; exact ⟨_, Sack.finGather (B:=c) _ _ (fun i _=> H i) (fun i=> zero_le_one.trans (payer m _))⟩
variable (S) (hp: Odd S.ratio.count.val)
abbrev groundFee (t:S.Choices)(x:vertP S.ratio hp G):=noiseTaylor S (represent x.1) (fieldF _ x.2) t
lemma luff (t:S.Choices) (h:S.patch.Branches S.kernel G)(r:ℕ): ContDiffAt ℝ ω (groundFee S hp (G:=G) t) 0 ∧ Talent (stationCall S.patch S.kernel G r) (paintV S.ratio hp G).toContinuousLinearMap (groundFee S hp t):=by
    let V(a: Site c)(i:Axis):= yodel G S.patch S.kernel i ∘ (nick hp a); let X:= ∑ a: Site c,∑ i:Axis,V a i
    have hV(a i): ContDiffAt ℝ ω (V a i) 0:= ((show ContDiffAt ℝ ω (yodel G S.patch S.kernel i) ((nick hp a) 0) from by rw [map_zero]; exact thinks h i).comp (f:=nick hp a) _ (nick hp a).contDiff.contDiffAt)
    have ht(i):ContDiffAt ℝ ω (∑ a:Axis,V i a) 0:= by rw [show (∑ a:Axis,V i a)=(fun z=> ∑ a:Axis,V i a z) from funext (fun a=> sum_apply ..)]; exact ContDiffAt.sum (fun a _=> hV i a)
    have he: groundFee S hp t=ᶠ[𝓝 0] X:=by
       filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun j=>turnsAt hp h t i j] with x hx; unfold X groundFee noiseTaylor; simp only [Finset.sum_apply,Fintype.sum_prod_type]; rw [mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [mul_sum]; exact sum_congr rfl fun j _=> hx i j
    refine ⟨(show ContDiffAt ℝ ω X 0 from (show _ from ?_)).congr_of_eventuallyEq he,fun w=>?_⟩
    · rw [show X=(fun a=> ∑ i:Site c,(∑ j,V i j) a) from funext fun a=> sum_apply ..]; exact ContDiffAt.sum (fun i _=> ht i)
    rw [(he.iteratedFDeriv ℝ r).eq_of_nhds]; unfold X; rw [iteratedFDeriv_sum_apply (fun i _=> (ht i).of_le le_top), _root_.sum_apply]; unfold library stationCall; rw [mul_sum]; apply sum_congr rfl; intro i _; rw [reads_sum]; swap; · intro a _; exact sootS (ser_s _ _ 0 _).choose_spec
    rw [iteratedFDeriv_sum_apply (fun a _=> (hV _ _).of_le le_top),_root_.sum_apply,mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; let F:=yodel G S.patch S.kernel j; let Y:= lookS (theatre G S.patch) i; let P:= (paintV S.ratio hp G).toContinuousLinearMap; have ht:= thinks h j; have hy: ContDiffAt ℝ (r:WithTop ℕ∞) (F ∘ Y) 0:=((show ContDiffAt ℝ ω F (Y 0) from by rw [map_zero];exact ht).comp (f:=Y) _ Y.contDiff.contDiffAt|>.of_le le_top)
    erw [show V i j=(F ∘ Y) ∘ P from rfl, jets_linear P hy]; exact ser_sense _ F _ _ i (ht.of_le le_top)
end Script
end YM.OPE.Flume
