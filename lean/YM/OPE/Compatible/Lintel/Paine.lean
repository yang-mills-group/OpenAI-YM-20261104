import YM.OPE.Compatible.Lintel.Tomato
/-! # V-resonance identification actual K in receipt & further virtual propagations. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
variable {B:Sponsor G}{H:Seasons B}
-- purchased
lemma elevation (P:Flight i j)(h:Mag i j)(M:Alps B H i b)(N:Alps B H j b')(he:M.gear=P.wing)(hx:N.gear=P.land) (hv:Pilgrim G P B.K M.clip N.clip M.live N.live α V)(hq:LocalRatio V) (C:Medal P.patch G B.K i):
    TEX (⟨i,h.1,C,M.gear⟩:Boxes G P.patch B.K) M.clip N.clip M.live N.live α V:=by
     refine prime_weave hq ?_ M.pays N.pays
     obtain ⟨m,hm,Z,Y,W,hY,L⟩:= hv.cohabit; refine ⟨m,hm,Z,Y,W,hY,?_⟩; intro x
     let S : StepData (m x) (m x * P.L):= P.visit B.K rfl; let X:= P.duo B.K.penalty; let T:= installed S.ratio X.A0; obtain ⟨hL,g,hg,hk,hθ⟩:=L x; refine ⟨M.sky,T,g,?_,hk,hθ⟩; change Bid.Larger (G:=G) S at hL; have hP:=M.active; have hS:=N.active; let F:=forest S.ratio P.odd; have hz :Defined B.K.penalty (B.l i) P.wing M.sky:= he ▸ hP.2.1; have hf:Defined B.K.penalty (B.l j) P.land N.sky:= hx ▸ hS.2.1; have hh : Towers.Diagonal S M.sky N.sky X := Next.Free.diagonal B.K _ _ (B.h.net _) (B.h.net _) P h.2.1 M.sky N.sky hz hf rfl
     have hB:= hP.2.2.2.1 (m x*P.L); have ha:= hP.2.2.2.2 (m x*P.L); have ht1:= Virgin.receives (g:=g) hg (B.X.eta_pos _) hL hh hB (hS.2.2.2.1 (m x)) M.pays M.fills ha; have HT:= Work.F03.answer G _ _ S hL F M.sky _ M.live _ _ _ _ _ hB M.pays M.fills ha (Work.F02.answer G _ _ _ _ _ M.pays); refine ⟨⟨hL.1,?_,?_⟩,hg,ht1,HT.2⟩
     · have hf : Precision.K (M.sky.metric.acts (m x*P.L))=Precision.K ((pink B.K.penalty P.wing).acts (m x*P.L)):= by unfold Precision.K; rw [hz.metric,Matrix.mul_assoc,Matrix.mul_assoc]; rw [(obligations B.K.penalty (B.l i) B.K.penalty_pos (B.h.net _) h.1 P.wing (m x*P.L)).2.2.1]
       change treeMatrix G S F M.sky.metric=treeMatrix G S F (pink B.K.penalty M.gear); rw [he]; apply congr_arg (fun X : Matrix _ _ ℝ=> (tensor G X).submatrix (plant F) (plant F)); exact congr_arg (fun x: Matrix _ _ ℝ=> x+ _ ) hf
     change installed S.ratio (C.highCross M.gear)=_; rw [he]; exact C.trueMean S P.odd P.wing hL P.legal (Flight.tangent P B.K h.2.1 (c:=m x) (f:=m x* P.L) rfl).1
end YM.OPE.Votive
