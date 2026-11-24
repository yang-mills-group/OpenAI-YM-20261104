import YM.OPE.Compatible.Glim.Rex
/-! # Formal Laplace div formula. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
-- M.Rcm arithmetic
lemma meltJ (p q:E→ℝ)(hp:ContDiffAt ℝ ω p 0)(hq: ContDiffAt ℝ ω q 0): Pawn.mold (p*q) 0= Pawn.mold p 0 * Pawn.mold q 0:=by
     funext x; apply (((Pawn.calm ((hp.mul hq).of_le le_top)).stale x)).equality (((Pawn.calm (hp.of_le le_top)).stale x).pile ((Pawn.calm (hq.of_le le_top)).stale x)) -- f invalid
lemma meldAdd (p q:E→ℝ)(hp:ContDiffAt ℝ ω p 0)(hq:ContDiffAt ℝ ω q 0): Pawn.mold (p+q) 0= Pawn.mold p 0 + Pawn.mold q 0:=by
     funext x; exact ((Pawn.calm ((hp.add hq).of_le le_top)).stale x).equality (((Pawn.calm (hp.of_le le_top)).stale x).sum ((Pawn.calm (hq.of_le le_top)).stale x)) -- uses variants defeq
omit [FiniteDimensional ℝ E] in lemma meltSame (p q:E→ℝ)(hp:p=ᶠ[𝓝 0] q)(j:ℕ): Pawn.mold p j=Pawn.mold q j:=by
     funext x; have hx(i:ℕ): jet p i x=jet q i x:= by unfold jet; rw [(hp.iteratedFDeriv ℝ i).eq_of_nhds];
     exact eta _ _ (hx _) (hx _) (hx _)
lemma melts (p:I→E→ℝ)(s:Finset I)(h:∀ i∈s,ContDiffAt ℝ ω (p i) 0): Pawn.mold (∑ i∈s,p i) 0=∑ i∈s,Pawn.mold (p i) 0:= by induction s using Finset.induction_on with
     | empty=> simp only [Finset.sum_empty]; funext x; exact ((Pawn.calm (contDiffAt_const (𝕜:=ℝ) (c:=(0:ℝ)) (x:=(0:E)))).stale x).equality (Reads.constants 0)
     | insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,meldAdd _ _ (h i (mem_insert_self ..)) (show ContDiffAt ℝ ω (∑ i ∈ s,p i) 0 from ?_),ih (fun j hj=>h j (mem_insert_of_mem hj))]; rw [show (∑ i ∈ s,p i)=(fun y=>∑ i ∈ s,p i y) from funext (fun i=>sum_apply ..)]; exact ContDiffAt.sum (fun j hj=>h j (mem_insert_of_mem hj))
noncomputable def Flux (u:I→E)(H:I→ScriptJ E)(S:Finset I)(p:ScriptJ E):ScriptJ E:=∑ i∈S,H i * Pry (u i) p
noncomputable abbrev divergence (u:I→E)(H:I→ScriptJ E)(S:Finset I):= ∑ i∈S,Pry (u i) (H i)
lemma plyAdd (u:I→E)(H:I→ScriptJ E)(S:Finset I)(p q:ScriptJ E)(hp:p.B)(hq:q.B): Flux u H S (p+q)= Flux u H S p+ Flux u H S q:=by unfold Flux; simp_rw [pryAdd _ _ _ hp hq, mul_add];rw[sum_add_distrib]
lemma plyFlux (u:I→E)(H:I→ScriptJ E)(S:Finset I)(p q:ScriptJ E)(hp:p.B)(hq:q.B): Flux u H S (p*q)= p*Flux u H S q+Flux u H S p*q:=by
     unfold Flux; simp_rw [pryMul _ _ _ hp hq, mul_add]; rw [sum_add_distrib, Finset.mul_sum, Finset.sum_mul]; congr 1 <;> (apply Finset.sum_congr rfl; intro i _; ring)
omit [FiniteDimensional ℝ E] in
lemma sumBat (s:Finset I)(p:I→ScriptJ E)(h:∀ i∈s,(p i).B): ScriptJ.B (∑ i∈s,p i):=by induction s using Finset.induction_on with
     | empty=>rw[sum_empty]; intro i; exact Bond.keep ((0:Token).seq i)
     | insert i s hi ih=> rw [sum_insert hi]; exact ScriptJ.key (h _ (mem_insert_self ..)) (ih (fun i hI=>h _ (mem_insert_of_mem hI)))
lemma fluxB (u:I→E)(H:I→ScriptJ E)(S:Finset I)(h:∀ i∈S,(H i).B)(p:ScriptJ E)(hp:p.B): ScriptJ.B (Flux u H S p):= sumBat _ _ (fun i hi=> height (h i hi) (pryB _ _ hp))
lemma diveB (u:I→E)(H:I→ScriptJ E)(S:Finset I)(h:∀ i∈S,(H i).B): ScriptJ.B (divergence u H S):=sumBat _ _ (fun _ hi=> pryB _ _ (h _ hi))
-- div_y integrated. point.T
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
abbrev link (z:E)(x:E): Token:= plainJ (L.P z x)
lemma purge (p:ScriptJ E)(u:E)(hp:p.B): draw (Pry u p) L μ=draw (link L u * p) L μ:=by
      have h (f:E→ℝ) (hx:Bond f):L.average μ (bat u f)=L.average μ ((fun i=> L.P u i) * f):=by
           symm; apply Flock.bask μ L _ _ _ hx (hx.amount u); intro a t; let g(k:ℝ):= a+k • u; have hv:HasDerivAt g u t:=by simpa [g] using! ((hasDerivAt_id' t).smul_const u).const_add a
           exact (hx.smooth.differentiable (by simp)|>.differentiableAt).hasFDerivAt.comp_hasDerivAt t hv
      unfold draw; simp only [Pi.mul_apply,link,plainJ, JetS.ml_h,JetS.ml_l,JetS.ml_s, zero_mul,add_zero]; exact eta _ _ (h _ (hp 0)) (h _ (hp 1)) (h _ (hp 2))
end YM.OPE.Variance
