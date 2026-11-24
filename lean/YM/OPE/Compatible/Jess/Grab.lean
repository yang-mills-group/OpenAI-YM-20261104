import YM.OPE.Compatible.Jess.Iota
/-!
# Sap transform relation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Pose
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Bloch Precision Wilson Exterior Flume Flume.Virgin Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Arc Stranded Adhesion Silt
open Shell Char Module Finset
variable {F E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open JetS
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
abbrev merry (c:ℝ):Token:=⟨0,0,c⟩
lemma sparing (p a:ScriptJ E)(f g:E→ℝ)(hp:p.B)(ha:a.B)(hf:Bond f)(hg:Bond g)(hX:∀ i,(p i).s=1):
    let v:E→Token:=fun i=>p i + merry (f i); let q:E→Token:=fun i=>a i + merry (g i); let w(i:E):=(a i).s; let A:=L.average μ
    fair μ L v q=fair μ L p a+ merry (A g+A (f*w)-A w*A f):=by
     intro v q w A; let F:= draw p L μ; let Y:= draw (a*p) L μ; have ht:F.s=1:=by unfold F draw; rw [show (fun i=>(p i).s)= _ from funext hX]; exact singleConst ..
     have hx:ScriptJ.B (a*p):=height ha hp; have he:Y.s=A w:=by change A (fun i=> (a i*p i).s)=_; simp only [JetS.ml_s,hX, mul_one];rfl
     let u:=g+f*w; have hu:Bond u:=hg.add (hf.mul (ha 0))
     have h(i) : q i*v i=(a i*p i)+ merry (u i):=by
          unfold q v u merry; apply eta; · simp
          · simp
          simp only [JetS.ml_h,pl_s,pl_l,pl_h,Pi.add_apply,Pi.mul_apply,hX,add_zero,w];ring
     have hv : draw v L μ=F+ merry (A f):=by
          unfold v F draw merry; apply eta<;> simp only [pl_s,pl_l,pl_h,add_zero]; exact sun μ L (hp 2) hf
     have hy : draw (q*v) L μ=Y+merry (A u):=by unfold Y draw; apply eta<;>simp only [Pi.mul_apply,h,pl_s,pl_l,pl_h,merry,add_zero]; exact sun μ L (hx 2) hu
     unfold fair; rw [hv,hy]; change _=Y/F+_; rw [show A u= A g+A (f*w) from sun _ _ hg (hf.mul (ha 0))]; simp_rw [dv]; apply eta
     · simp
     · simp
     simp only [JetS.ml_h,merry,pl_s,pl_l,pl_h, sp_h, sp_l,sp_s,ht,he, add_zero,one_pow,div_one,inv_one,mul_one];ring
-- neg p0 tuer
lemma rental (p a:ScriptJ E)(v g:E→ℝ)(b r:ℝ)(hp:p.B)(ha:a.B)(hg:Bond g)(hv:∀ i, v i=r-b*L.P i i/2)(hX:∀ i,(p i).s=1):
    let w(i:E):=(a i).s; let A:=L.average μ
    fair μ L (fun i=>p i+merry (v i)) (fun i=>a i+merry (g i))=fair μ L p a+merry (A g-(b/2)*A (hillP w)):=by
     intro w A; let q:E→ℝ:=fun i=>r; have hw : v=q-(b/2) • normE L:=funext fun i=> (hv i).trans (by change _=r-b/2*(L.P i i);ring)
     have ht:Bond v:=by rw [hw]; exact ((Bond.keep (E:=E) r).sub (Bond.scale (b/2) (standE L)))
     rw [show fair μ L _ _= _ from sparing μ L p a v g hp ha ht hg hX]; have hg : Bond w:= ha 0; have h₁:A v=r-b/2*(finrank ℝ E:ℝ):=by -- change (finrank ℝ E:ℝ)
          rw [show v=q + (-(b/2)) • normE L from (by rw [hw,neg_smul]; exact sub_eq_add_neg ..)]; unfold A; rw [sun μ L (Bond.keep _) (Bond.scale _ (standE L)),singleConst,scooted,fullV]; ring
     have h₂:A (v*w)= r*A w-(b/2)*((finrank ℝ E:ℝ)*A w+A (hillP w)):=by
          rw [show v*w=r • w + (-(b/2)) • (normE L*w) from ?_]; swap
          · funext i; rw [Pi.mul_apply,hv]; change _=(r*w i)+ -(b/2)*(L.P i i*w i);ring
          unfold A; rw [sun μ L (Bond.scale _ hg) (Bond.scale _ ((standE L).mul hg)), scooted,scooted, mul_comm (normE L),mul_comm w (normE L), foretell μ L w hg]; ring
     change fair _ _ _ _+ merry (A g+A (v*w)-A w * A v)= _; rw [h₁,h₂]; congr 2;ring
end YM.OPE.Libra.Pose
