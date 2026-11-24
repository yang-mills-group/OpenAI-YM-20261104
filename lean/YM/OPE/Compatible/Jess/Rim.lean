import YM.OPE.Compatible.Jess.Grab
/-!
# Shift response. Generic free pedestal. All t obey smooth paths already.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Pose
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Bloch Precision Wilson Exterior Flume Flume.Virgin Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Paver Rill Glass Coin Pilot Radial Flock Arc Stranded Adhesion Silt
open Shell Char Module Finset
variable {F E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure](L:Law E)
open JetS
lemma flareZero (p q:ScriptJ E)(h:∀ i,(p i).s=1): (fair μ L p q).s= L.average μ (fun i=>(q i).s):=by
      unfold fair; rw [dv, ml_s,sp_s,show (draw p L μ).s=1 from ?_,inv_one,mul_one]
      · change L.average μ _=_; congr! 1; funext i; rw [Pi.mul_apply,ml_s,h,mul_one]
      change L.average μ _= _; rw [show (fun i=> (p i).s)= _ from funext h]; exact singleConst ..
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
omit [MeasurableSpace E] [BorelSpace E] in
lemma orbitD (q:E→ℝ)(p: E)(h:Bond q) : deriv (fun v:ℝ=> q (v • p)) 1=hillP q p:=by
      have hv:HasDerivAt (fun v:ℝ=> v • p) p 1:=by simpa using! ((hasDerivAt_id' (1:ℝ)).smul_const p)
      have ht:= ((h.smooth.differentiable (by simp)|>.differentiableAt).hasFDerivAt.comp_hasDerivAt (1:ℝ) hv).deriv; unfold hillP; simpa only [Function.comp_def,one_smul] using! ht
lemma steer (q:F×E→ℝ)(v:F)(h:Bond q):
     L.average μ (fun y=>hillP q (v,y))-L.average μ (hillP (fun y=>q (v,y)))=deriv (fun t:ℝ=>L.average μ (fun y=>q (t • v,y))) 1:=by
          let T:= (ContinuousLinearMap.toSpanSingleton ℝ v).prodMap (ContinuousLinearMap.id ℝ E); have hh : HasDerivAt (fun t:ℝ=> L.average μ (fun y=>q (t • v,y))) (L.average μ (fun i=> deriv (fun t:ℝ=> q (t • v,i)) 1)) 1:= hotrod μ L (q∘T) (h.compLinear T.toLinearMap) 1
          rw [hh.deriv]; let A(i:E):=hillP (fun y=>q (v,y)) i; let V(i:E):=deriv (fun t:ℝ=> q (t • v,i)) 1; have he : Bond A:= heatE (Shift.leanB q h v); have hv :Bond V:=reel (q∘T) (h.compLinear T.toLinearMap) 1
          rw [show (fun y=>hillP q (v,y))=V+A from ?_,sun μ L hv he]; exact add_sub_cancel_right ..; funext y; let D:=fderiv ℝ q (v,y); have hX:V y=D (v,0):=by
               have ht:HasDerivAt (fun t:ℝ=>(t • v,y)) (v,0) 1:=by convert! (((hasDerivAt_id' (1:ℝ)).smul_const v).prodMk (hasDerivAt_const _ y)) using 1; simp
               simpa only [one_smul] using! ((h.smooth.differentiable (by simp)|>.differentiableAt).hasFDerivAt.comp_hasDerivAt _ ht).deriv
          have hp:A y=D (0,y):=by
               rw [show A y= _ from (orbitD (fun y=>q (v,y)) y (Shift.leanB q h v)).symm]; have ht:HasDerivAt (fun t:ℝ=>(v,t • y)) (0,y) 1:=by convert! ((hasDerivAt_const (x:=(1:ℝ)) v).prodMk ((hasDerivAt_id' _).smul_const y)) using 1; simp
               simpa only [one_smul] using! ((h.smooth.differentiable (by simp)|>.differentiableAt).hasFDerivAt.comp_hasDerivAt _ ht).deriv
          change D (v,y)=V y+A y; rw [hX,hp,←map_add,show (v,0)+(0,y)=(v,y) from Prod.ext (add_zero _) (zero_add _)]
lemma topD (c:ℝ)(p:ScriptJ (F×E))(f:F→ScriptJ E)(g:ScriptJ E)(hp:p.B)(u:F)(r:ℝ)
   (he: ScriptJ.B (f u))(h: ∀ i:F,∀ y,(f i y).s=1)(hg:∀ i,g i=f u i + merry (r-c*L.P i i/2)):
   let w(i:F)(y:E):=p (i,y); let a:= fair μ L (f u) (w u)
   fair μ L g (fun y=>w u y+merry ((c/2)*deriv (fun t:ℝ=> (p (t • (u,y))).s) 1))= a+merry ((c/2)*deriv (fun t:ℝ=> (fair μ L (f (t • u)) (w (t • u))).s) 1) :=by
     intro w a; let Q(v:F×E):=(p v).s; let Z(i:E):= (c/2)*hillP Q (u,i)
     have hp':Bond Q:= hp 0; let x(i:E):= r-c*L.P i i/2
     rw [funext hg]; simp_rw [show ∀ y:E,deriv (fun t:ℝ=>(p (t • (u,y))).s) 1=hillP Q (u,y) from fun y=>orbitD Q (u,y) hp']; rw [rental μ L (f u) (w u) x Z c r he ?_ ?_ (fun _=>rfl) (h _)]; swap
     · exact fun i=> Shift.leanB _ (hp _) u
     swap; · exact Bond.scale _ (Shift.leanB _ (heatE hp') _)
     change _= a+ merry ((c/2)*deriv (fun t:ℝ=> (fair μ L (f (t • u)) (w (t • u))).s) 1)
     have hb (t:ℝ) : (fair μ L (f (t • u)) (w (t • u))).s=L.average μ (fun y=>Q (t • u,y)):= flareZero μ L (f (t • u)) _ (h _)
     rw [funext hb, ← steer μ L Q u hp',show L.average μ Z= _ from scooted μ L (c/2) (fun i:E=>hillP Q (u,i)),mul_sub]
end YM.OPE.Libra.Pose
