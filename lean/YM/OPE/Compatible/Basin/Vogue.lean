import YM.OPE.Compatible.Basin.Testa
/-!
# Script second flows exact inc Hess price. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody Next.Foundations
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type*} {G:Gauge}{n m c f:Side}{S:StepData c f} {p q:Clip} {R:PathData G}{U V a s:ℝ} {k r:ℕ}
namespace Script
open Virgin
abbrev extX (G:Gauge)(n:Side): Bid.Dir G n≃L[ℝ] Link G n:= (arm G n 1).symm
abbrev swornV (p:Clip)(R:PathData G): Bid.Dir G n→ℝ:= mainTerm p R ∘ represent
abbrev swornY (R:PathData G):Bid.Dir G n→ℝ:=Precision.loop R ∘ represent
abbrev swornX (R:PathData G) (p:Clip):Bid.Dir G n→ℝ:= secondTerm p R ∘ represent
lemma tubesY (R:PathData G)(p:Clip)(n:Side)(h:R.Bounds p s U V): ContDiffAt ℝ ω (swornY R (n:=n)) 0∧ ContDiffAt ℝ ω (swornX R p (n:=n)) 0:=by
    let L:= extX G n; have hx:L 0=0:=L.map_zero; have hy(z:Bid.Dir G n): input G n (L z)=represent z:= congr_arg represent ((arm _ _ _).apply_symm_apply z)
    have hh:=stain_knit R p h (m:=n); refine ⟨?_,?_⟩
    · rw [show swornY R (n:=n)=(turnSeries R.loop)∘ L from funext fun x=> by change Precision.loop R _=Precision.loop R (input G n (L x)); rw [hy]]; exact ((show AnalyticAt ℝ (turnSeries R.loop (m:=n)) (L 0) from hx.symm ▸ turns_analytic _ h.width h.two).contDiffAt.comp 0 L.contDiff.contDiffAt)
    rw [show swornX R p (n:=n)=inputSeries p R∘ L from funext fun x=>by change secondTerm p R _=secondTerm p R (input G n (L x)); rw [hy]]; exact ((hx.symm ▸ hh.analytic : AnalyticAt ℝ (inputSeries p R) (L 0)).contDiffAt.comp _ L.contDiff.contDiffAt)
lemma chartK (R:PathData G)(p:Clip)(n:Side)(h:R.Bounds p s U V): ContDiffAt ℝ ω (swornV p R (n:=n)) 0∧ iteratedFDeriv ℝ 2 (swornV p R (n:=n)) 0=iteratedFDeriv ℝ 2 (swornX R p) 0 :=by
    let A:= inputSeries p R (m:=n); let C:=turnSeries R.cubic (m:=n); let D:= turnSeries R.quartic (m:=n); let L:= extX G n; have he:= (stain_knit R p h (m:=n)).analytic; have hh:=turns_analytic R.cubic h.width h.three (m:=n); have hd:=turns_analytic R.quartic h.width h.four (m:=n); let V:= A+C+D
    have hv : ContDiffAt ℝ ω V 0:= (he.contDiffAt.add hh.contDiffAt).add hd.contDiffAt; have hw(z: Bid.Dir G n):input G n (L z)=represent z:=congr_arg represent ((arm _ _ _).apply_symm_apply z)
    rw [show swornV p R (n:=n)= intended p R∘ L from funext fun i=> by change mainTerm p R _=mainTerm p R (input G n (L i)); rw [hw], intent, show swornX R p (n:=n)= A∘ L from funext fun i=> by change secondTerm p R _= secondTerm p R (input G n (L i));rw [hw]]
    change ContDiffAt ℝ ω (V ∘ L) 0 ∧ _; refine ⟨(show ContDiffAt ℝ ω V (L 0) from L.map_zero.symm ▸ hv).comp 0 L.contDiff.contDiffAt,?_⟩
    erw [jets_linear L.toContinuousLinearMap (hv.of_le le_top),jets_linear L.toContinuousLinearMap (he.contDiffAt (n:=ω) |>.of_le le_top)]; unfold V C D A
    rw [iteratedFDeriv_add_apply ((he.add hh).contDiffAt) (hd.contDiffAt), iteratedFDeriv_add_apply he.contDiffAt hh.contDiffAt,(rays_jet hh _).1 (turns_low _ h.width h.three) 2 (by decide),(rays_jet hd _).1 (turns_low _ h.width h.four) 2 (by decide),add_zero,add_zero]
section
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X][Fintype I]
abbrev listV (p:Script I r)(n:Side):Tensor.T (deck I n) ℝ r:=∑ i:Site n,orchestra p i
lemma muses (p:Script I r)(h:Summable p)(x:Fin r→ deck I n):listV p n x= library n p x:=by unfold listV; rw [_root_.sum_apply]; exact Finset.sum_congr rfl fun i _=> (instruments p h ..).tsum_eq.symm
def Talent (p:Script I r)(L: X→L[ℝ] deck I n)(A:X→ℝ): Prop:=∀ v: Fin r→X, iteratedFDeriv ℝ r A 0 v=(r.factorial:ℝ)*library n p (L∘v)
lemma talent (p: Script I r)(L:X→L[ℝ] deck I n)(A:X→ℝ)(hp:ContDiffAt ℝ ω A 0)(he:Summable p)(hv:p.Idem)(hx:∀ v,WardBin.leading r (fun x:ℝ=>A (x • v))=narrate n p (L v)): Talent p L A:=by
    let B:=(r.factorial:ℝ) • (listV p n).compContinuousLinearMap (fun _:Fin r=>L);
    have h(i): Tensor.diagonal (iteratedFDeriv ℝ r A 0) i=Tensor.diagonal B i:=by
        apply mul_left_cancel₀ (a:=(r.factorial:ℝ)⁻¹) (by positivity); rw [show _*Tensor.diagonal (iteratedFDeriv ℝ r A 0) i= WardBin.leading r (fun x:ℝ=>A (x • i)) from congr_arg ((r.factorial:ℝ)⁻¹ • ·) (iteratedDeriv_on_line (hp.of_le le_top) i).symm,hx]; change _= (r.factorial:ℝ)⁻¹ * ((r.factorial:ℝ)* listV p n _); rw [inv_mul_cancel_left₀ (by positivity),muses p he];rfl
    have hx : iteratedFDeriv ℝ r A 0=B:= Tensor.ext_diag _ _ (fun v i=> Analysis.sym_Jet (hp.of_le le_top) v i) (fun v i=> congr_arg ((r.factorial:ℝ)*·) (pointed hv he n (L∘v) i)) (funext h)
    intro v;rw [hx];change (r.factorial:ℝ)*listV p n _=_;rw [muses p he];rfl
end
end Script
end YM.OPE.Flume
