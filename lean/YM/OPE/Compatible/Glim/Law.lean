import YM.OPE.Compatible.Glim.Sorb
/-! # Formal Ward by polynomial Laplace calculus:
  derivative of hat and adjoint of affine direction.

No global measure expansion; standalone formal finite periods only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell
variable {E F I:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
-- consequences
omit [FiniteDimensional ℝ E] in lemma tauNeg (p:ScriptJ E)(hp:p.B): ScriptJ.B (-p):=by
      have h(i):= hp i; exact Xbond (Bond.neg (h 0)) (Bond.neg (h 1)) (Bond.neg (h 2)) -- neg
omit [FiniteDimensional ℝ E] in lemma tauSub (p q:ScriptJ E)(hp:p.B)(hq:q.B): ScriptJ.B (p-q):=by rw[sub_eq_add_neg]; exact ScriptJ.key hp (tauNeg q hq)
variable (L:Law E) [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure]
lemma Divμ (u:I→E)(Y:I→ScriptJ E)(H:Finset I)(hY:∀ i∈H,(Y i).B) (W R: ScriptJ E) (hw:W.B)(hR:R.B) (h:Flux u Y H W+W*Flux u Y H R=W*(indexQ L u Y H-divergence u Y H))(f:ScriptJ E)(hp:f.B): draw (Flux u Y H f*W) L μ= draw (Flux u Y H R*f*W) L μ:=by
    let D:= divergence u Y H; let ζ:=Flux u Y H; let J:= indexQ L u Y H; have ha: ζ W + W*ζ R=W*(J-D):=h
    have he := Ein L μ u Y H hY (f*W) (height hp hw); rw [plyFlux _ _ _ _ _ hp hw] at he; have hx:f*ζ W+ζ f*W+D*(f*W)= ζ f*W-(ζ R*f*W)+f*W*J:=by rw [show ζ W= W*(J-D)-W*ζ R from eq_sub_of_add_eq ha]; ring
    have hb: ScriptJ.B J:=sumBat _ _ fun i hi=> height (hY _ hi) (show ScriptJ.B (link L (u i)) from lower (Bond.glyph (L.P _))); let a:=ζ f*W; let b:=ζ R*f*W; let g:=f*W*J; have ht:a.B:=height (fluxB _ _ _ hY f hp) hw; have hv:b.B:= height (height (fluxB _ _ _ hY _ hR) hp) hw; have hg:g.B:=height (height hp hw) hb
    change draw (f*ζ W+ζ f*W+D*(f*W)) L μ= draw g L μ at he; rw [hx, show ζ f*W-_=a-b from rfl, duoS μ L _ _ (tauSub a b ht hv) hg] at he; change draw a L μ=draw b L μ; rw [← sub_add_cancel a b,duoS μ L _ _ (tauSub _ _ ht hv) hv]; exact (congr_arg (· + draw b L μ) (add_right_cancel (he.trans (zero_add _).symm))).trans (zero_add _)
-- EOM formula weighted Y. marker
noncomputable abbrev Stamp (u:I→E)(Y:I→ScriptJ E)(H:Finset I)(R f:ScriptJ E):ScriptJ E:= Flux u Y H R*f-Flux u Y H f
omit [MeasurableSpace E][BorelSpace E] in lemma stampL (u:I→E)(Y:I→ScriptJ E)(H:Finset I)(hY:∀ i∈H,(Y i).B) (W R: ScriptJ E) (hw:W.B)(hR:R.B): ScriptJ.B (Stamp u Y H W R):= tauSub _ _ (height (fluxB _ _ _ hY W hw) hR) (fluxB _ _ _ hY R hR)
lemma tokenOf (u:I→E)(Y:I→ScriptJ E)(H:Finset I) (hY:∀ i∈H,(Y i).B) (X F J:E→ℝ)(c:Token)(hf:ContDiffAt ℝ ω F 0)(h:∀ x,jet X 2 x=L.P x x/2)(hp':divergence u Y H * Pawn.mold J 0+ Flux u Y H (Pawn.mold J 0)=0)(q r:ScriptJ E)(hq:q.B)(hr:r.B):
    let W:=(fun _:E=>c)*Wax X F J
    fair μ L W (Stamp u Y H (BookW X F) q *r) = fair μ L W (q* Flux u Y H r):=by -- lock
       intro W; let ζ:= Flux u Y H; let A:=q*ζ r; let V:= Stamp u Y H (BookW X F) q *r; let t:=ζ q*r; let D:=BookW X F; have hL:D.B := ScriptJ.key (tallJ _ X) (tallJ _ F); have ht:t.B:=height (fluxB _ _ _ hY q hq) hr; have hW: ScriptJ.B W:= height (p:=fun _:E=>c) (Bfray _) (stampB X F J)
       unfold fair; apply congr_arg (· / _) -- expands fair
       change draw (V * W) L μ=draw (A * W) L μ
       have he:= Divμ L μ u Y H hY W (BookW X F) hW hL (bud L u Y H X F J c hf h hp') (q*r) (height hq hr); rw [plyFlux _ _ _ _ _ hq hr,add_mul] at he; have hz:draw (A*W+t*W) L μ=draw (V*W+t*W) L μ:=he.trans (congr_arg (draw · L μ) (by unfold V Stamp W t ζ; ring)); rw [duoS μ L (A*W) (t*W) (height (height hq (fluxB _ _ _ hY r hr)) hW) (height ht hW),duoS μ L (V*W) (t*W) (height (height (stampL _ _ _ hY D _ hL hq) hr) hW) (height ht hW)] at hz; exact add_right_cancel hz.symm
end YM.OPE.Variance
