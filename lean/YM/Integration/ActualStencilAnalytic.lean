import YM.Integration.ActualLeadingSeries

/-! Analyticity of the actual finite Wilson stencil in the full log-link
increment chart. The matrix-coordinate and polynomial proof is recovered from
RG06.Stencil.Entry/Invoice/Germ; it is independent of their derivative-price
and quotient layers. No regularity or size estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualStencilAnalytic
open _root_.YM.Wilson Lattice Function Gauge Labels Source RG
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {S : Finset Cover}

private def matrixRead (i : Source.Index G S) : G.Mat →ₗ[ℝ] ℂ :=
  let f : G.Mat →ₗ[ℝ] ℂ := LinearMap.proj i.2.2.1 ∘ₗ LinearMap.proj i.2.1
  if i.2.2.2 then (starL ℝ : ℂ ≃L[ℝ] ℂ).toLinearEquiv.toLinearMap ∘ₗ f else f

private lemma matrixRead_apply (i : Source.Index G S) (v:G.Mat): matrixRead i v = (if i.2.2.2 then star (v i.2.1 i.2.2.1) else v i.2.1 i.2.2.1):=by cases h:i.2.2.2 <;> simp [matrixRead,h] <;> rfl


private def matrixReadC (i:Source.Index G S): G.Mat→L[ℝ]ℂ:= (matrixRead i).toContinuousLinearMap

variable {n : Side} (o : Site n)

private lemma curve_entry {S : Finset Cover}(i:Source.Index G S) (U:Config G n):
    ContDiff ℝ ω (fun v : Directions G n=> Source.entry (expandAt o (increment U v)) i):=by
   let T : G.Mat →L[ℝ] ℂ := (matrixReadC i)
   let e : Edge (Site n):= (wrap n i.1.val.1+o,i.1.val.2)
   have he := (G.exp_jet.comp (f:=fun v:Directions G n=> v e) (contDiff_apply ℝ G.Color e)).mul (contDiff_const (c:=G.mat (U e)))
   have hz (v:Directions G n):Source.entry (expandAt o (increment U v)) i=T (G.mat (G.lieExp (v e))*G.mat (U e)):=by unfold Source.entry expandAt increment; rw [G.mat_mul]; erw [show ∀ y:G.Mat, T y= matrixRead _ _ from fun _=>rfl,matrixRead_apply] 
   rw [funext hz]; exact T.contDiff.comp (g:=fun A:G.Mat=>T A) he
theorem polynomial {S:Finset Cover}(p:Source.Formula G S)(U:Config G n) :
    ContDiff ℝ ω (fun v : Directions G n=>MvPolynomial.aeval (Source.entry (expandAt o (increment U v))) p):=by
   induction p using MvPolynomial.induction_on with
   | C x=> simp only [MvPolynomial.aeval_C]; exact contDiff_const
   | add p q hp hq=>simp only [map_add]; exact hp.add hq
   | mul_X p i hp=> simp only [map_mul,MvPolynomial.aeval_X]; exact hp.mul (curve_entry o i U)


end YM.Integration.ActualStencilAnalytic
