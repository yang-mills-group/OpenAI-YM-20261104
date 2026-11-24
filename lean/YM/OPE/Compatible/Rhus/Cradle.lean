import YM.OPE.Compatible.Rhus.Nail
/-! Snap character allocation of labels -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Labels Tensor WithLp Source Drops WardBin Planned.PrimaryIntegral295.Parts
open scoped Topology BigOperators Classical ContDiff
variable {r d m n j:ℕ}{c:ℝ}{W:Type*}{G:Gauge}
namespace Script
open Page
-- p ↦ f on snap. read expansion through d.
def cate (d:ℕ) (p: Labels.Label G j)(x:Snap G d):= read (expand d x) p.val
lemma returnL {p:Labels.Label G j}(h:j≤d)(x:Jet G):cate d p (trunk d x) = read x p.val:= racts (raiseLabel G h p) x
lemma fareJet (p:Labels.Pol G)(d:ℕ)(k:WithTop ℕ∞): ContDiff ℝ k (fun x:Snap G d=> Labels.read (expand d x) p):=by
    induction p using MvPolynomial.induction_on with
    | C a=> simp only [Labels.read,MvPolynomial.aeval_C]; exact contDiff_const
    | add p q hp hq=> simp only [map_add]; exact hp.add hq
    | mul_X A i ih=>
      simp only [map_mul, Labels.read,MvPolynomial.aeval_X]; apply ih.mul
      by_cases he:i.1<d-1
      · let v: Fin (d-1):=⟨i.1,he⟩; let x: Snap G d→ₗ[ℝ] ℝ:= ((Labels.axes G i.1).coord i.2) ∘ₗ LinearMap.proj v
        simp only [Labels.coord, Drops.expand, dif_pos he]; exact Complex.ofRealCLM.contDiff.comp (g:=Complex.ofRealCLM) (f:=x) x.toContinuousLinearMap.contDiff
      simp only [Labels.coord,Drops.expand,dif_neg he]; exact contDiff_const
lemma surged (p:Labels.Label G j)(h:p∈Grade (n+r,r))(e:ℕ):∃ B:SpineX G r e, Tensor.diagonal B = cate e p ∧ Tensor.Sym B:=by
     let f:=cate e p; have hf : ContDiffAt ℝ r f 0:= (fareJet p.val e _).contDiffAt; refine ⟨Tensor.coeff f r 0,funext fun x=>?_,Tensor.coeff_symm hf⟩; rw [← leading_tensor x f hf]; have he(t:ℝ): f (t • x)= t^r • f x:=by unfold f cate; rw [expand_smul]; exact Next.Foundations.read_pure _ h t
     rw [funext he,lead_monomial,if_pos rfl]
abbrev Lode (g:G.El): Snap G d→L[ℝ] Snap G d:=LinearMap.toContinuousLinearMap (LinearMap.pi fun i: Fin (d-1)=> Taylor.paint g∘ₗ LinearMap.proj (φ:=fun j:Fin (d-1)=>Taylor G j.val) i)
lemma surgedFields (p:Labels.Label G j)(d:ℕ) {B:SpineX G r d}(hp:Tensor.diagonal B=cate d p)(h:Tensor.Sym B) :
   (∀ u:G.El,∀ x:Fin r→Snap G d,B (fun i=>Cast u (x i))=B x):=by
        intro u x; let A:= B.compContinuousLinearMap (fun _=> Lode u); have hu(v:Snap G d): Lode u v=Cast u v:=rfl
        have he:Tensor.diagonal A=Tensor.diagonal B:=by
           ext1 x; change Tensor.diagonal B ((Lode u) x) = _; rw [hp,hu]; unfold cate; rw [show expand d (Cast u x)=colored u (expand d x) from funext fun j=> by by_cases h:j<d-1<;>simp [Cast,h,expand,colored]]; exact p.property.2 ..
        exact congr_arg (fun v:SpineX G r d=>v x) (Tensor.ext_diag A B (fun x s=>h (fun i=> Lode u (x i)) s) h he)
lemma surgedEngs (p:Labels.Label G j)(d:ℕ) {B:SpineX G r d}(hp:Tensor.diagonal B=cate d p)(h:Tensor.Sym B)(hw:p∈ Grade (n+r,r)) :
   (∀ t:ℝ,∀ x:Fin r→Snap G d, B (fun i=>engineered t (x i))=t^(n+r) • B x):=by
        intro t x; let A:= B.compContinuousLinearMap fun _=> engineered t
        have he:Tensor.diagonal A=Tensor.diagonal (t^(n+r) • B):=by
           ext1 x; change Tensor.diagonal B (engineered t x)= t^(n+r) • Tensor.diagonal B x; rw [hp]; unfold cate; rw [← expand_jet, scaled_grade _ _ _ hw] -- `_`
        exact congr_arg (fun v:SpineX G r d=> v x) (Tensor.ext_diag A _ (fun x z=>h (fun i=>engineered t (x i)) z) (fun x z=>congr_arg (HSMul.hSMul (t^(n+r))) (h x z)) he)
lemma germKitchen (p:Labels.Label G j)(d:ℕ) {B:SpineX G r d}(hp:Tensor.diagonal B=cate d p)(h:Tensor.Sym B)(hw:p∈ Grade (n+r,r))(i:Fin r→ Fin (d-1)) (x:∀ y,Taylor G (i y).val)(hD:rankX i≠ n): B (fun j=>monoX (i j) (x j))=0:=by
        let v(j:Fin r):Snap G d:= monoX (i j) (x j); have ht(t:ℝ) : B (fun i=>engineered t (v i))=t^(rankX i+r) • B v:=by
            rw [show (fun i=>engineered t (v i))=(fun j=>(t^((i j).val+2)) • v j) from ?_]
            · rw [B.map_smul_univ,prod_pow_eq_pow_sum]; exact congr_arg (fun t:ℕ=> _^t • B v) (costOff i) -- fail hole
            ext1 j; ext1 y; by_cases he:y=i j
            · rw [he]; rfl
            rw [engineered_at]; simp [Pi.single_eq_of_ne he,v,monoX]
        have hp(t:ℝ):t^(n+r) • B v=t^(rankX i+r) • B v:=((surgedEngs p d hp h hw) t v).symm.trans (ht t)
        exact (show B v=0 by
             rw [← (show leading (n+r) (fun t:ℝ=>t^(n+r) • B v)=_ from (lead_monomial (n+r) (n+r) (B v)).trans (if_pos rfl))]
             rw [funext hp,lead_monomial,if_neg (by omega)]) -- B v replaced both? rw at goal
end Script
end YM.OPE.Flume
