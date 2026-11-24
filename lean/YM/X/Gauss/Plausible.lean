import YM.PertExtension.GaussianIBP
/-!
Polynomial functions on finite dimensional real E. For gauge-composition arguments before estimating physical values. No positivity assumptions here. Integration ops elsewhere. Use `lm` with tower Real via Bundle.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gauss
open Function Filter Set ComplexConjugate PertExtension PertExtension.Series
open scoped BigOperators Topology ContDiff Classical
variable {E F J : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
local notation "L"=> Module.Dual ℝ E
inductive Plausible {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E] : (E→ℝ)→Prop
 | atom (c:ℝ): Plausible (fun _=>c)
 | times (f:E→ℝ)(a:E→ₗ[ℝ]ℝ): Plausible f → Plausible (f*(⇑a))
 | add {f g}: Plausible f → Plausible g → Plausible (f+g)
namespace Plausible
variable {f g:E→ℝ}{b:J→E→ℝ}
omit [FiniteDimensional ℝ E] in
lemma scale (c:ℝ)(h:Plausible f):Plausible (c • f):= by
   induction h with
   | atom d=> exact atom _
   | times p a _ hi=> rw [smul_mul_assoc c p a|>.symm]; exact times _ a hi -- dir
   | add _ _ h1 h2=> rw [smul_add]; exact h1.add h2
omit [FiniteDimensional ℝ E] in
lemma neg (h:Plausible f):Plausible (-f):= neg_one_smul ℝ f ▸ h.scale (-1)
omit [FiniteDimensional ℝ E] in
lemma sub (hf:Plausible f)(hg:Plausible g):Plausible (f-g):= sub_eq_add_neg f g ▸ hf.add hg.neg
omit [FiniteDimensional ℝ E] in
lemma mul (hf:Plausible f)(hg:Plausible g):Plausible (f*g):= by
   induction hg with
   | atom c=> rw [← Pof] -- comm scalar
              exact hf.scale c
   | times p a _ ih=> rw [← mul_assoc]; exact times _ a ih
   | add _ _ h1 h2=> rw [mul_add]; exact h1.add h2
 where Pof (c : ℝ): c • f=f*(fun _=>c):= by ext; simp; exact mul_comm ..
omit [FiniteDimensional ℝ E] in
lemma sum {k:Finset J}(hb:∀ i∈k,Plausible (b i)):Plausible (∑ i∈k,b i):= by
   induction k using Finset.induction_on with
   | empty=> rw [Finset.sum_empty]; exact atom 0
   | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (hb i (by simp)).add (ih fun k hk=> hb k (by simp [hk]))
omit [FiniteDimensional ℝ E] in
lemma line (a:L): Plausible (⇑a):= by
   have he:Plausible ((1:E→ℝ)*(⇑a)):= Plausible.times _ a (atom 1); rwa [one_mul] at he
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma app (M:E→ₗ[ℝ] F) {w:F→ℝ}(h:Plausible w):Plausible (w ∘ M):= by
   induction h with
   | atom v=> exact atom _
   | times v a _ ih=> exact times _ (a.comp M) ih
   | add _ _ h g=> exact h.add g
lemma smooth (h:Plausible f): ContDiff ℝ ω f:= by
   induction h with
   | atom v=> exact contDiff_const
   | times v a _ ih=> exact ih.mul a.toContinuousLinearMap.contDiff
   | add _ _ h g=> exact h.add g
lemma invoice (h:Plausible f): Zone.Invoice (Radial.zone (E:=E)) f:= by
   induction h with
   | atom v=> exact Zone.Invoice.const v
   | times v a _ ih=> exact ih.mul (GaussianScore.Law.linearInvoice a)
   | add _ _ h g=> exact h.add g
omit [FiniteDimensional ℝ E] in
lemma prod {k:Finset J}(hb:∀ i∈k,Plausible (b i)):Plausible (∏ i∈k,b i):= by
   induction k using Finset.induction_on with
   | empty=> rw [Finset.prod_empty]; exact atom 1
   | insert i s hi ih=> rw [Finset.prod_insert hi]; exact (hb i (by simp)).mul (ih fun k hk=> hb k (by simp [hk]))
end Plausible

def diff' (v:E)(f:E→ℝ)(x:E):= fderiv ℝ f x v
namespace Plausible
variable {f g:E→ℝ} (v:E)
lemma ds (hf:Plausible f):Plausible (diff' v f):= by
   induction hf with
   | atom c=> unfold diff'; simp only [fderiv_fun_const,_root_.zero_apply]; exact atom _
   | times p a hp ih=>
     let z : E→ℝ :=a
     have he : diff' v (p*z)= diff' v p * z+(a v) • p:= by
        funext x; unfold diff'
        rw [fderiv_mul (hp.smooth.differentiable (by simp) x) (show DifferentiableAt ℝ z x from a.toContinuousLinearMap.differentiableAt),show fderiv ℝ z x=a.toContinuousLinearMap from a.toContinuousLinearMap.fderiv]; simp only [_root_.smul_apply,_root_.add_apply, _root_.mul_apply, smul_eq_mul]; change p x*a v+z x*(fderiv ℝ p x v)= (fderiv ℝ p x v)*z x+a v*p x; ring
     rw [he]; exact (Plausible.times _ a ih).add (scale _ hp)
   | add hx hy h g=> rw [show diff' v _=diff' v _+diff' v _ from funext (fun x=> by rw [diff', fderiv_add (hx.smooth.differentiable (by simp) x) (hy.smooth.differentiable (by simp) x)]; rfl)]; exact h.add g
-- separate generic multilinear closure
lemma diagonal {J : Type*} [Fintype J] (f:MultilinearMap ℝ (fun _ : J=>E) ℝ): Plausible fun x=> f (fun _=> x) := by
   let B:=Module.finBasis ℝ E
   have he : (fun x=> f (fun _=> x)) = ∑ p:J→Fin (Module.finrank ℝ E), (f (B ∘ p)) • (∏ i:J,(B.coord (p i):E→ℝ)) := by -- type conflict
      funext x; change f (fun _=> x)=_; conv_lhs=> rhs; intro i; rw [←B.sum_equivFun x] -- syntax?
      rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ,Finset.sum_apply]; apply Finset.sum_congr rfl; intro i hi; rw [Pi.smul_apply,Finset.prod_apply]; convert! (MultilinearMap.map_smul_univ f _ _) using 1; exact mul_comm ..
   rw [he]; exact sum fun p _=> scale _ (prod fun i _=> line _)
lemma stamp (t:E→ℝ)(i:ℕ):Plausible (Radial.jet t i):=
 scale _ (diagonal (iteratedFDeriv ℝ i t 0).toMultilinearMap)
end Plausible
end YM.PositionX.Gauss
