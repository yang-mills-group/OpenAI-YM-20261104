import YM.FVA2.Gen.Shuffle
import YM.Analysis.Symmetric
/-! # From partial jets (viewed as along parameter) to drifting jets -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Gen
open Function Set Filter Finset ContinuousMultilinearMap Topology
open scoped ContDiff BigOperators Classical
universe u
variable {E F H : Type u}[NormedAddCommGroup E][NormedAddCommGroup F][NormedAddCommGroup H][NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ H] {f g:E→F}{x a:E}{n k:ℕ}
-- comp CLM before f at point
section
-- universes independent
variable {A B C: Type*}[NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup B][NormedSpace ℝ B][NormedAddCommGroup C][NormedSpace ℝ C]{y:A}{z:B}{p:B→ C}
lemma affine (L:A→L[ℝ]B)(u:ContDiffAt ℝ (n:ℕ) p ( z+L y )): iteratedFDeriv ℝ n (fun t=>p (z+L t)) y= ( iteratedFDeriv ℝ n p (z+L y)).compContinuousLinearMap (fun _=>L):=by
    let h(t:B):=p (z+t); have hh: ContDiffAt ℝ (n:ℕ) h (L y):= u.comp (f:=( z+ · ) ) _ (contDiffAt_const.add contDiffAt_id)
    obtain ⟨s,hs,hS⟩:=hh.contDiffOn le_rfl (by simp); obtain ⟨d,hd,hD,hy⟩:= mem_nhds_iff.mp hs; let w:=L ⁻¹' d; have hw:IsOpen w:= hD.preimage L.continuous; have hx:y∈w:=hy
    change iteratedFDeriv ℝ n (h ∘ L) y = _; rw [ ← iteratedFDerivWithin_of_isOpen _ hw hx, L.iteratedFDerivWithin_comp_right (hS.mono hd) hD.uniqueDiffOn hw.uniqueDiffOn hy le_rfl, iteratedFDerivWithin_of_isOpen _ hD hy ]; unfold h; rw [ iteratedFDeriv_comp_add_left ]
lemma line (u:ContDiffAt ℝ n p z)(v:B): iteratedDeriv n (fun t:ℝ=> p ( z+t • v )) 0= iteratedFDeriv ℝ n p z ( fun _=>v ):= by
    let L:ℝ→L[ℝ]B:= ContinuousLinearMap.toSpanSingleton ℝ v; change iteratedFDeriv ℝ n (fun t:ℝ=>p (z+L t)) _ _=_; rw [ affine L (by simpa using u),_root_.map_zero,add_zero]; change (iteratedFDeriv ℝ n p z) ( fun _=> L 1 ) = _; simp only [L,ContinuousLinearMap.toSpanSingleton_apply,one_smul]
end
-- Full jet at any point
/-- Equality through indicated inclusive **all** smooth formal cost. -/
def Rent (x:E) (n:ℕ)(f g:E→F): Prop:= ∀ i≤n, iteratedFDeriv ℝ i f x=iteratedFDeriv ℝ i g x
theorem Rent.along (u:Rent x n f g){p:ℝ→ E}(hp:p 0=x)(hc:ContDiffAt ℝ ∞ p 0)(hf:ContDiffAt ℝ ∞ f x)(hg:ContDiffAt ℝ ∞ g x): Near n (f ∘ p) (g ∘ p):=by
    intro i hi; subst x; have he : (i:WithTop ℕ∞)≤∞:= WithTop.coe_le_coe.mpr le_top; rw [ iteratedDeriv_vcomp_eq_sum_orderedFinpartition hf hc he, iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hc he ]; exact Finset.sum_congr rfl (fun q _=>by rw [ u _ ( q.length_le.trans hi ) ])
theorem rent_of_line (h: ∀ x:E, Near n (fun t:ℝ=> f ( a+t • x )) (fun t:ℝ=> g (a+t • x)))(hf:ContDiffAt ℝ ∞ f a)(hg:ContDiffAt ℝ ∞ g a): Rent a n f g:=by
    intro i hi; have he : (i:WithTop ℕ∞)≤∞:= WithTop.coe_le_coe.mpr le_top; apply Tensor.ext_diag _ _ (perm_fee (hf.of_le he)) (perm_fee (hg.of_le he)); funext v; unfold Tensor.diagonal; rw [← line (hf.of_le he), ← line (hg.of_le he), h v i hi ]
section
-- transport formula still works for `∞` at point (no smooth assumption everywhere else)
local notation "Q"=> E × H
variable {p q: E×H→F}{z:H}
theorem point (h:∀ x:E,Rent z n (fun t=> p (x,t)) (fun t=> q (x,t)))(hp:∀ x:E,ContDiffAt ℝ ∞ p (x,z))(hq:∀ x:E,ContDiffAt ℝ ∞ q (x,z))(x:E): Rent (x,z) n p q:=by
    intro m hm; induction m generalizing x with
    | zero=> ext1 v; let h:= h x 0 (Nat.zero_le _); exact congrArg ( fun a:Tensor.T H F 0=> a (fun _=>z)) h
    | succ m ih=>
        let a:= (x,z); let J:= Fin (m+1); let X:= iteratedFDeriv ℝ (m+1) p a; let Y:= iteratedFDeriv ℝ (m+1) q a; change X=Y
        -- subtract. if any x-only at all then difference zero by differentiating all t-cost <.
        have he(v:J→ Q)(i:J)(hx:(v i).2=0): X v=Y v:= by
            let σ:= Equiv.swap 0 i; rw [ show X v= X ( v ∘ σ ) from ( perm_fee ((hp x).of_le (WithTop.coe_le_coe.mpr le_top)) v σ ).symm, show Y v=Y ( v ∘ σ ) from ( perm_fee ((hq x).of_le (WithTop.coe_le_coe.mpr le_top)) v σ ).symm ]; unfold X Y; rw [ iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left ]; let l(y:E):=(y,z); let P: E→L[ℝ] Q:= ContinuousLinearMap.inl ..; have hL (u:E): HasFDerivAt l P u:= ( hasFDerivAt_id u ).prodMk ( hasFDerivAt_const z _ ); let A:= Fin.tail (v ∘ σ); let Q':= iteratedFDeriv (E:=Q) (F:=F) ℝ m; let R:= Q' p -- ψ
            have ht : Q' p ∘ l = Q' q ∘ l:= funext fun y=> ih y (by omega)
            have H1: (m:WithTop ℕ∞) <∞:= by exact_mod_cast ENat.coe_lt_top _ --?
            have hf: ( v ∘ σ ) 0=P ((v i).1):= by rw [ comp_apply, show σ 0=i from Equiv.swap_apply_left .. ]; exact Prod.ext rfl hx
            rw [hf]; apply congrArg (fun y:Tensor.T Q F m=> y A); change ( ( fderiv ℝ ( Q' p ) a ).comp P ) _= ( ( fderiv ℝ ( Q' q ) a ).comp P ) _; rw [ ← show ( fderiv ℝ ( Q' p ∘ l ) x )=_ from ( (( hp x ).differentiableAt_iteratedFDeriv (m:=m) H1).hasFDerivAt.comp x (hL x) ).fderiv, ← show ( fderiv ℝ ( Q' q ∘ l ) x )=_ from ( (( hq x ).differentiableAt_iteratedFDeriv (m:=m) H1).hasFDerivAt.comp x (hL x) ).fderiv, ht ]
        let L:=ContinuousLinearMap.inr ℝ E H
        have ht (w:J→ H): X ( L ∘ w )= Y ( L ∘ w ):= by
           let r(t:H):=t-z; -- use p(x,t) = affine with shift (x,0) not (x,z)
           let b:=(x,(0:H)); let K(t:H):=b+L t; have hv(t:H): K t=(x,t):= Prod.ext (add_zero _) (zero_add _)
           have hC (f:Q→F)(hf:ContDiffAt ℝ ∞ f a): iteratedFDeriv ℝ (m+1) (fun t:H=>f (x,t)) z w= iteratedFDeriv ℝ (m+1) f a ( L ∘ w ):= by
               rw [show (fun t:H=> f (x,t))=(fun t:H=> f (b+L t)) from funext fun t=> congrArg f (hv t).symm]; rw [affine L (by rw [ show b+L z=a from hv _ ]; exact hf.of_le (WithTop.coe_le_coe.mpr le_top) ), show b+L z=a from hv _ ]; rfl
           exact ( hC p ( hp x ) ).symm.trans ( Eq.trans ( by rw [h x (m+1) hm] ) (hC q ( hq x )) )
        -- multilinearity if updating one slot. Induct on # remaining slots, remove x parts.
        ext1 v; let v'(i:J):Q:= L (v i).2
        have hx(s:Finset J): (X-Y) (fun i=> if i∈s then v i else v' i) = 0:= by
            induction s using Finset.induction_on with
            | empty=> simp only [Finset.notMem_empty, ↓reduceIte, _root_.sub_apply, sub_eq_zero]; exact ht (Prod.snd ∘ v)
            | @insert i s h' ih'=>
                let q(i:J):Q:= if i∈s then v i else v' i; let e:Q:=((v i).1,0); have hv:e+q i=v i:= Prod.ext (by rw [show q i=v' i from if_neg h']; exact add_zero _) (by rw [show q i=v' i from if_neg h']; exact zero_add _)
                rw [ show (fun j:J=> if j∈insert i s then v j else v' j)=Function.update q i ( e+q i ) from funext fun j=> by rw [hv]; by_cases hx:j=i<;> simp [hx,q], (X-Y).map_update_add q i e (q i), _root_.sub_apply, he _ i (by simp [e]), sub_self, update_eq_self, ih' ]; exact add_zero _
        simpa only [_root_.sub_apply,Finset.mem_univ,↓reduceIte, sub_eq_zero] using hx Finset.univ
end
-- specialized H=ℝ (u=Type)
section
variable {E F:Type}[NormedAddCommGroup E][NormedAddCommGroup F][NormedSpace ℝ E][NormedSpace ℝ F]{p q:E×ℝ→F}
theorem parameter (h:∀ x:E,Near n (fun t=> p (x,t)) (fun t=> q (x,t)))(hp:∀ x:E,ContDiffAt ℝ ∞ p (x,0))(hq:∀ x:E,ContDiffAt ℝ ∞ q (x,0))(x:E): Rent (x,(0:ℝ)) n p q:=point (fun x i hi=>by apply ContinuousMultilinearMap.ext; intro u; rw [ iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,h x i hi ] ) hp hq x
end
end YM.FVA2.Gen
