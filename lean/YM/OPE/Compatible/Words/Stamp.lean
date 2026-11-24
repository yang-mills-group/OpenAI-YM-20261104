import YM.OPE.Compatible.Words.Map
/-!
# Matrix stockings. natural
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt
open MeasureTheory Function Finset Filter Module Matrix Cascade Cascade.Paver
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial
variable {I J K:Type}[Fintype I][Fintype J]{n k d:ℕ}
local notation "Λ"=> PAD I
local notation "Γ"=> PAD J
section
variable {p:Pole Λ n}
-- first slot enough plus sym; define GoodSpan allowing x any
abbrev Reserve (A:Mat I)(p:Pole Λ n):Prop:= ∀ i v,∀ x, A*ᵥ x=0→ p (update v i x)=0
lemma Reserve.sees {A:Mat I}(p:Pole Λ (n+1))(h:Reserve A p)(x:Λ): Reserve A (p.curryLeft x):=by
     intro i v r hh; have hx:(Fin.cons x (update v i r): Fin (n+1)→ Λ)=update (Fin.cons x v) i.succ r:=by
          ext1 j; refine Fin.cases ?_ (fun j=>?_) j; · simp [Ne.symm (Fin.succ_ne_zero i)]
          by_cases he:j=i; subst j;simp; simp [he]
     exact (congr_arg p hx).trans (h i.succ _ r hh)
lemma Reserve.hits {A:Mat I}(p:Pole Λ (n+2))(h: Reserve A p)(B:Mat I):Reserve A (Semester B p):=by
      intro i v r hh; unfold Semester; simp_rw [_root_.sum_apply]; refine Finset.sum_eq_zero (fun j _=>Finset.sum_eq_zero fun k _=>?_); rw [_root_.smul_apply,show ((p.curryLeft (Pi.single j 1)).curryLeft (Pi.single k 1)) _= _ from (Reserve.sees p h (Pi.single j 1)|>.sees _ _) i v r hh,smul_zero]
lemma currencyP (p:Pole Λ (n+2))(u:Fin n→Λ)(x y:Λ): ((p.curryLeft x).curryLeft y) u= x ⬝ᵥ (Matrix.of (fun a b:I=> ((p.curryLeft (Pi.single a 1)).curryLeft (Pi.single b 1)) u)*ᵥ y):=by
     rw [brewC p, ContinuousMultilinearMap.curryLeft_apply, _root_.sum_apply]; unfold dotProduct; refine sum_congr rfl ?_; intro i _; rw [_root_.smul_apply]; let T:=p.curryLeft (Pi.single i 1); change x i*T.curryLeft y u=x i*(∑ j, ((T.curryLeft (Pi.single j 1)) u) * y j); rw [brewC T, _root_.sum_apply]; congr 1; exact sum_congr rfl fun j _=>mul_comm ..
lemma busbar (P X Y Z:Mat I)(p:Pole Λ (n+2))(hz: ∀ x:Λ,Health P (Z*ᵥ x))(ht:∀ x:Λ,Health P x→Z*ᵥ x=x)(hp:∀ x y:Λ, Health P x→ Health P y→x ⬝ᵥ( X*ᵥ y)=x ⬝ᵥ(Y *ᵥ y))(h:Reserve P p):
     Semester X p=Semester Y p:=by
          ext1 u; let V (a b:I):= p (Fin.cons (Pi.single a 1) (Fin.cons (Pi.single b 1) u)); rw [stanzaR,stanzaR]; apply sandstone P X Y Z (Matrix.of V) hz ht hp
          · intro j v hf; have hx := currencyP p u (Pi.single j 1) v; rw [single_one_dotProduct] at hx
            have hh : ∀ v, ∀ w: Fin n→Λ, P*ᵥv=0→ p (Fin.cons (Pi.single j 1) (Fin.cons v w))=0:=by
                 intro v w hu; let R:= p.curryLeft (Pi.single j 1); let t:Fin (n+1)→Λ:= Fin.cons v w; change R t=0; rw [← update_eq_self (f:=t) 0] -- lemma
                 exact h.sees p _ _ _ v hu
            exact hx.symm.trans (hh _ _ hf)
          intro j v hf; -- use fixed Pi
          have hx := currencyP p u v (Pi.single j 1); simp only [Matrix.mulVec_single_one] at hx; rw [dotProduct_comm]; refine hx.symm.trans ?_; let T:Fin (n+2)→Λ:= Fin.cons v (Fin.cons (Pi.single j 1) u); change p T=0; rw [← update_eq_self (f:=T) 0]; exact h _ _ v hf
end
