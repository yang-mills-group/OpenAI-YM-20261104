import YM.Integration.WilsonMarkedRootedPolynomial
import YM.Analysis.Homogeneous

/-! Homogenization on the genuine coefficient coordinates. Every missing
field leg carries the scalar coupling, not a unit free-link direction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedCoupledPolynomial
open Function Finset Tensor MvPolynomial FormalBulk08 FormalBulk08.Lava
open scoped Classical BigOperators
variable {E X V:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype V]

def word : (r:ℕ)→(Fin r→(E→L[ℝ]ℝ))→T E ℝ r
  | 0,_=>ContinuousMultilinearMap.uncurry0 ℝ E 1
  | r+1,L=>added (word r fun i=>L i.succ) (L 0)

theorem word_value (r:ℕ)(L:Fin r→(E→L[ℝ]ℝ))(x:E):
    diagonal (word r L) x=∏i:Fin r,L i x:=by
  induction r with
  | zero=>simp [word,diagonal]
  | succ r ih=>rw [word,added_diag,ih,Fin.prod_univ_succ];rfl

theorem word_sym (r:ℕ)(L:Fin r→(E→L[ℝ]ℝ)):Sym (word r L):=by
  cases r with
  | zero=>intro v s;rfl
  | succ r=>exact added_sym (word r fun i=>L i.succ) (L 0)

def raise {r:ℕ} (A:T E ℝ r)(L:E→L[ℝ]ℝ):(d:ℕ)→T E ℝ d
  | 0=>if h:r=0 then h ▸ A else 0
  | d+1=>if h:r=d+1 then h ▸ A else added (raise A L d) L

theorem raise_value {r:ℕ} (A:T E ℝ r)(L:E→L[ℝ]ℝ)(d:ℕ)(le:r≤d)(x:E)(one:L x=1):
    diagonal (raise A L d) x=diagonal A x:=by
  induction d with
  | zero=>have :r=0:=by omega
          subst r;simp [raise]
  | succ d ih=>by_cases eq:r=d+1
               · subst r;simp [raise]
               · rw [raise,dif_neg eq,added_diag,one,one_smul,ih (by omega)]

theorem raise_sym {r:ℕ} {A:T E ℝ r} (sym:Sym A)(L:E→L[ℝ]ℝ)(d:ℕ):Sym (raise A L d):=by
  cases d with
  | zero=>by_cases eq:r=0
          · subst r;simpa [raise] using sym
          · rw [raise,dif_neg eq];intro v s;rfl
  | succ d=>by_cases eq:r=d+1
            · subst r;simpa [raise] using sym
            · rw [raise,dif_neg eq];exact added_sym (raise A L d) L

def stamp (L:X→L[ℝ](V→ℝ)) (d:ℕ) (P:MvPolynomial V ℝ): T (ℝ×X) ℝ d :=
  ∑r∈range (d+1),∑v:chain V r,marble r P v • raise
    (word r fun i=>(ContinuousLinearMap.proj (v i)).comp (L.comp (ContinuousLinearMap.snd ℝ ℝ X)))
      (ContinuousLinearMap.fst ℝ ℝ X) d

theorem symmetric (L:X→L[ℝ](V→ℝ)) (d:ℕ) (P:MvPolynomial V ℝ):Sym (stamp L d P):=by
  intro v s;unfold stamp;simp only [_root_.sum_apply,smul_apply]
  apply sum_congr rfl;intro r _;apply sum_congr rfl;intro t _
  let taps (i:Fin r):ℝ×X→L[ℝ]ℝ:=(ContinuousLinearMap.proj (t i)).comp (L.comp (ContinuousLinearMap.snd ℝ ℝ X))
  exact congrArg (fun a:ℝ=>marble r P t • a)
    (raise_sym (word_sym r taps) (ContinuousLinearMap.fst ℝ ℝ X) d v s)

theorem filed (L:X→L[ℝ](V→ℝ)) (d:ℕ) (P:MvPolynomial V ℝ) (tail:∀r,d<r→marble r P=0) (z:X):
    diagonal (stamp L d P) ((1:ℝ),z)=MvPolynomial.eval (L z) P:=by
  have h:=congrArg (MvPolynomial.eval (L z)) (WilsonMarkedRootedPolynomial.levels P d tail)
  rw [←h,map_sum];simp_rw [WilsonMarkedRootedPolynomial.form]
  unfold stamp diagonal
  simp only [_root_.sum_apply,smul_apply]
  apply sum_congr rfl;intro r hr;apply sum_congr rfl;intro v _
  change _ * diagonal (raise _ _ d) ((1:ℝ),z)=_ * _
  rw [raise_value _ _ _ (by simpa using hr) _ rfl,word_value]
  rfl

end YM.Integration.WilsonMarkedCoupledPolynomial
end
