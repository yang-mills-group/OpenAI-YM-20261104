import YM.SignedWilsonExpansion.F9.Difference
import YM.SignedWilsonExpansion.F9.Empathy
/-!
# Price of slot commitments incl arbitrary frozen testimony
-/
noncomputable section
set_option autoImplicit false
namespace YM.SignedWilsonExpansion.Commission
open Function Set Filter PowerSeries WilsonCoeffUV.Mer.Xa XSpace.Normalize Tape
open scoped Topology ContDiff BigOperators Classical
variable {E F:Type}[AddCommGroup E][Module ℂ E] [AddCommGroup F][Module ℂ F]
variable {ι κ:Type}{n d r e k l:ℕ} {L:Filter ι}{q:ι→ℝ}
local notation "Ink"=> PowerSeries ℂ
namespace RateQ
variable (h:Maxer L q)
variable {A:ι→ Tape.Table E n}
abbrev Knows (l:Filter ι)(q:ι→ℝ) (A:ι→ Tape.Table E n) (k:ℕ): Prop:=∀ j≤k,∀ u, Billed l q (fun i=> A i j u)
abbrev Costy (l:Filter ι)(q:ι→ℝ) (x:ι→ Ink)(k:ℕ): Prop:=∀ j≤k, Billed l q (fun i=> coeff j (x i))
section smooth
variable {U:ι→ MultilinearMap ℂ (fun _:Fin n=> E) ℂ}
include h
lemma counts {F:Type*}[NormedField F](z:ι→ κ → F)(S:Finset κ)(v:∀ i∈ S,Billed L q (fun j=> z j i)): Billed L q (fun j=>∏ i∈ S,z j i):=by
    induction S using Finset.induction_on with
    | empty=> simpa only [Finset.prod_empty] using Billed.const (1:F)
    | @insert i S u ih=> simp_rw [Finset.prod_insert u]; exact Billed.mul h (v i (Finset.mem_insert_self ..)) (ih (fun j hj=> v j (Finset.mem_insert_of_mem hj)))
lemma booked [Fintype κ](B:Module.Basis κ ℂ E)(P:ι→ Fin n→ E)(p:∀ i: Fin n,Across L q ℂ (fun j=> P j i)) (v:∀ f: Fin n→ κ,Billed L q (fun j=> U j (B ∘ f))): Billed L q (fun j=> U j (P j)):=by
   have hv(x:ι): U x (P x)=∑ f:Fin n→κ,(∏ i, B.repr (P x i) (f i))* U x (B∘ f):=by
       nth_rw 1 [show P x=(fun i=> ∑ j,B.repr (P x i) j • B j) from funext (fun j=> (B.sum_repr ..).symm)]; rw [MultilinearMap.map_sum]; exact Finset.sum_congr (by simp) fun j _=> MultilinearMap.map_smul_univ ..
   have ht(i:Fin n→κ): Billed L q (fun x=> (∏ j, B.repr (P x j) (i j)) * U x (B∘ i)):= Billed.mul h (counts h _ _ (fun j _=> p j (B.coord (i j)))) (v i)
   exact Billed.via (Billed.sum h _ _ (fun j _=> ht j)) (Eventually.of_forall hv)
lemma paidSlots [FiniteDimensional ℂ E] (B:Knows L q A k)(v:d≤k)(P:ι→ Fin n→ E)(p:∀ i: Fin n,Across L q ℂ (fun j=>P j i)): Billed L q (fun j=> A j d (P j)):= booked h (Module.finBasis ℂ E) P p fun i=> B d v _
lemma costF_pow (x:ι→ Ink)(d:ℕ)(v:Costy L q x k): Costy L q (fun i=> (x i)^d) k:=by
    induction d with
    | zero=> intro j _; simp only [pow_zero]; exact Billed.const _
    | succ d ih=> intro j u; simp_rw [pow_succ,coeff_mul]; exact Billed.sum h _ _ (fun i v'=>by have hx:=Finset.mem_antidiagonal.mp v'; exact Billed.mul h (ih i.1 (by omega)) (v i.2 (by omega)))
lemma composedCost (x:ι→Ink)(v:Costy L q x k)(A:ι→ Tape.Table E n)(p:Knows L q A k): Knows L q (fun i=> Tape.composed (A i) (x i)) k:=by
    intro j b z; simp only [Tape.composed,_root_.sum_apply,_root_.smul_apply]; exact Billed.sum h _ _ (fun i p'=> Billed.smul h _ _ (costF_pow h _ i v j b) (p i (by have H:=Finset.mem_range.mp p'; omega) _))
lemma comp_bill [FiniteDimensional ℂ E](v:Knows L q A k)(x:ι→Ink)(w:Costy L q x k)(P:ι→ Fin n→ Tape E)(p:∀ i j,j≤k→Across L q ℂ (fun t=> P t i j)): Costy L q (fun i=> Tape.tabular (Tape.composed (A i) (x i)) (P i)) k:=by
    have he {l:ℕ}(v:Days n)(h:v∈tally l n) (i): v i≤ l:= ((totaled v).mp h) ▸ Finset.single_le_sum (f:=fun i=> v i) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)
    intro i b; simp_rw [tab_coeff]; exact Billed.sum h _ _ fun j hj=> paidSlots h (composedCost h x w A v) ( ( he j (l:=i) hj none ).trans b ) (fun i a=> P i a (j (some a))) (fun k=> p k _ ((he (l:=i) j hj (some k)).trans b)) -- he l uses section param fixed; fix
end smooth
-- Astro expressions of whole panel.TopStamp budget. all multilinear external field frames fixed arbitrary.
variable (B: Tape.Table E n)(P: Fin n→ F→ₗ[ℂ] Tape E)
def exam (B: Tape.Table E n)(P: Fin n→ Tape (F→ₗ[ℂ]E))(x:Fin n→ F): Ink:= Tape.tabular B (fun i=> Tape.spur (P i) (x i))
def testₗ (T:Tape (F→ₗ[ℂ]E)): F→ₗ[ℂ] Tape E where
   toFun:= Tape.spur T
   map_add' _ _:= funext fun _=> map_add ..
   map_smul' _ _:= funext fun _=> map_smul ..
def papers (B: Tape.Table E n)(P: Fin n→ Tape (F→ₗ[ℂ]E))(e:ℕ) : MultilinearMap ℂ (fun _:Fin n=>F) ℂ:= (coeff e).compMultilinearMap ((tabular B).compLinearMap (fun i=> testₗ (P i)))
lemma at_papers (B: Tape.Table E n)(P: Fin n→ Tape (F→ₗ[ℂ]E))(x:Fin n→ F) : Tape.archive (papers B P) x=exam B P x:=PowerSeries.ext fun n=> (coeff_mk ..)
include h
/- Pack evaluation priced through all clock caps and arbitrary acrossT alphabets -/
lemma keeps [Fintype κ](B:Module.Basis κ ℂ F)(X:ι→ Tape.Table E n)(P: ι→ Fin n→ Tape (F→ₗ[ℂ]E))(e:ℕ)(x:ι→ Fin n → F)(v:∀ i,Across L q ℂ (fun j=> x j i))(p:∀ f:Fin n→κ,Billed L q (fun i=> coeff e (exam (X i) (P i) (B∘ f)))): Billed L q (fun i=> coeff e (exam (X i) (P i) (x i))):=by
     apply booked h B (U:=fun i=> papers (X i) (P i) e) x v; exact p
end RateQ
end YM.SignedWilsonExpansion.Commission
