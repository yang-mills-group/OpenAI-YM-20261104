import YM.RegulatorIR.Primitives.Hear

/-! One joint Taylor word, with its thermal slots removed after differentiation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingJointMonomial
open Function Finset MvPolynomial YM.RegulatorIR Budget Budget.Packet Budget.Tuple Diagram
open Prim Cluster PertExtension.Series
open scoped Classical BigOperators
variable {I:Type} {k r:ℕ} [Fintype I] [DecidableEq I]

def live (z:Tuple (Option I) k):Finset (Fin k):=Finset.univ.filter fun i=>(z i).isSome
def length (z:Tuple (Option I) k):ℕ:=(live z).card
def layout (z:Tuple (Option I) k):Fin (length z) ≃ ↥(live z):=
  (Fintype.equivFinOfCardEq (by simp [length])).symm
def name (z:Tuple (Option I) k)(i:Fin (length z)):I:=
  (z (layout z i)).get (Finset.mem_filter.mp (layout z i).property).2
def island (q:Tuple I r):Packet I r:=symmetry (Pi.single q 1)
def row (z:Tuple (Option I) k):Ranked I:=Pi.single (length z) (island (name z))

omit [Fintype I] [DecidableEq I] in
theorem product (z:Tuple (Option I) k)(x:I→ℝ):
    (∏ i,x (name z i))=∏ i,(z i).elim 1 x:=by
  have read (v:Option I)(hv:v.isSome):x (v.get hv)=v.elim 1 x:=by
    cases v with
    | none=>contradiction
    | some _=>rfl
  have hp (i:Fin (length z)): x (name z i)=(z (layout z i)).elim 1 x:=by
    exact read _ _
  simp_rw [hp]
  rw [Equiv.prod_comp (layout z) (fun i:↥(live z)=>(z i).elim 1 x)]
  rw [Finset.prod_coe_sort (live z) (fun i=>(z i).elim 1 x)]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  cases h:z i with
  | none=>rfl
  | some v=>exact (hi (by simp [live,h])).elim

theorem placed (z:Tuple (Option I) k):
    Satin (row z) ∧ Within k (row z) ∧
      ∀ x:I→ℝ, MvPolynomial.eval x (packed (row z) k)=∏ i,(z i).elim 1 x:=by
  classical
  have length_le:length z≤k:=by
    simpa [length,live] using Finset.card_filter_le (s:=Finset.univ) (fun i:Fin k=>(z i).isSome)
  refine ⟨?_,?_,?_⟩
  · intro r
    by_cases h:r=length z
    · subst r; simpa only [row,Pi.single_eq_same,island] using is_symmetry (Pi.single (name z) 1)
    · rw [row,Pi.single_eq_of_ne h];intro _ _;rfl
  · intro r h
    by_contra! hh
    exact h (Pi.single_eq_of_ne (by omega) _)
  · intro x
    unfold packed
    rw [Finset.sum_eq_single_of_mem (length z) (Finset.mem_range.mpr (by omega))]
    · rw [row,Pi.single_eq_same,island,render_symmetry,render]
      rw [Finset.sum_eq_single_of_mem (name z) (Finset.mem_univ _)]
      · simp only [Pi.single_eq_same,map_one,one_mul,word,map_prod,eval_X];exact product z x
      · intro q _ h;rw [Pi.single_eq_of_ne h,map_zero,zero_mul]
    · intro q _ h;rw [row,Pi.single_eq_of_ne h,render_zero]

theorem charge (w:Tuple I r→ℝ) (permits:∀ (e:Equiv.Perm (Fin r)) p,w (p ∘ e)=w p)
    (q:Tuple I r):∑ p,w p * |island q p|=w q:=by
  classical
  have pos (p:Tuple I r): 0 ≤ island q p:=by
    rw [island,symmetry_at];apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg;intro e _
    by_cases h:p ∘ e=q
    · simp [h]
    · simp [Pi.single_eq_of_ne h]
  simp_rw [abs_of_nonneg (pos _),island,symmetry_at,mul_left_comm (w _) _ (∑ _,_)]
  rw [← Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key (e:Equiv.Perm (Fin r)):
      (∑ p:Tuple I r,w p*(Pi.single q 1 : Packet I r) (p ∘ e))=w q:=by
    calc
      _ = ∑ p,(fun u=>w u*(Pi.single q 1 : Packet I r) u) ((Tuple.perm I e) p):=by
        apply Finset.sum_congr rfl;intro p _;change _= w (p ∘ e) * _;rw [permits];rfl
      _ = _:=Equiv.sum_comp (Tuple.perm I e) (fun p=>w p*(Pi.single q 1 : Packet I r) p)
      _ = _:= by simp [Pi.single_apply]
  calc
    _ = ∑ _ : Equiv.Perm (Fin r), (Fintype.card (Equiv.Perm (Fin r)) : ℝ)⁻¹ * w q := by
      apply Finset.sum_congr rfl;intro e _
      rw [← Finset.mul_sum,key]
    _ = _ := by
      simp only [sum_const,card_univ,nsmul_eq_mul]
      field_simp

end YM.Integration.WilsonThermometerUnitFilingJointMonomial
