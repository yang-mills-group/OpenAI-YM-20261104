import YM.Integration.WilsonThermometerUnitFilingJointMonomial

/-! Price the symmetric tensor of an actual joint Taylor polynomial from its ordered entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingJointTensor
open Function Finset MvPolynomial RegulatorIR Budget Budget.Packet Budget.Tuple Diagram
open Prim Cluster PertExtension PertExtension.Series Series.Radial Series.Tested WilsonThermometerUnitFilingJointMonomial
open scoped Classical BigOperators ContDiff
variable {I:Type} {k:ℕ} [Fintype I] [DecidableEq I]

def card (c:Tuple (Option I) k→ℝ):Ranked I:=∑ z,c z • row z

theorem printed (c:Tuple (Option I) k→ℝ):
    Satin (card c) ∧ Within k (card c) ∧ ∀ x:I→ℝ,
      MvPolynomial.eval x (packed (card c) k)=∑ z,c z * ∏ i,(z i).elim 1 x:=by
  refine ⟨?_,?_,?_⟩
  · intro r;unfold card;rw [Finset.sum_apply]
    exact symmetric_sum fun z _=>symmetric_scale ((placed z).1 r) (c z)
  · intro r h;by_contra! hp
    apply h;unfold card;rw [Finset.sum_apply]
    apply Finset.sum_eq_zero;intro z _
    have hz:row z r=0:=by by_contra v;exact (not_le.mpr hp) ((placed z).2.1 r v)
    simp only [Pi.smul_apply,hz,smul_zero]
  · intro x;unfold card;rw [pack_sum,map_sum]
    apply Finset.sum_congr rfl;intro z _
    rw [pack_smul,map_mul,eval_C,(placed z).2.2]

theorem price (c:Tuple (Option I) k→ℝ)(r:ℕ)(w:∀ h,Tuple I h→ℝ)
    (pos:∀ h p,0≤w h p)(order:∀ h (e:Equiv.Perm (Fin h)) p,w h (p ∘ e)=w h p):
    ∑p,w r p * |card c r p| ≤ ∑z,w (length z) (name z) * |c z|:=by
  have piece (z:Tuple (Option I) k):
      (∑p,w r p * |row z r p|)≤w (length z) (name z):=by
    by_cases h:r=length z
    · subst r
      simpa only [row,Pi.single_eq_same] using (charge (w (length z)) (order _) (name z)).le
    · simpa only [row,Pi.single_eq_of_ne h,Pi.zero_apply,abs_zero,mul_zero,Finset.sum_const_zero]
        using pos (length z) (name z)
  calc
    _ ≤ ∑ p,∑ z,w r p*(|c z| *|row z r p|):=by
      apply Finset.sum_le_sum;intro p _
      simp only [card,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [abs_mul] using (Finset.abs_sum_le_sum_abs (fun z:Tuple (Option I) k=>c z*row z r p) Finset.univ)) (pos r p)
    _ = ∑ z,(∑p,w r p*|row z r p|)*|c z|:=by
      rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro z _;rw [Finset.sum_mul]
      apply Finset.sum_congr rfl;intro p _;ring
    _ ≤ _:=Finset.sum_le_sum fun z _=>mul_le_mul_of_nonneg_right (piece z) (abs_nonneg _)

def axis (i:Option I):Figure I:=i.elim (1,0) (fun j=>(0,Pi.single j 1))
def entry (F:Figure I→ℝ)(k:ℕ)(z:Tuple (Option I) k):ℝ:=
  (k.factorial:ℝ)⁻¹ * iteratedFDeriv ℝ k F 0 (axis ∘ z)

theorem applied (F:Figure I→ℝ)(k:ℕ)(x:I→ℝ):
    ∑ z,entry F k z * ∏ i,(z i).elim 1 x=jet F k (1,x):=by
  let D:=(iteratedFDeriv ℝ k F 0).toMultilinearMap
  have split:(1,x)=∑ i:Option I,i.elim 1 x • axis i:=by
    apply Prod.ext
    · simp_rw [Prod.fst_sum];simp [Fintype.sum_option,axis]
    rw [Prod.snd_sum];ext1 i;simp [Fintype.sum_option,axis,Finset.sum_apply,Pi.single_apply,mul_ite]
  symm;change (k.factorial:ℝ)⁻¹ * D (fun _=>(1,x))= _
  rw [split,show D _= _ from (D.map_sum (fun _ i=>i.elim 1 x • axis i)),Finset.mul_sum]
  apply Finset.sum_congr rfl;intro z _
  have hv:=D.map_smul_univ (fun i=>(z i).elim 1 x) (fun i=>axis (z i))
  rw [hv];unfold entry;change (k.factorial:ℝ)⁻¹*((∏ i,(z i).elim 1 x)*D (axis ∘ z))= (k.factorial:ℝ)⁻¹*D (axis ∘ z)*(∏ i,(z i).elim 1 x)
  ring

theorem joint (F:Figure I→ℝ)(k:ℕ): Mold k (fun x=>jet F k (1,x)):=by
  have p:=printed (entry F k)
  exact ⟨_,p.1,p.2.1,fun x=>(applied F k x).symm.trans (p.2.2 x).symm⟩

end YM.Integration.WilsonThermometerUnitFilingJointTensor
