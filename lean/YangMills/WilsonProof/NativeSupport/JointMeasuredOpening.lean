import YangMills.WilsonProof.NativeSupport.JointNativeStep
import YangMills.WilsonProof.NativeSupport.JointDatedOpening

/-! Opening a clipped native receipt under the *same* tagged Haar integral.
The old density may already involve an arbitrary product of earlier sources. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice RG Wilson Marker MeasureTheory Packet MergeProof.Accent
open scoped Classical BigOperators
variable {V I X T:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype T] [MeasurableSpace X]
local notation "B" => Stock.census V
theorem measured_open (μ:Measure X) (k:T → X → ℂ) (F:T → X → Poly B) (out:Poly B)
    (exact_:∀ s:Finset V,out.part (tag s)=(∑ t:T,∫ x,k t x*(F t x).part (tag s) ∂μ) ∧
      ∀ t,Integrable (fun x=>k t x*(F t x).part (tag s)) μ) (a:V → ℂ):
    openAt a out=∑ t:T,∫ x,k t x*openAt a (F t x) ∂μ := by
  unfold openAt
  simp_rw [(fun s=>(exact_ s).1),Finset.mul_sum]
  rw [sum_comm]
  apply sum_congr rfl;intro t _
  simp_rw [←integral_const_mul]
  rw [←integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with x;apply sum_congr rfl;intro s _;ring
  · intro s _;exact ((exact_ s).2 t).const_mul _

theorem confined_mask (old:Finset V) (P:Poly B):confined old (diagonal (only old) P) := by
  intro s h;by_contra no;exact h (by rw [mask_part,if_neg no])

theorem open_dated (a:V → ℂ) (old seen:Finset V) (inc:old ⊆ seen) (P:Poly B) (p:confined old P)
    (b:I → V) (c:I → ℂ) (probe:V → ℂ) (idp:∀ i∈old,probe i=1)
    (inject:Injective b) (new_:∀ i,b i∉old) (placed:∀ i,b i∈seen) :
    openAt (fun i=>a i*only seen i) (diagonal probe (P*∏ i:I,(1+Poly.send ((Stock.census V).fire (b i)) (c i))))=
      openAt a P*∏ i:I,(1+a (b i)*probe (b i)*c i) := by
  rw [open_diagonal,open_plant _ P old p b c inject univ (fun i _=>new_ i)]
  have before:=open_on (fun i=>a i*only seen i*probe i) a old P p
  rw [before (fun i hi=>by rw [idp i hi,only,if_pos (inc hi),mul_one,mul_one])]
  congr 1
  apply prod_congr rfl;intro i _
  rw [only,if_pos (placed i),mul_one]

theorem measured_dated (μ:Measure X) (k:T → X → ℂ) (P:X → Poly B) (out:Poly B)
    (c:I → X → ℂ) (probe:T → X → V → ℂ) (b:I → V) (exact_:∀ s:Finset V,
      let f (t:T) (x:X):=k t x*(diagonal (probe t x) (P x*∏ i:I,(1+Poly.send ((Stock.census V).fire (b i)) (c i x)))).part (tag s)
      out.part (tag s)=(∑ t:T,∫ x,f t x ∂μ) ∧ ∀ t,Integrable (f t) μ)
    (a:V → ℂ) (old seen:Finset V) (inc:old ⊆ seen) (p:∀ x,confined old (P x))
    (idp:∀ t x i,i∈old → probe t x i=1)
    (inject:Injective b) (new_:∀ i,b i∉old) (placed:∀ i,b i∈seen) :
    openAt a (diagonal (only seen) out)=∑ t:T,∫ x,k t x*(openAt a (P x)*∏ i:I,(1+a (b i)*probe t x (b i)*c i x)) ∂μ := by
  rw [open_diagonal,measured_open μ k _ out exact_]
  apply sum_congr rfl;intro t _
  apply integral_congr_ae
  filter_upwards with x
  rw [open_dated _ old seen inc _ (p x) b _ _ (idp t x) inject new_ placed]

end YM.Integration.InletSusceptibility.JointShadow
