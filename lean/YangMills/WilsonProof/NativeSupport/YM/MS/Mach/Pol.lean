import YM.MS.Mach.Pol
import YM.MS.Halo.Mint
/-!
# Constructing polynomial representatives of MS seeds
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Literal Halo Alps Native
open scoped Topology ContDiff InnerProductSpace
variable {I E J M:Type} [AddCommGroup E][Module ℂ E][AddCommGroup J] [Module ℂ J] [ AddCommGroup M][Module ℂ M]
-- μ scale independent polynomials, z=g formal. not ζ=ε.
variable {f g:ℂ→E}{a:ℂ→J}
namespace Present
lemma yes (f:Box E): Present fun z=>value E z f:= ⟨f,rfl⟩
lemma sub (h:Present f)(he: Present g): Present (fun z=> f z-g z):= by obtain ⟨V,rfl⟩:=h; obtain ⟨W,rfl⟩:=he; exact ⟨V-W, funext fun z=> map_sub _ _ _ ⟩
lemma sum (S:Finset I){f:I→ℂ→ E}(h:∀ i∈ S,Present (f i)): Present fun z=>∑ i∈ S,f i z:= by
    classical
    induction S using Finset.induction with | empty=> simp_rw [Finset.sum_empty]; exact here _| insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).add ( ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
variable [Module ℝ E][IsScalarTower ℝ ℂ E]
/-- real axis suffices: currents/budgets/resp. Does not pick a norm on kernels. -/
lemma pay {K:Submodule ℝ E}(h:f∈ (show Set (ℂ→E) from {p|∀ i:ℝ,p i∈ K}))(V:Box E)(hp:∀ z,value E z V=f z)(k:ℕ): V k ∈ K := by
   by_contra hc; obtain ⟨ℓ,hL,hK⟩:= Submodule.exists_dual_map_eq_bot_of_notMem hc inferInstance
   have ht : ∀ i:ℝ,(∑ j∈ V.support,i^j*ℓ ( V j ))=0:= by
        intro x; apply (Submodule.mem_bot ℝ).mp; rw [← hK]; have he:x^1=x:= pow_one x; refine ⟨f x,(Set.mem_setOf.mp h) x,?_⟩; rw [← hp, valued,map_sum]; simp_rw [← Complex.ofReal_pow]; apply Finset.sum_congr rfl; intro i hi; rw [ show (((x^i:ℝ):ℂ)) • V i=(x^i:ℝ) • V i from IsScalarTower.algebraMap_smul ℂ (x^i:ℝ) _, map_smul, smul_eq_mul] -- name
   have hh (i k:ℕ)(a:ℝ) : iteratedDeriv k (fun z:ℝ=> z^i • a) 0= if k=i then (i.factorial:ℝ)*a else 0:= by rw [ iteratedDeriv_smul_const (by fun_prop), iteratedDeriv_fun_pow_zero ]; split; rfl; simp
   obtain hx:= congr_arg (fun f:ℝ→ℝ=> iteratedDeriv k f 0) (funext ht); rw [ iteratedDeriv_fun_sum,Finset.sum_eq_single_of_mem k (Finsupp.mem_support_iff.mpr (by intro h; exact hL (by rw [h,map_zero]))) ] at hx
   · simp only [smul_eq_mul] at hh; rw [ show _=_ from hh k k (ℓ (V k)),if_pos rfl, iteratedDeriv_const ] at hx; exact (mul_ne_zero (show (k.factorial:ℝ)≠0 from by exact_mod_cast Nat.factorial_ne_zero k ) hL) (by simpa using hx)
   · intro j _ hd; exact (hh j k _).trans (if_neg (Ne.symm hd))
   intro i _; fun_prop
end Present
end YM.MS.Mach
