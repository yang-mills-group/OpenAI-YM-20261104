import YM.OPE.Compatible.Stamen.Income
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cloud
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
open Silt PertExtension GaussianScore Series Flock
-- budget C estimate.O. Use masks of bad axes
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
-- orbit.Book.Mult
protected lemma anthem.song {f:E→ℝ}(h:anthem k f) :∃ p∈harmon E k,f=Strike k p:=by
      induction h with
      | bank k f=>
         let T:= ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _:Fin 0=> E) f
         refine ⟨Pi.single 0 T, ⟨fun n hx=>by rw [Pi.single_eq_of_ne (by omega)], fun l=>?_⟩,?_⟩
         · by_cases h:l=0; subst l; intro v s; congr 1; exact Subsingleton.elim ..; rw [Pi.single_eq_of_ne h]; exact fun _ _=>rfl
         funext i; rw [Strike,sum_eq_single 0];rw [Pi.single_eq_same]; rfl; exact fun j _ h=> (by rw [Pi.single_eq_of_ne h]; rfl); simp
      | @add n f g ha hb hp hx=> obtain ⟨p,hp,rfl⟩:=hp; obtain ⟨q,hq,rfl⟩:=hx; refine ⟨p+q,(harmon E n).add_mem hp hq,?_⟩; funext i; simp only [Strike,Pi.add_apply,Tensor.diagonal,_root_.add_apply,Finset.sum_add_distrib]
      | @cons n c f hf hp=>
           obtain ⟨p,hp,rfl⟩:= hp; let u(i:ℕ)(P:Pole E i):= added P (c.toContinuousLinearMap); let t(i:ℕ):Pole E i:= match i with | 0=>0| j+1=> u j (p j)
           refine ⟨t,⟨fun i hi=>?_,fun i=>?_⟩,?_⟩
           · cases i with
             | zero=>omega
             | succ i=> change u i (p i)= _; refine ext_diag _ 0 (added_sym (p i) (c.toContinuousLinearMap)) (fun _ _=>rfl) (funext fun v=>?_); simp only [u,added_diag, (show ∀ i,i>n→p i=0 from hp.1) i (by omega)]; simp only [Tensor.diagonal,_root_.zero_apply,smul_zero]
           · cases i with
             | zero=> exact fun _ _=> rfl
             | succ i=> exact added_sym (p i) (c.toContinuousLinearMap)
           funext i; simp only[Pi.mul_apply,Strike]; rw [sum_range_succ' (n:=n+1),show Tensor.diagonal (t 0) i=0 from rfl,add_zero, Finset.mul_sum]; exact sum_congr rfl fun a _=> (added_diag (p a) (c.toContinuousLinearMap) i).symm
lemma hymn (U:Submodule ℝ (E→ℝ))(h:∀ p∈U,anthem k p):FiniteDimensional ℝ U:=by
     let V:= (j:Fin (k+1))→ Pole E j.val; let L: ((j:Fin (k+1))→ Pole E j.val) →ₗ[ℝ] (E→ℝ):={toFun:=fun t=>∑ i:Fin (k+1), Tensor.diagonal (t i),map_add':=fun a b=> (by ext i; simp only[Finset.sum_apply,Pi.add_apply,Tensor.diagonal,_root_.add_apply,sum_add_distrib]),map_smul':=fun v x=> (by ext i; simp only [Finset.sum_apply,Pi.smul_apply,Tensor.diagonal,_root_.smul_apply]; exact (Finset.smul_sum ..).symm)}
     exact Submodule.finiteDimensional_of_le (S₂:=LinearMap.range L) (fun i hi=>by obtain ⟨p,hp,rfl⟩:= (h i hi).song; refine ⟨fun j=>p j.val,?_⟩; ext x; change (∑ i:Fin (k+1), _ : E→ℝ) _= _; rw [Finset.sum_apply]; exact (Fin.sum_univ_eq_sum_range (fun i=> Tensor.diagonal (p i) x) _)) -- check args
variable [MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (A:Law E)
lemma trivialCost : Husk μ A j 0:=⟨Bond.zero,fun hi g h=>by rw[zero_mul]; exact singleConst μ A _⟩
lemma limel (g:I→E→ℝ)(h:∀ i, Husk μ A j (g i))(hp:∀ i,anthem k (g i)) (f:E→ℝ)(ht:∀ i:E, HasSum (fun v=>g v i) (f i)): Husk μ A j f:=by
      let U: Submodule ℝ (E→ℝ):= { carrier:= {p| Husk μ A j p ∧ anthem k p},zero_mem':=⟨trivialCost μ A, anthem.bank ..⟩,add_mem':=fun {a b} (x : Husk _ _ j a∧anthem k a)(y: Husk _ _ j b∧anthem k b)=>⟨x.1.split y.1,x.2.add y.2⟩,smul_mem':=fun r x (hx:Husk _ _ j x∧anthem k x)=>⟨hx.1.elementary r,hx.2.scale r⟩ }
      haveI :FiniteDimensional ℝ U:= hymn U (k:=k) fun i hi=>hi.2; let G(p:Finset I):= ∑ i∈p,g i; have he : Tendsto G atTop (𝓝 f):= tendsto_pi_nhds.mpr fun i=> by simpa only [G,Finset.sum_apply] using! (show Tendsto (fun s':Finset I=>∑ x∈s',g x i) atTop (𝓝 (f i)) from ht i)
      have hh : f∈U:= U.closed_of_finiteDimensional.mem_of_tendsto he (Eventually.of_forall fun u=>U.sum_mem (fun i _=>⟨h i,hp i⟩)); exact hh.1
end YM.OPE.Cloud
