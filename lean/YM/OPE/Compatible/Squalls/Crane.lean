import YM.OPE.Compatible.Squalls.Card
/-! # Vol principal arity detection. Angular zero degrees are still visible. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics WardBin
open scoped Topology BigOperators Classical ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
lemma swell (p: Script W r)(x:Fin r→fieldX W)(θ: Fin r→ℝ): wholeX p (fun i=> θ i • x i)= (∏ i,θ i)* wholeX p x:=by
    unfold wholeX; rw [← tsum_mul_left]; refine tsum_congr fun i=>?_ ; simp only [wordX, Pi.smul_apply,smul_eq_mul,prod_mul_distrib]; ring
lemma reed (v n:ℕ) (k:Fin r→ℕ) (x:Fin r→ fieldX W) (q:Script W n) :∃ A: Tensor.T (Fin r→ℝ) ℝ n, (∀ θ:Fin n→ Fin r→ℝ,A θ=∑ i:Fin n→Fin r, if (∑ j,(k (i j)+1))=v then (∏ j, θ j (i j))*wholeX q (x ∘ i) else 0) ∧ (∀ θ, Tensor.diagonal A θ=slopeX (fun i=> θ i • x i) k v n q):=by
   let B(u:Fin n→Fin r):Tensor.T (Fin r→ℝ) ℝ n:= if (∑ j,(k (u j)+1))=v then wholeX q (x ∘ u) • ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap fun i=>ContinuousLinearMap.proj (u i)) else 0
   let T:=∑ i:Fin n→Fin r,B i
   suffices h:∀ θ:Fin n→_, T θ=∑ i:Fin n→Fin r, if (∑ j,(k (i j)+1))=v then (∏ j, θ j (i j))*wholeX q (x ∘ i) else 0 by
       refine ⟨T,h,fun θ=>?_⟩; rw [Tensor.diagonal,h]; apply Finset.sum_congr rfl; intro i _; split; exact (swell q (x∘i) _).symm; rfl
   intro θ; unfold T; rw [_root_.sum_apply]; apply Finset.sum_congr rfl; intro b _; unfold B; split_ifs; exact mul_comm ..;rfl
private lemma lowScale (t:ℝ)(x:fieldX W)(h:Low x d):Low (t • x) d:=fun i=>by obtain ⟨f,hp,h⟩:=h i; exact ⟨_,(Flavor Axis d).smul_mem t hp,fun p=>by simp [h]⟩
lemma plazaOne {P:(r:ℕ)→ Script (Shade G) r}(v:ℕ) (x:Fin r→ fieldX (Shade G))(k:Fin r→ℕ)(h:radiantX x k)(hp:(∑ i,(k i+1))=v) (ht:(P r).sorted) (hy: ∀ x:Fin r→ fieldX (Shade G),radiantX x k→summitX P x k v=0): wholeX (P r) x=0:=by
     choose A H hf using fun n=> reed v n k x (P n); have he(θ): Tensor.diagonal (A r) θ=0:=by
        have hh(t:ℝ): (∑ n∈range (v+1), t^n • Tensor.diagonal (A n) θ)=0:=by
           simp_rw [← Tensor.homogeneous,hf]; exact hy _ (fun i=> lowScale _ _ (h i))
        have hz:= congr_arg (leading r) (funext hh)
        have hc:v+1>r:=by have hh: (∑ i:Fin r, (1:ℕ)) ≤ v:= (sum_le_sum (g:=fun i=> k i+1) (fun i _=>by omega)).trans_eq hp; simp at hh; omega
        rw [lead_sum _ _ (fun _ _ =>(monoSmooth ..).contDiffAt)] at hz; simp_rw [lead_monomial] at hz; simpa [hc, leading] using hz
     have hs: Tensor.Sym (A r):=by
        intro θ β; rw [H,H]; let E : (Fin r→ Fin r) ≃ (Fin r→ Fin r):=Equiv.arrowCongr β.symm (Equiv.refl _); rw [← E.sum_comp]; refine sum_congr rfl fun i _=>?_ ; rw [show (∑ j,(k ((E i) j)+1))= _ from Equiv.sum_comp β (fun j=> k (i j)+1)]; split_ifs with h; swap; rfl; congr 1
        · exact Equiv.prod_comp β (fun j=> θ j (i j))
        exact sortedX ht (x ∘ i) β
     let p(i:Fin r): Fin r→ℝ:= Pi.single i 1; have ht := H r p; rw [Tensor.ext_diag _ 0 hs (fun _ _=>rfl) (funext he),Finset.sum_eq_single (fun i:Fin r=>i)] at ht
     · rw [if_pos hp, Finset.prod_eq_one, one_mul] at ht; exact ht.symm; intro i _; erw [show p i i=1 from Pi.single_eq_same ..]
     · intro b _ hb; split_ifs; swap; rfl; rw [show (∏ j,p j (b j))=0 from ?_, zero_mul]; obtain ⟨j,hj⟩:= not_forall.mp (fun H:∀ i,b i=i=>hb (funext H)); exact Finset.prod_eq_zero (mem_univ j) (by unfold p; simp [hj])
     simp
end Script
end YM.OPE.Flume
