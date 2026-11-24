import YM.Frontier6.Bouquet.Anise.Lone

/-! Finite Taylor arrays by lifted directions, usable for the jet formula. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise Tensor
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable (P:Place)[FiniteDimensional ℝ P]
-- label by derivative tensor. (real orientation chosen once for this expansion)
abbrev harp := stdOrthonormalBasis ℝ P
abbrev Kin (P:Place)(j:ℕ):= Fin j→ Fin (dim P)
namespace Kin
variable {P}{j:ℕ}(a:Kin P j)
def take (p:Fin j):P:= harp P (a p)
def phrase : Multiset Room := List.ofFn (fun i:Fin j=> (take a i).val)
lemma phrase_in : ∀ i∈ phrase a, i∈ P:=by intro i hi; unfold phrase at hi; obtain ⟨k,rfl⟩:= List.mem_ofFn.mp (Multiset.mem_coe.mp hi); exact (a.take k).property
lemma phrase_size : (phrase a).card=j:=by simp [phrase]
lemma phrase_path (f:Full P): train P (phrase a) f= Anise.path (List.ofFn a.take) f:=by
    unfold phrase; rw [train_list]; unfold pedal; rw [List.map_ofFn, show ((ontoSpace P) ∘ _)= a.take from funext (fun i=> on_home (a.take i))]
lemma at_point (f:Full P)(x:P): train P (phrase a) f x=iteratedFDeriv ℝ j f x a.take:=by rw [phrase_path, Anise.path_fn f] -- syntax
-- coefficient includes factorial scaled. version accurate machine ℝ complex bridge
abbrev quantity (x:P):ℝ:=∏ i:Fin j,⟪take a i,x⟫_ℝ
lemma quantity_smooth : Smooth (quantity a):= by unfold quantity Smooth; exact contDiff_prod (fun i _=> (innerSL ℝ (take a i)).contDiff)
def count (x:P):ℂ:= ((j.factorial:ℝ)⁻¹ * quantity a x:ℝ)
def event (s:ℝ): Full P:= screen (count a) (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (quantity_smooth a))) (Normal.shrink P s)
lemma event_at (s:ℝ)(x:P): event a s x= count a x*Normal.shrink P s x:=rfl
lemma event_size {s:ℝ}(h:0<s): Fits (2*s) (event a s):=subset_trans (screen_subset (a.count) _ _) (shrink_fits h)
end Kin
lemma fragments (f:Full P)(j:ℕ)(x:P): fragment j (f:P→ℂ) x=∑ a: Kin P j, a.count x * (train P a.phrase f 0):=by
    let A:= iteratedFDeriv ℝ j f 0; let U:= Fin (dim P); let v (i: Fin j) (z:U):= ⟪harp P z,x⟫_ℝ • harp P z; have ht (i: Fin j): ∑ z:U,v i z=x:= (harp P).sum_repr' x;
    change (j.factorial:ℝ)⁻¹ • A (fun _=>x)=_; rw [show (fun _: Fin j=>x)= (fun i=>∑ z:U,v i z) from (funext ht).symm, A.map_sum, Finset.smul_sum]; refine sum_congr rfl (fun i _=>?_)
    let y:Kin P j:= i; rw [Kin.at_point]; unfold Kin.count; rw [show A (fun a=> v a (i a))=y.quantity x • A y.take from A.map_smul_univ _ _, smul_smul, Complex.real_smul]
def series (j:ℕ) (a:Kin P j)(s:ℝ) (f:Full P):= train P a.phrase f 0 • a.event s
lemma portion_series (s:ℝ)(f:Full P)(m:ℕ): Normal.portion s m f=∑ i:Fin (m+1),∑ a:Kin P i, series P _ a s f:=by
   ext1 x; simp only [Normal.portion_at, plan]; rw [Finset.sum_apply,Finset.mul_sum]; simp_rw [_root_.sum_apply]; -- TestFunction? check
   refine sum_congr rfl (fun i _=>?_); rw [fragments,Finset.mul_sum]; apply sum_congr rfl; intro a _; unfold series; rw [smul_apply,Kin.event_at]; change _ = _ * _; ring
end YM.Frontier6.Bouquet
