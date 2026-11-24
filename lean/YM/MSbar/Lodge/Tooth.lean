import YM.MSbar.Lodge.Ballad
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
variable {σ ι M:Type}[Fintype σ][Fintype ι][MeasurableSpace M]{μ:MeasureTheory.Measure M}[MeasureTheory.IsProbabilityMeasure μ]
open MeasureTheory Set Metric
local notation "Π"=>Positions σ
local notation "Λ"=>Positions ι
variable {k p s:ℕ}{a c C w B V ε:ℝ}{n:Side}{F:Positions σ→ℝ}(P:Positions ι→L[ℝ]Positions σ)
variable {m:ℕ}{D A:ℝ} (Q:Positions ι→L[ℝ]Positions σ)
-- deterministic controls ∆ without volume. polynomial s .cv. use gradient triangular.
variable {Y:Positions σ} (hF : ContDiffAt ℝ k F Y) (K:Positions σ)
variable (hD:∀ i:ι, ∑ j:σ,|P (bolt i) j|≤ D)(h₀:0 ≤D)(l T:List (Positions σ))(i:σ){U:List (Positions σ)}
include hF h₀
lemma tooth (hm:l.length=m) (he:m < k) (hk:∀ b∈l,∑ i:σ, |b i| ≤ D)(hh:∀ L:List σ,L.length=m→|roc F (K:: (L.map Uniform.bolt)) Y|≤C)(hC:0≤C) : |roc F (K::l) Y|≤ D^m*C:=by
    have ht(T:List σ)(v:List Π)(hf: T.length+v.length=m)(h:∀ b∈v,∑ i:σ,|b i| ≤ D) : |roc F (K::((T.map Uniform.bolt)++v)) Y|≤ D^v.length*C :=by
         induction v generalizing T with
         | nil=>rw [List.append_nil,List.length_nil,pow_zero,one_mul]; exact hh T hf -- length+0
         | cons b v ih=>
             let p(T:List σ):= K::(T.map (@bolt σ)); have hX(z:σ): |roc F (p T ++ ((bolt z)::v)) Y|≤ D^v.length*C:=by
                 rw [show p T++ _= K::(((T++[z]).map Uniform.bolt) ++v) from (by unfold p; simp)]
                 exact ih (T++[z]) (by simp only [List.length_append,List.length_cons,List.length_nil] at *;omega) (fun b' hb=>h b' (List.mem_cons_of_mem b hb))
             change |roc F (p T ++ (b::v)) Y| ≤ _; have hp:= Lis.num (f:=F) (p T) v (@bolt σ) b Finset.univ k hF (by unfold p; simp only [List.length_cons,List.length_map] at *; omega); rw [← spiral b] at hp; rw [hp]; apply (Finset.abs_sum_le_sum_abs _ _).trans; refine le_trans (Finset.sum_le_sum (g:=fun i=> |b i| *(D^v.length*C)) (fun i _=>?_)) ?_
             · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hX i) (abs_nonneg _)
             rw [← Finset.sum_mul]; apply (mul_le_mul_of_nonneg_right (h _ (List.mem_cons_self ..)) (mul_nonneg (pow_nonneg h₀ _) hC)).trans_eq; rw [List.length_cons,pow_succ']; ring
    rw [← hm]; exact ht [] l (by simp [hm]) hk
-- replace all through μ gauge derivative.G
variable (hQ:∀ i:ι,∑ j:σ,|Q (bolt i) j|≤ D)(he:m<k)(hh:0≤C)(hq:∀ v:ι,∀ l:List σ,l.length=m → |roc F ((P (bolt v)-Q (bolt v)) :: (l.map (@bolt σ))) Y| ≤ C)
include hD hQ he hh hq
lemma stroke (l:List ι)(hL:l.length=m+1) :
    |roc F ((l.map bolt).map P) Y-roc F ((l.map bolt).map Q) Y| ≤ (m+1:ℕ)*(D^m*C):=by
    let V(Z : Λ →L[ℝ] Π)(l:List ι):= (l.map bolt).map Z
    let X(L:List Π):= roc F L Y
    have hp(Z)(k:List ι) : List.length (V Z k)=k.length:=by unfold V; simp
    have ht(l t:List ι)(hm:l.length+t.length=m+1) : |X (V Q t++V P l)-X (V Q t++V Q l)|≤ (l.length:ℝ)*(D^m*C):=by
        induction l generalizing t with
        | nil=> simp [V]
        | cons a l ih=>
           let v:σ→ℝ:= P (bolt a)- Q (bolt a); let T:=V Q t; let f:= V P l; let p:=V P (a::l); let F':= T++f; let i:= T++p; let u:= T ++ (Q (bolt a)::f); let j:= T++ V Q (a::l)
           have hz :F'.length=m:=by unfold F'; rw [List.length_append,hp P,show T.length=t.length from hp Q t]; rw [List.length_cons] at hm; omega
           have hx(y:Π): X (T++(y::f))= X (y:: F'):= Lis.echo _ hF _ _ (by simp only [List.length_append,List.length_cons]; have hV:T.length+f.length=m:=(List.length_append).symm.trans hz; omega) (List.perm_middle)
           let W(x:Π):= X (x:: F'); have hw(x y:Π): W (x-y)=W x-W y:= by unfold W X; simp only [roc,map_sub]
           have hy : |X i-X u| ≤ D^m*C:= by
               change |X (T ++ (_::f))-X _| ≤ _; unfold u; rw [hx,hx, ← show W v=W (P (bolt a))-W (Q (bolt a)) from hw ..]; apply tooth hF v h₀ F' hz he _ (hq a) hh -- argument order
               intro b hb; obtain he|he:=List.mem_append.mp hb
               · simp only [T,V,List.mem_map] at he; obtain ⟨p,⟨i,hi,rfl⟩,rfl⟩:=he; exact hQ i
               simp only [f,V,List.mem_map] at he; obtain ⟨p,⟨i,hi,rfl⟩,rfl⟩:= he; exact hD i
           have h': |X u-X j|≤ l.length*(D^m*C):=by
               let K:= t++[a]; have hh (Z :List Π) : (V Q K++ Z)=T++(Q (bolt a)::Z):=by unfold T K V; simp
               have hV:= ih K (by unfold K;simp only [List.length_append,List.length_cons,List.length_nil] at *; omega); rw [hh,hh] at hV; exact hV
           change |X i-X j| ≤ _; exact ((abs_sub_le (X i) (X u) (X j)).trans (add_le_add hy h')).trans_eq (by rw [List.length_cons]; push_cast; ring)
    rw [←hL]; exact ht l [] (by simp [hL])
end YM.MSbar.Lodge
