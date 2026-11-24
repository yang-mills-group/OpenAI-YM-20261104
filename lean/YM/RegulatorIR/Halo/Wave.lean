import YM.RegulatorIR.Halo.Clutch

/-!
# Read along series-valued inputs at finite orders
Component budgets on $I^r$ alone. No factors from number of inputs, assuming
only bounded-array smooth rays (can choose at each coefficient).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Halo
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Step Matrix StopB Ward Uniform Finset
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff
variable {I J X:Type}{P:ℝ}{G:Gauge}{k e m a r i j:ℕ}{n:Side}

-- no finiteness requirement for reading infinite rotor unless regroup

def pip (u: I→ℝ⟦X⟧)(p:Tuple I r):=∏ i,u (p i)
def rhyme (u:I→ ℝ⟦X⟧)(v: Packet I r)(i:ℕ):=∑'p :Tuple I r,v p*coeff i (pip u p)
def rhymeR (u:I→ℝ⟦X⟧)(T:Orders I)(m:ℕ)(e:ℕ):= ∑ j∈antidiagonal e, ∑ i∈ Finset.range (j.1+m+1), rhyme u (T j.1 i) j.2

lemma rhyme_f [Fintype I] (u:I→ℝ⟦X⟧)(T:Packet I r): rhyme u T i= PowerSeries.coeff i (MvPolynomial.aeval u (render T)):=by unfold rhyme pip; rw [tsum_fintype,render,map_sum,map_sum];simp only [map_mul,MvPolynomial.aeval_C,word,map_prod,MvPolynomial.aeval_X,PowerSeries.algebraMap_eq,coeff_C_mul]
lemma rhyme_v [Fintype I] (T:Orders I)(u:I→ℝ⟦X⟧) : coeff e (ocean (MvPolynomial.aeval u) (rated (fun i=>i+m) T)) = rhymeR u T m e:=by rw [submerge]; unfold rhymeR; simp_rw [rated_v,packed,map_sum,rhyme_f]

-- only shadow through fixed order

def Full {W:Type}{X:W→Type}(x:(w:W)→X w→ℝ⟦X⟧)(k:ℕ) : Prop:=∀ i ≤ k,∃ v:ℝ≥0∞, v≠⊤ ∧ ∀ w z,‖coeff i (x w z)‖ₑ≤ v
section
variable {W:Type}{Y:W→Type}{x:(w:W)→ Y w → ℝ⟦X⟧}
lemma Full.pipes (H:Full x k)(r:ℕ): Full (fun w (p:Tuple (Y w) r)=>pip (x w) p) k:=by
 induction r with
 | zero=> exact fun i _=>⟨‖coeff i (1:ℝ⟦X⟧)‖ₑ,by finiteness,fun w p=>by simp [pip]⟩
 | succ b ih=>
    intro i hi
    have hv : ∀ j∈Finset.antidiagonal i,∃ v:ℝ≥0∞, v≠⊤∧∀ w (p:Tuple (Y w) (b+1)),‖coeff j.1 (x w (p 0))*coeff j.2 (pip (x w) (Fin.tail p))‖ₑ≤v:=by
       intro j hj; have hp:= mem_antidiagonal.mp hj; obtain ⟨v,hc,h⟩:= H j.1 (by omega); obtain ⟨g,ht,hg⟩:= ih j.2 (by omega); exact ⟨v*g,by finiteness,fun w p=> (enorm_mul ..).trans_le (mul_le_mul' (h w (p 0)) (hg w (Fin.tail p)))⟩
    choose! m hm ht using hv; refine ⟨_, (Finset_sum_ne _ _ hm),fun w p=>?_⟩
    dsimp only; rw [show pip _ _= x w (p 0)*pip (x w) (Fin.tail p) from Fin.prod_univ_succ _ , coeff_mul]; exact le_trans (enorm_sum_le ..) (Finset.sum_le_sum (fun j hj=> ht j hj w p))
where
 Finset_sum_ne (s:Finset (ℕ×ℕ))(v:ℕ×ℕ→ℝ≥0∞)(h:∀ i∈s,v i≠⊤): (∑ i∈s,v i)≠⊤:= ENNReal.sum_ne_top.mpr h
lemma songs {L:Meter W}{z:W→ℝ≥0∞}{T:(w:W)→Packet (Y w) r}(h : Carry L z (fun w=>quota (T w) 1)) (H: Full x e)(hp : i ≤ e) : Carry L z fun w=> ‖rhyme (x w) (T w) i‖ₑ:=by
 obtain ⟨v,hv,he⟩:= H.pipes r _ hp
 apply Carry.mono (Carry.mul_right h (Poly.standard L hv))
 intro w; dsimp only; rw [quota_base, ← ENNReal.tsum_mul_right]; unfold rhyme; apply le_trans enorm_tsum_le_tsum_enorm; apply ENNReal.tsum_le_tsum; intro p;rw [enorm_mul];exact mul_le_mul_right (he w p) _
lemma songs_many {L:Meter W}{z:W→ℝ≥0∞}{T:(w:W)→Orders (Y w)}(h:∀ i ≤ e,∀ r,Carry L z fun w=>quota (T w i r) 1)(H:Full x e) : Carry L z fun w=> ‖rhymeR (x w) (T w) m e‖ₑ:=by
 let P (p:ℕ×ℕ) (w:W):=∑ i∈Finset.range (p.1+m+1),rhyme (x w) (T w p.1 i) p.2
 have he:∀ i∈Finset.antidiagonal e,Carry L z fun w=> ‖P i w‖ₑ:=by
    intro i hi; apply Carry.mono (Carry.sum (L:=L) (Finset.range (i.1+m+1)) (fun b w=> ‖rhyme (x w) (T w i.1 b) i.2‖ₑ) ?_) (fun w=> enorm_sum_le ..); have hp:= Finset.mem_antidiagonal.mp hi; exact fun i _ => songs (h _ (by omega) _) H (by omega)
 exact Carry.mono (Carry.sum _ _ he) (fun _=> enorm_sum_le ..)
end

-- absolute, permit source restriction and limits
lemma rhyme_abs (u:I→ℝ⟦X⟧)(T:Packet I r)(k:ℕ)(h:quota T 1≠⊤){c:ℝ≥0∞}(hc:c≠⊤)(H:∀ p:Tuple I r,‖coeff k (pip u p)‖ₑ≤c): quota (fun p:Tuple I r=> T p*coeff k (pip u p)) 1 ≠⊤:=by
 rw [quota_base] at h ⊢; apply ne_top_of_le_ne_top (ENNReal.mul_ne_top h hc); rw [← ENNReal.tsum_mul_right]; refine ENNReal.tsum_le_tsum ?_; intro i; rw [enorm_mul]; exact mul_le_mul_right (H i) _
lemma rhyme_echo (A:Equiv.Perm I)(T:Packet I r)(u:I→ ℝ⟦X⟧) (k): rhyme u (echo A T) k=rhyme (u ∘ A) T k:=by unfold rhyme; rw [← (Equiv.piCongrRight (fun _:Fin r=> A)).tsum_eq]; apply tsum_congr; intro p; change echo A T (onPath A p) * _=_; rw [show _= _ from echos A T p];rfl

section Churn
variable {u:ℝ→ I→ℝ}
def vow (u:ℝ→ I→ℝ) (x:I):= tale (fun t=>u t x)
def filament (v:Jet I)(x:ℝ→I→ℝ)(t:ℝ):= MvPolynomial.eval (x t) v
lemma slim [Fintype I](h:ContDiffAt ℝ ∞ u 0)(v:Jet I) : tale (filament v u)= churn u v:=by
 apply Script.dictates _ (ink u (contDiffAt_pi.mp h) v)
 induction v using MvPolynomial.induction_on with
 | C a => simp only [MvPolynomial.eval_C]; exact contDiffAt_const
 | add f g hf hg=> simp_rw [map_add]; exact hf.add hg
 | mul_X f i H=> simp only [map_mul,MvPolynomial.eval_X]; exact H.mul (contDiffAt_pi.mp h i)
lemma rhyme_tube (v:ℝ→ Horizon G n)(m:ℕ)(T:Orders (Book G n))(e:ℕ): coeff e (reel T m v)= rhymeR (vow (peel v)) T m e := rhyme_v ..
lemma reel_split [Fintype I](T U:Orders I): rated (fun i=>i+m) (T-U)=rated (fun i=>i+m) T-rated (fun i=>i+m) U:=by
 ext1 i;rw [map_sub,rated_v,rated_v,rated_v,Pi.sub_apply]; apply eq_sub_of_add_eq; rw [← pack_add, sub_add_cancel]
end Churn
end YM.RegulatorIR.Halo
