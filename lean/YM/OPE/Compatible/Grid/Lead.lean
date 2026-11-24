import YM.OPE.Compatible.Glow.Puff
/-! # Walk derivative cost. Along logits to order d. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}
namespace Script
open Page
lemma stewRace (G:Gauge)(U:ℝ)(hv:0≤U)(d:ℕ):∃ c:ℝ,0≤c∧∀ (w:List G.Color)(t:ℝ),(∀ i∈w, ‖i‖≤U)→‖iteratedDeriv d (voyageX w) t‖≤c*(w.length+1:ℝ)^d:=by
   induction d using Nat.strong_induction_on with| h d ih=>
      by_cases hd:d=0
      · subst d; exact ⟨G.colorScale,G.colorScale_pos.le,fun w t _ =>by rw [iteratedDeriv_zero,(voyage_norm ..).2]; simp⟩
      choose c hc H using fun i:Fin d=> ih i.val i.isLt
      let z(i:ℕ):=if h:i<d then c ⟨i,h⟩ else (0:ℝ); have hz i:0 ≤ z i:=by unfold z; split; exact hc _;rfl
      let P(i:ℕ):= max 1 G.colorScale*(G.colorScale*U)^i; let f:=(range (d+1)).erase 0; let k (j:ℕ):ℝ:= (d.choose j:ℝ)*P j*z (d-j); have he :0 ≤ G.colorScale:= G.colorScale_pos.le; have ht i:0≤ k i:=by unfold k P; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hz _)
      let C:= ∑ i∈f,k i; have hvv:0 ≤ C:=sum_nonneg (fun i _=>ht i); let D:=C; have hy:0 ≤ D:=hvv
      refine ⟨D,hy,fun w t h=>?_⟩; induction w with
      | nil=>
        change ‖iteratedDeriv d (fun t:ℝ=> (1:G.Mat)) t‖≤ _; have ht : iteratedDeriv d (fun t:ℝ=>(1:G.Mat)) t=0:= by unfold iteratedDeriv; rw [iteratedFDeriv_const_of_ne hd]; rfl
        rw [ht,norm_zero]; positivity
      | cons i w hw=>
        have hi : ‖i‖≤U:= h i (by simp); let E:=(w.length+1:ℝ)^d; have hx:∀ i∈w,‖i‖≤U:= fun j H=> h _ (by simp [H]); let e:ℝ:= w.length+1; have h1e:1 ≤ e:=by unfold e; simp
        rw [show voyageX (i::w)=(horse i)*(voyageX w) from rfl,iteratedDeriv_mul ((runner i).of_le le_top |>.contDiffAt) ((voyageS w).of_le le_top |>.contDiffAt)]
        let q (j:ℕ):G.Mat:= ↑(d.choose j)*iteratedDeriv j (horse i) t * iteratedDeriv (d-j) (voyageX w) t; have hg : ‖q 0‖ ≤ D*E:=by unfold q; rw [Nat.choose_zero_right,Nat.cast_one,Nat.sub_zero,iteratedDeriv_zero,one_mul,Gauge.mul_frob_eq (horse i t) _ (G.mat_star_mul _)]; exact hw hx
        have hn(j:ℕ)(hJ:j∈f):‖q j‖≤ k j * e^(d-1):=by
            have h1:j≠0:= ne_of_mem_erase hJ; have h2:d-j < d:=by omega
            have hx:=H ⟨d-j,h2⟩ w t hx; have he:= (race i t j).trans (show _ ≤ P j from by unfold P; gcongr); unfold q; apply (norm_mul_le ..).trans; change _ ≤ ((d.choose j:ℝ)*P j*z (d-j))*e^(d-1); rw [show (↑(d.choose j):G.Mat)* _= (d.choose j:ℝ) • iteratedDeriv j (horse i) t from by rw [Nat.cast_smul_eq_nsmul];exact nsmul_eq_mul ..|>.symm, norm_smul, Real.norm_natCast]; unfold z; rw [dif_pos h2,mul_assoc (↑(d.choose j)*P j)]; apply mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) (hx.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1e (by omega)) (hc _))) (norm_nonneg _) (mul_nonneg (by positivity) ((norm_nonneg _).trans he)) -- last mul
        rw [← add_sum_erase (range (d+1)) q (mem_range.mpr (Nat.succ_pos d))]; apply (norm_add_le ..).trans; apply (add_le_add hg ((norm_sum_le ..).trans (sum_le_sum hn))).trans;
        rw [← sum_mul]; change D * e^d + D * _ ≤ _; rw [← mul_add]; have hz:d≠0:=hd; cases d with | zero=>simp at hz
                                                                                                     | succ d=>rw [List.length_cons,Nat.cast_add,Nat.cast_one]; apply mul_le_mul_of_nonneg_left _ hy; change e^(d+1)+e^d ≤(e+1)^(d+1); simp_rw [pow_succ]; rw [show e^d * e + e^d=e^d*(e+1) by ring]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (zero_le_one.trans h1e) (by linarith) _) (by linarith)
end Script
end YM.OPE.Flume
