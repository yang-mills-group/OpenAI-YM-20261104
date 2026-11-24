import YM.OPE.Compatible.Spades.Range
/-!
# prices, No cost paid on null. Canonical Schur marginals
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt Tensor Cloud
open Cascade.Paver
variable {E F X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {I J:Type}{i j k r:ℕ}
section
variable [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (A:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
lemma boundedV {p q:E→ℝ}(hq:RunsG A μ q)(hp:∀ x:E,‖p x‖≤q x): ‖A.average μ p‖ ≤ A.average μ q:=by
      unfold Law.average; rw [norm_div,Real.norm_of_nonneg (spent μ A).le]; refine div_le_div_of_nonneg_right ((norm_integral_le_integral_norm _).trans (_root_.Classical.byCases (p:= Integrable (fun i=> ‖(p*A.kern) i‖) μ) ?_ ?_ : (∫ x:E, ‖(p*A.kern) x‖ ∂μ)≤∫ x:E, (q*A.kern) x ∂μ)) (spent μ A).le
      · intro h; exact integral_mono h hq fun i=> by change ‖_ * (A.kern i)‖≤_ *_; rw [norm_mul,Real.norm_of_nonneg (show 0 ≤ A.kern i from Real.exp_nonneg _)]; exact mul_le_mul_of_nonneg_right (hp i) (Real.exp_nonneg _)
      intro h; rw [integral_undef h]; exact integral_nonneg fun i=> mul_nonneg ((norm_nonneg _).trans (hp i)) (Real.exp_nonneg _)
lemma perK {p:E→ℝ}{C:ℝ}(hp:∀ x:E,‖p x‖≤C): ‖A.average μ p‖ ≤ C:= (boundedV A μ (p:=p) (q:=fun _=>C) (runsG _ _ (Stature.poly (Bond.keep _) 0)) hp).trans_eq (singleConst ..)
variable [Fintype I]
lemma Palet (S:E→L[ℝ] PAD I){p:PAD I→ℝ}(h:Stature p k)(i:ℕ)(hv:i ≤ k){C:ℝ}(hh:∀ x, ‖iteratedFDeriv ℝ i p x‖≤ C): ‖FarG A μ S h i‖ ≤ C:=by
       have hp:0 ≤ C:= (norm_nonneg _).trans (hh 0); refine ContinuousMultilinearMap.opNorm_le_bound hp (fun x=>?_); let z:= ∏ j,‖x j‖; rw [SemG _ _ _ h _ hv,norm_mul,norm_inv,Real.norm_natCast]; apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (Nat.factorial_pos _)))); exact perK A μ fun y=> ((iteratedFDeriv ℝ i p _).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hh _) (prod_nonneg fun _ _=>norm_nonneg _)) -- application
end
section
variable [Fintype I](V:Mat I)
local notation "E!"=> PAD I
noncomputable def grunt (k:ℕ):ℝ:=∑ i∈range (k+1), ‖wind i‖
noncomputable abbrev spentW (I:Type)[Fintype I](k:ℕ)(C:ℝ):=C*(Fintype.card I:ℝ)^2*grunt k
lemma spentPos (k:ℕ){C:ℝ}(hp:0 ≤ C):0≤ spentW I k C:= mul_nonneg (mul_nonneg hp (sq_nonneg _)) (sum_nonneg fun _ _=>norm_nonneg _)
lemma SemesterW {C:ℝ}(hv:0≤C)(hp:∀ i j, ‖V i j‖≤ C)(x:Pole E! (k+2)): ‖Semester V x‖≤ C* (Fintype.card I:ℝ)^2 *‖x‖:=by
      refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (mul_nonneg hv (sq_nonneg _)) (norm_nonneg _)) (fun y=>?_); let L:= ∏ i,‖y i‖; rw [stanzaR]; have he(i j:I): ‖ x (Fin.cons (Pi.single i 1) (Fin.cons (Pi.single j 1) y))‖ ≤ ‖x‖*L:=by
           apply (x.le_opNorm _).trans; refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _); rw [Fin.prod_univ_succ]; simp only[Fin.cons_zero,Fin.cons_succ]; rw [Fin.prod_univ_succ]; simp [L,Pi.norm_single]
      refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>∑ _j:I, C*(‖x‖*L)) (fun i _=>(norm_sum_le ..).trans (sum_le_sum (fun j _=>?_)))).trans_eq ?_); · rw [norm_mul]; exact mul_le_mul (hp ..) (he i j) (norm_nonneg _) hv
      unfold L; simp only[sum_const,card_univ,nsmul_eq_mul];ring
lemma Operas (p:Song E!)(h:p∈harmon (PAD I) k){c d:ℝ}(hd:0≤d)(hz:∀ i:ℕ,i ≤ k→‖p i‖≤c)(hv:∀ i j,‖V i j‖ ≤ d)(n i:ℕ)(hp:i≤k): ‖(opus V^n) p i‖≤ spentW I k d ^n*c:=by
      have H : reduces (harmon (PAD I)) (opus V):=by simpa only [one_smul] using opusReducer V 1
      have hc:= (norm_nonneg _).trans (hz 0 (by omega)); let D:= spentW I k d; have hD:0≤D:=spentPos k hd; induction n generalizing i with
      | zero=> simpa using hz i hp
      | succ n ih=>
          let S:=(opus V^n) p; let N:=(Fintype.card I:ℝ); have ht: S∈ harmon (PAD I) k:= harmonic (Nat.sub_le ..) ((iterateD H h n).1); rw [pow_succ', End.mul_apply]; change ‖wind i • Semester V (S (i+2))‖≤ D^(n+1)*_; rw [norm_smul]; by_cases he:i+2≤k
          · let X:=D^n*c; have hy:=mul_le_mul_of_nonneg_left ((SemesterW V hd hv _).trans (mul_le_mul_of_nonneg_left (ih _ he) (by change 0≤d*N^2; positivity))) (norm_nonneg (wind i)); exact hy.trans ((mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _=>norm_nonneg (wind j)) (mem_range.mpr (Nat.lt_succ_of_le hp))) (show 0 ≤ d*N^2*X from by unfold X; positivity)).trans_eq (by change grunt k * _= _; unfold D spentW; ring)) -- cast
          rw [(show ∀ i:ℕ,i>k→S i=0 from ht.1) (i+2) (by omega),semZ,norm_zero,mul_zero]; exact mul_nonneg (pow_nonneg hD _) hc
noncomputable def wakeY (k:ℕ)(I:Type)[Fintype I](t d:ℝ):ℝ:=∑ i∈range (k+1),‖t^i/(i.factorial:ℝ)‖*spentW I k d ^i
lemma Woper (t c d:ℝ)(hd:0≤d)(F:Song E!)(hp:F∈ harmon E! k)(he:∀ i≤k,‖F i‖ ≤ c)(ht:∀ i j,‖V i j‖≤d)(i:ℕ)(hi:i≤k): ‖fixExp (opus V) t k F i‖≤ wakeY k I t d *c:=by
       rw [Hflow,Finset.sum_apply]; unfold wakeY; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun j hj=>?_); let g:= ((opus V)^j) F; rw [Pi.smul_apply,norm_smul]; exact (mul_le_mul_of_nonneg_left (Operas V F hp hd he ht j i hi) (norm_nonneg _)).trans_eq (mul_assoc ..|>.symm)
end
end YM.OPE.Jargon
