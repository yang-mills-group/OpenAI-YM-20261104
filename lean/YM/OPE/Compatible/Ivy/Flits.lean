import YM.OPE.Compatible.Ivy.Fax
/-!
# Coalesce rank tours
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E: Type} [Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {k m d e n:ℕ}{p:Phase}{s:Meeting}{Ω:Row I I}{S: Story I}{P:Curtain I}{t:Side}{x:deck I t}{j:Site t}{Z:E→L[ℝ] deck I t}
lemma conox (i:Phase)(s:Meeting)(h:s∈Plans i)(d e:ℕ)(m n:ℕ)(a σ:ℝ)(C:ℕ→ℝ)(hp:n+HueS (insert 4 s)≤m)(hx:0<σ)(ha:0≤a)(hC:0≤C):
    ∃ D:ℝ, 0 ≤ D∧ ∀ (t:Side)(E: Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (L: Law E)(Ω:Row I I), Ω.strip σ a→∀ (S: Story I)(x:deck I t)(c:ℝ)(Z:E→L[ℝ] deck I t)(b s':Site t), Ribbon S Ω Z L x b m C c → (∀ i≤m, Cold b s' (Oriel L Z) (C i) i)→∀ w, weightsB S m w→∀ P Q:Curtain I,∀ u v,Volume P d m u→Volume Q e m v→ Mold (πc μ L s (Char.Sketch S c x Z) (Char.Ωx d P Z x b) (Char.Ωx e Q Z x s') 4) 0 (D*u*v*Visit w s * (1+‖x‖)^(extendK d i+e)) t n:=by
         choose B hB H using fun d e=> comet (I:=I) i s h d e m n a σ C hp hx ha hC; let D:=range (d+1); let E':=range (e+1); refine ⟨∑ j∈D,∑ i∈E', B j i, Finset.sum_nonneg (fun j _=> Finset.sum_nonneg fun i _=>hB j i),?_⟩; intro t E _ _ _ _ _ μ _ L Ω hΩ S x c Z b s' hS hK w hW P Q u v hP hV
         let q:=Char.Sketch S c x Z; let U(p y:E→ℝ):=πc μ L s q p y 4; let Y(k):=flash (Q k) Z x s'; let W(k):=flash (P k) Z x b; have hs : okP q s:= branches sizes (fun _=>0) _ x x Z s; have hy :∀ k,Bond (Y k):=fun k=>flashB x s' _ v (hV.2 k)
         have he(k):Bond (W k):=flashB x b _ _ (hP.2 k); let r:=Visit w s; have hU:= Sack.coins (hP.2 0);have hp':=Sack.coins (hV.2 0); have hr:0 ≤ r:=Visit0 (covers hW); let b':=(1+‖x‖)^(extendK d i+e); let f(j k):= B j k*u*v*r*b'; have hb(j)(hj:j∈D)(k)(hk:k∈E'):Mold (U (W j) (Y k)) 0 (f j k) t n:=by
              have ht:extendK j i+k≤extendK d i +e := Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right (Nat.le_of_lt_succ (mem_range.mp hj)) _) _) (Nat.le_of_lt_succ (mem_range.mp hk)); exact le_trans (H j k _ E μ L Ω hΩ S _ _ _ _ _ hS (hK _ le_rfl) hK w hW _ _ _ _ (hP.2 j) (hV.2 k)) (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) ht) (show 0 ≤ B j k*u*v*r from by have :=hB j k; positivity))
         have h4:=rows i s h; rw [cells,cells]; change Mold (πc μ L s q (∑ j∈D,W j) (∑ k∈E',Y k) 4) _ _ _ _; rw [πc_along μ L s q _ h4 _ (Sumbond _ _ fun i _=>hy i) W D hs fun i _=>he i]; simp_rw [show ∀ j,πc μ L s q (W j) (∑ k∈E',Y k) 4=∑ k∈E',U (W j) (Y k) from fun j=> πc_batches μ L s q _ h4 (W j) Y _ hs (he _) fun _ _=>hy _]; have ht:=moldSum (fun j hj=> moldSum (fun i hi=>hb j hj i hi)); simp only [sum_const_zero] at ht; apply ht.trans_eq; unfold f; simp_rw [sum_mul];rfl
omit [Fintype I] in
lemma flairCost (p: Curtain I)(d:ℕ)(b:ℝ)(x:deck I t) : Flair (b • p) d x j= b* Flair p d x j:=by
     unfold Flair; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=>score_scaled ..
lemma sculpt {a b α:ℝ}(h:Mold a b α t n)(c:ℝ): Mold (c*a) (c*b) (‖c‖*α) t n:=by unfold Mold; rw [←mul_sub,norm_mul,mul_left_comm]; exact mul_le_mul_of_nonneg_left h (norm_nonneg _)
end YM.OPE.Libra.Char
