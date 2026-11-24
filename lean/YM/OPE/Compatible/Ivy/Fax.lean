import YM.OPE.Compatible.Ivy.Swing
/-!
# rank collecting
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E: Type} [Fintype I] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E]{μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable {k m d e n:ℕ}{p:Phase}{s:Meeting}{Ω:Row I I}{S: Story I}{P:Curtain I}{t:Side}{x:deck I t}{j:Site t}{Z:E→L[ℝ] deck I t}
def rootCush (S:Story I)(Ω:Row I I)(s:Meeting)(d:ℕ)(Q:Curtain I): Curtain I:= ∑ j∈ Finset.range (d+1),Canvas S Ω s j (Q j)
protected def Ωx (d:ℕ)(P:Curtain I)(Z:E→L[ℝ] deck I t)(x:deck I t)(j:Site t)(i:E):ℝ:= Flair P d (x+Z i) j
omit [Fintype I][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in -- E→Deck requires Fintype
lemma cells : Char.Ωx d P Z x j = ∑ i∈range (d+1),flash (P i) Z x j :=funext fun i=> (Finset.sum_apply i (range (d+1)) (fun i=> flash (P i) Z x j)).symm
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in
lemma chips {u:ℝ}(hp: Volume P d k u): Bond (Char.Ωx d P Z x j):=by rw [cells]; exact Sumbond _ _ fun i _=> flashB x j _ _ (hp.2 i)
lemma pano (p:Phase)(s:Meeting)(h:s∈ Plans p) (α u:ℝ)(C:ℕ→ℝ)(hα:0<α)(hu:0 ≤ u)(hC:0≤C)(d k n:ℕ)(hk:n+HueS s≤k):
    ∃ c:ℝ,0≤c ∧ ∀ (t:Side)(E: Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure](L:Law E) (Ω:Row I I), Ω.strip α u→∀ (S: Story I)(c':ℝ)(x:deck I t)(Z:E→L[ℝ] deck I t)(j:Site t),Ribbon S Ω Z L x j k C c'→∀ w, weightsB S k w→∀ P:Curtain I,∀ v:ℝ,Volume P d k v→ let Q:=rootCush S Ω s d P; Volume Q (d+p.val) k (c*v*Visit w s) ∧ Mold (Tap μ L (Char.Sketch S c' x Z) (Char.Ωx d P Z x j) s) (Flair Q (d+p.val) x j) (c*v*Visit w s * (1+‖x‖)^(extendK d p)) t n:=by
         classical
         choose D hd H using fun i=> canvasR (I:=I) p s h i k n α u C hk hα hu hC; let a:= range (d+1); refine ⟨∑ i∈a,D i, Finset.sum_nonneg (fun i _=> hd i),?_⟩; intro t E _ _ _ _ _ μ _ L Ω hΩ S z x Z j hR w hW P v hp Q
         let U(i:ℕ):= Canvas S Ω s i (P i); let T(i):=flash (P i) Z x j; let V:=Visit w s; let D'(i):=D i*v*V; let M:=Tap μ L (Char.Sketch S z x Z); have hS(i):= H i _ μ L Ω hΩ t S x z Z j hR w hW (P i) v (hp.2 i)
         have hQ(i)(h:i∈a): Volume (U i) (d+p.val) k (D' i):=(hS i).1.raise _ (by change i∈Finset.range _ at h; rw [mem_range] at h; omega) le_rfl
         constructor
         · have hh:= Volume.sum U D' a hQ; rw [Finset.sum_mul, Finset.sum_mul];exact hh
         rw [show Q=∑ i∈a,U i from rfl, flairS (d+p.val) x j U fun i hi=>(hQ _ hi).bound _, cells, prices μ L (Char.Sketch S z x Z) s (branches sizes (fun _=>0) _ x x Z s) a (fun i=>flash (P i) Z x j) (fun i _=>flashB _ _ _ _ (hp.2 i))]
         have hc: 0 ≤ v:= Sack.coins (hp.2 0); have hY:0 ≤ V:=Visit0 (covers hW); let f(i):=Flair (U i) (d+p.val) x j; have he(i)(hi:i∈a): Mold (M (T i) s) (f i) (D' i*(1+‖x‖)^extendK d p) t n:=by
              have hx:i ≤ d:= Nat.le_of_lt_succ (mem_range.mp hi); unfold f; rw [← Volume.wax (U i) (hS i).1 (d+p.val) (Nat.add_le_add_right hx _)]; exact le_trans (hS i).2 (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by simp) (Nat.add_le_add_right (Nat.add_le_add_right hx _) _)) (show 0 ≤ D i*v*Visit w s from mul_nonneg (mul_nonneg (hd i) hc) hY))
         apply (moldSum he).trans_eq; unfold D' V; simp_rw [Finset.sum_mul]
end YM.OPE.Libra.Char
