import YM.OPE.Compatible.Chain.Gym
/-!
# Local covariance estimates uniformly. Self caps horizon
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Terp
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Matrix Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Flume.Script Finset Metric
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent Further.FreeCovariance.KP GaussianScore Work.F06 Work.F08
variable {C:KernelChoices}{r:ℕ}{J:Type}[Fintype J]
nonrec def swimming (C:KernelChoices)(h:4≤r)(v:Train r)(p:J→Edge Cover) (y w:Keys G J):ℝ:=∑ j:J,∑ i:G.ColorIndex,∑ l:J,∑ k:G.ColorIndex, y j i*w l k*horizon v C h i k (p j) (p l)
def tick4 (n:ℕ): Side:= ⟨2*(n+1),by omega⟩
lemma ticked (n:ℕ): Even (tick4 n).val:= ⟨n+1,by unfold tick4; dsimp; omega⟩
abbrev cosy (p:J→Edge Cover)(i:ℕ) (w:Keys G J): Dual' (Keys G (Limb (ticked i))):=pointS (ticked i) (fun j=>warpAt 0 (p j)) w
lemma ticklife: Tendsto (fun i=>(tick4 i).val) atTop atTop:=by
     apply Filter.tendsto_atTop.2; intro i; filter_upwards [eventually_ge_atTop i] with x hx; change i ≤ 2*(x+1);omega
lemma core_cost (v:Train r)(h:4≤r)(w w':Keys G J)(p:J→Edge Cover)(H:Even n.val)(u:Site n): (boost H v h C).wick (pointS H (warpAt u ∘p) w) (pointS H (warpAt u ∘p) w')=∑ j:J, ∑ i:G.ColorIndex,∑ x:J, ∑ a:G.ColorIndex, w j i*w' x a*boostJet H h v C i a (warpAt u (p j)) (warpAt u (p x)) := by
      unfold Law.wick pointS; simp only [map_sum, map_smul,LinearMap.sum_apply,LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]; simp_rw [mul_assoc];rfl
lemma floats (v:Train r)(h:4≤r)(w w':Keys G J)(p:J→Edge Cover): Tendsto (fun i:ℕ=> (boost (ticked i) v h C).wick (cosy p i w) (cosy p i w')) atTop (𝓝 (swimming C h v p w w')) :=by
      change Tendsto (fun i=> (boost (ticked i) _ _ _).wick (pointS _ (warpAt 0 ∘ p) _) (pointS _ (warpAt 0 ∘ p) _)) _ _; simp_rw [core_cost]; unfold swimming; refine tendsto_finsetSum univ fun j _=> tendsto_finsetSum univ fun a _=> tendsto_finsetSum univ fun i _=> tendsto_finsetSum univ fun t _=>?_ ; exact (pays (fun _=>0) ticked ticklife h v a t (p j) (p i)).const_mul _
lemma swims (C:KernelChoices)(h:4≤r)(G:Gauge):∃ a>0,∀ v:Train r,∀ (p:J→Edge Cover), Injective p→∀ w:Keys G J, a*picture w ≤ swimming C h v p w w := by
      obtain ⟨B,hb,H⟩:= boostUpper h (C:=C) (G:=G); refine ⟨B⁻¹,inv_pos.mpr hb,fun v p hp w=>?_⟩; refine ge_of_tendsto (floats v h w w p) ?_; filter_upwards [radIn (fun _=>0) ticked ticklife _ hp] with i hi; exact ascent (ticked i) v h _ w hi hb (H v _ _) -- H inference
lemma watery (v:Train r)(h:4≤r)(w w':Keys G J)(p:J→Edge Cover): swimming C h v p w w'= swimming C h v p w' w:= by
      have hh {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](R:Law E)(u v:Dual' E): R.wick u v=R.wick v u:=by
          unfold Law.wick; nth_rw 1 [← R.applies v]; nth_rw 2 [← R.applies u]; apply R.turns
      exact tendsto_nhds_unique (floats v h w w' p) ((floats v h w' w p).congr fun _=>hh ..)
end YM.OPE.Cascade.Terp
