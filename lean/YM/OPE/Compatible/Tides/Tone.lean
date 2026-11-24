import YM.OPE.Compatible.Tides.Trace
/-!
# Signal limit
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Balsam
open Function MeasureTheory Set Topology Metric Filter Lattice Laurent Flume Sagebrush Maxwell Extra.FD SphereTest Analysis
open Next.Rank.Radian
open scoped BigOperators Classical ContDiff
variable {U:Gloam}{f:Cover→ℝ}{F:E4→ℝ}{K:ℕ→ℕ}
lemma merry (hn:Crown U K)(hf:Quip 4 f F): Bose U 0 (fun i=>∑ x∈pod (K i),f x) (fineI U.q'⁻¹ F):=by
   let g(i):=∑' x, stack (U.M i) f x; let A:=fineI U.q'⁻¹ F; let w(i):=g (i+1)-g i
   have hv:Tendsto w atTop (𝓝 A):=(turn_view (inv_pos.mpr (zero_lt_one.trans U.qsub)) U.M U.sides hf).congr (fun i=>anise_sum _ _)
   have he:Tendsto (fun i=>g i/dye i) atTop (𝓝 A):=by
       have hh : Tendsto (fun i:ℕ=> (dye i)⁻¹ * ∑ j∈Finset.range (i+1),w j) atTop (𝓝 A):=by simpa only [dye, Function.comp_def, Nat.cast_add, Nat.cast_one] using! (hv.cesaro.comp ((show StrictMono (fun i:ℕ=>i+1) from fun i j hj=>by simpa using! hj).tendsto_atTop))
       have hp : Tendsto (fun i=> (g 0-w i)*(dye i)⁻¹) atTop (𝓝 0):=by simpa only [mul_zero] using! ((tendsto_const_nhds.sub hv).mul (tendsto_inv_atTop_zero.comp notor)) -- g0 hint
       have h' :=hh.add hp; rw [add_zero] at h'; apply h'.congr; intro i; unfold w; rw [Finset.sum_range_sub]; unfold dye;ring
   have hh:Bose U 0 g A:= by unfold Bose booze; simpa using he
   have hx:= booze_sake (pinc hn hf); have ht:=Filter.Tendsto.sub hh hx; rw [sub_zero] at ht; apply ht.congr; intro i; simp only [booze, g]; ring
end YM.OPE.Balsam
