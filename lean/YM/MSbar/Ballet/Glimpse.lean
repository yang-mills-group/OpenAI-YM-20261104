import YM.MSbar.Geneva.Film
import YM.MSbar.Alto.Suez
import YM.Extra.ITERATION_NO_LOSS.Gates
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
noncomputable def stamping (Z:Fees)(s:ℕ) : StageCost := ⟨s,Z.axis,Z.tilt,Z.pre,Z.shape,Z.c1,Z.c2,Z.c3,Z.c4⟩
-- before block choice uses Fields 1-3 of stamp. widths from Census. independent Z farm.
noncomputable def mortgage (M:StageCost)(P:Patch)(m:ℕ)(A:ℝ):Prop :=Geneva.Ready P M m A ∧ Cane.value 0 M.C M.A M.E M.s M.sway/P.L.val < 1/128
variable (i m s j p:ℕ)(V:StageCost)(a:ℝ)
noncomputable def climbV (V:StageCost) (i n:ℕ):ℝ:= let C:= Cane.value 0 V.C V.A V.E V.s V.sway; 5*4^(i+1)*((n:ℝ)^4*(C/n)^(i+1))
lemma height (h:4 ≤ i) : Tendsto (climbV V i) atTop (𝓝 0):=by
    let C:= Cane.value 0 V.C V.A V.E V.s V.sway; let A:=5*4^(i+1)*C^(i+1); let K:=i+1-4
    have ht:Tendsto (fun n:ℕ=> A/(n:ℝ)^K) atTop (𝓝 0):=tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by unfold K; omega)).comp tendsto_natCast_atTop_atTop)
    refine ht.congr' ?_; filter_upwards [eventually_gt_atTop 0] with n hn; have hu:(n:ℝ)≠0:=by positivity
    have he : (n:ℝ)^(i+1)= (n:ℝ)^4 * (n:ℝ)^K:=by nth_rw 1 [show i+1=4+K from (by unfold K;omega)]; rw [pow_add]
    unfold climbV A C; dsimp only; rw [div_pow,he]; field_simp
noncomputable def plotV (V:StageCost) (i n:ℕ):ℝ:= let l:ℝ:=n; 4^(i+1)* (l^4*(Cane.value 0 V.C V.A V.E V.s V.sway/l)*(2*(Measuring.feed 0 V.A V.E V.C V.s V.sway i/l^i)*(4/l)^(4-i))*5)
lemma depth (h:i∈Finset.Icc 1 3) : Tendsto (plotV V i) atTop (𝓝 0):=by
    have hx:=Finset.mem_Icc.mp h
    let u:=Cane.value 0 V.C V.A V.E V.s V.sway; let v:= Measuring.feed 0 V.A V.E V.C V.s V.sway i
    let C:= (4:ℝ)^(i+1)*(u*(2*v*4^(4-i))*5)
    have ht:Tendsto (fun n:ℕ=>C/(n:ℝ)) atTop (𝓝 0):=tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    refine ht.congr' ?_; filter_upwards [eventually_gt_atTop 0] with n hn; have hu:(n:ℝ)≠0:=(by positivity); unfold plotV C u v; dsimp only; rcases (show i=1∨i=2∨i=3 from (by omega)) with rfl|rfl|rfl <;> norm_num only [Nat.reduceSub,Nat.reduceAdd] <;> field_simp <;> ring
end YM.MSbar.Ballet
