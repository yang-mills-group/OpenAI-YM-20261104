import YM.Pert.Kinetic.Curl
import YM.Work.F03.Transport
/-! Absolute path-row bounds with one true wave derivative. -/
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff
variable {n : Side} {G : Gauge} {m : ℝ}
structure Slow (a : fieldDir G n 1) (m : ℝ) : Prop where
   rate : 0 ≤ m
   curl : ∀ x : Face (Per n), ‖faceCurl x a‖ ≤ m
   varies (x : Site n) (s : Slot) : ‖faceCurl (slotFace s x) a-faceCurl (x,s.plaq) a‖ ≤ s.length*m^2
lemma wave_slow {c : G.Color} (hc : ‖c‖=1) (b : Bool) (hn : 4 ≤ n.val) (i j : Axis) : Slow (n:=n) (lift1 (wave c b i j)) (Full.mesh n) := ⟨Full.mesh_pos.le,fun x=>curl_le c hc b hn x i j,fun x s=>curl_step c hc b hn x s i j⟩
variable {p : Clip} {σ C Λ : ℝ} {R : PathData G} (hb : R.Bounds p σ C Λ) {a : fieldDir G n 1} (h : Slow a m) (x : Face (Per n))
lemma moment_cost (he : 0<σ) (s : ℕ) : (s:ℝ) ≤ Real.exp (σ*s)/σ := by have hl := Real.add_one_le_exp (σ*s); apply (le_div_iff₀ he).2; linarith

def holdRow : G.Color := ∑' i, (R.row x.2 i).1 • faceCurl (x.1,(R.row x.2 i).2.plaq) a

def rowCost (σ C:ℝ) := C^2*σ⁻¹
include hb h
private def bill(i : ℕ) := |(R.row x.2 i).1| * Real.exp (σ * (R.row x.2 i).2.length)
omit h in
private lemma rent(i) : |(R.row x.2 i).1| ≤ bill (R:=R) (σ:=σ) x i := le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by exact mul_nonneg hb.width.le (by positivity)))

private lemma approx_summable : Summable (fun i=> (R.row x.2 i).1 • faceCurl (x.1,(R.row x.2 i).2.plaq) a) := by
   refine ((hb.rows x.2).2.1.mul_right m).of_norm_bounded fun i=>by
      rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul (rent hb ..) (h.curl _) (norm_nonneg _) (by change 0≤ _*_; positivity) -- hb ...

lemma hold_form : holdRow (a:=a) (R:=R) x = ∑ y:PlaqAxes,R.symbol0 x.2 y • faceCurl (x.1,y) a := by
   unfold holdRow PathData.symbol0
   simp_rw [←(hb.symTerms x.2 _).tsum_smul_const]
   rw [← Summable.tsum_finsetSum (fun y _=> (hb.symTerms x.2 y).smul_const _)]
   apply tsum_congr; intro i
   simp_rw [ite_smul]; rw [Finset.sum_eq_single ((R.row x.2 i).2.plaq)] <;> simp_all [eq_comm]

lemma holds_bound : ‖holdRow (a:=a) (R:=R) x‖ ≤ C*m := by
   unfold holdRow; refine (norm_tsum_le_tsum_norm (approx_summable hb h x).norm).trans ?_
   apply ((approx_summable hb h x).norm.tsum_le_tsum (g:=fun i=>bill (R:=R) (σ:=σ) x i*m) (fun i=>by
       rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul (rent hb ..) (h.curl _) (norm_nonneg _) (by unfold bill; positivity)) (by exact ((hb.rows x.2).2.1.mul_right m))).trans ?_
   rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (hb.rows _).2.2 h.rate
lemma true_bound : ‖ellLine R x a‖ ≤ C*m := by
   unfold ellLine; refine (norm_tsum_le_tsum_norm (ellLine_summable R hb x a).norm).trans ?_
   apply ((ellLine_summable R hb x a).norm.tsum_le_tsum (g:=fun i=>bill (R:=R) (σ:=σ) x i*m) (fun i=>by
       rw [norm_smul,Real.norm_eq_abs]; exact mul_le_mul (rent hb ..) (h.curl _) (norm_nonneg _) (by unfold bill; positivity)) (by exact ((hb.rows x.2).2.1.mul_right m))).trans ?_
   rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (hb.rows _).2.2 h.rate
lemma holds_tilt : ‖ellLine R x a - holdRow (a:=a) (R:=R) x‖ ≤ C/σ * m^2 := by
   unfold ellLine holdRow
   rw [←(ellLine_summable R hb x a).tsum_sub (approx_summable hb h _)]
   have he : Summable (fun i=>bill (R:=R) (σ:=σ) x i * (1/σ * m^2)) := ((hb.rows x.2).2.1.mul_right _)
   refine (norm_tsum_le_tsum_norm ?_).trans ?_
   · exact ((ellLine_summable R hb x a).sub (approx_summable hb h _)).norm
   have hs(i): ‖(R.row x.2 i).1 • faceCurl (slotFace (R.row x.2 i).2 x.1) a - (R.row x.2 i).1 • faceCurl (x.1,(R.row x.2 i).2.plaq) a‖ ≤ bill (R:=R) (σ:=σ) x i * (1/σ*m^2) := by
      rw [←smul_sub, norm_smul,Real.norm_eq_abs]
      refine (mul_le_mul_of_nonneg_left ((h.varies ..).trans (mul_le_mul_of_nonneg_right (moment_cost hb.width _) (by positivity))) (abs_nonneg _)).trans_eq ?_
      unfold bill; ring
   apply (((ellLine_summable R hb x a).sub (approx_summable hb h _)).norm.tsum_le_tsum (g:=fun i=>bill (R:=R) (σ:=σ) x i * (1/σ*m^2)) hs he).trans ?_
   rw [tsum_mul_right]; rw [div_mul_eq_mul_div,←mul_div_assoc]
   have hh := hb.width
   convert mul_le_mul_of_nonneg_right ((hb.rows x.2).2.2) (show 0≤(1/σ*m^2) from by positivity) using 1 <;> first | unfold bill; ring | ring

end YM.Pert.Kinetic
