import YM.Pert.First.OneArray
import YM.Pert.Warp.Initial
/-! Breaking first-order curvature-power marks into Gaussian polynomials of the external lines times one varied factor, with Wick subtraction still on the remaining slots. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Pert.First
open Filter MeasureTheory Lattice Function Full Orb Warp MvPolynomial
open scoped Topology Classical
variable {G : Gauge} {N : Side} {d r : ℕ} {I : Type} [Fintype I] [DecidableEq I]
variable (h : ℝ) (o : Grid N r) (tag : I→Fin r) (code : I→CosKey G d) (s : Finset I)
local notation "fmark" => root tag code
local notation "finit" => tube o h (fun _=>d) ∘ fmark

def painting (x : Coords G N) (i : Fin r) (a : Aux G d) (j : I) := fullPair h (o i) x (code j) a where -- replace
  fullPair (h' : ℝ) (v : Site N) (x' : Coords G N) (z : CosKey G d) (a' : Aux G d) := PowerSeries.constantCoeff (pairEval h' v x' a' (X z.val))

theorem painting_tame (x : Coords G N) (i) (b : Finset I) : Orb.Tame (fun a : Aux G d=> ∏ j∈b, painting h o code x i a j) := by
  apply prod_tame; intro j _; unfold painting painting.fullPair
  simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using (Full.leg_ready (d:=d) h (o i) x (X (code j).val) 0)
lemma lead_zero_mark (x : Coords G N) (i : Fin r) : finit s x i = ∫ a : Aux G d, ∏ j∈s with tag j = i, painting h o code x i a j ∂auxLaw G d h := by
  unfold comp; rw [tube, lead, auxiliary,avg,← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_mk]
  congr 1; funext u; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply];unfold root pairEval painting; simp only [map_prod]; rfl

def linkChange (x : Coords G N) (j) := first (Bare.seriesLex h (o (tag j)) x (code j).val)
lemma brush_tame (j) : Tame (fun x=>linkChange h o tag code x j) := by
  unfold linkChange first Bare.seriesLex; simp only [PowerSeries.coeff_mk]; exact tame_scaleJet _ _
lemma pair_singleton (x : Coords G N) (i : Fin r) (j) (u : Aux G d) : first (pairEval h (o i) x u (X (code j).val)) = first (Bare.seriesLex h (o i) x (code j).val) := by simp [pairEval,first,PowerSeries.coeff_C]
lemma painting_first (x : Coords G N) (i : Fin r) (u : Aux G d): first (pairEval h (o i) x u (fmark s i)) = ∑ j∈s with tag j=i, linkChange h o tag code x j * ∏ b∈s.erase j with tag b=i, painting h o code x i u b := by
  unfold root pairEval
  rw [map_prod]; change (first _ : ℂ)=_;rw [first_product]
  refine Finset.sum_congr rfl (fun j hj=> congr_arg₂ (· * ·) ?_ (Finset.prod_congr ?_ (fun k _=> rfl))) -- ordering of goals check
  · dsimp only [linkChange]; change first (pairEval _ _ _ _ _)=_;rw [pair_singleton,(Finset.mem_filter.mp hj).2]
  · rw [Finset.filter_erase (p:=fun b=>tag b=i)]
lemma dry_mark (x : Coords G N) (i : Fin r) : dry o h (fun _=>d) (fmark s) x i = ∑ j∈s with tag j=i, linkChange h o tag code x j * finit (s.erase j) x i := by
  unfold dry first
  rw [auxiliary, avg,PowerSeries.coeff_mk]; simp only [← show ∀ v, first v = PowerSeries.coeff 1 (v:PowerSeries ℂ) from fun v=>rfl]
  simp only [painting_first];rw [integral_finsetSum]
  · simp only [integral_const_mul,lead_zero_mark]
  exact fun j hj=> (bareTame_integrable h (painting_tame h o code x i _)).const_mul _
lemma tube_erase (x : Coords G N) (j : I) (i : Fin r) (hji : tag j ≠ i) : finit s x i = finit (s.erase j) x i := by
  rw [lead_zero_mark,lead_zero_mark]; congr 1;funext x; rw [Finset.filter_erase,Finset.erase_eq_self.mpr]; intro hj; exact hji (Finset.mem_filter.mp hj).2

lemma varied_total (x : Coords G N) : ∑ i : Fin r, varied Finset.univ o h (fun _=>d) (fmark s) x i = ∑ j∈s, linkChange h o tag code x j * line Finset.univ o h (fun _=>d) (fmark (s.erase j)) x := by
  rw [← Finset.sum_fiberwise s tag]; apply Finset.sum_congr rfl; intro i _
  unfold varied; rw [dry_mark,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro j hj
  have he : tag j=i := (Finset.mem_filter.mp hj).2
  rw [line, line, ←Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]; rw [mul_right_comm (linkChange h o tag code x j), ← mul_assoc]; congr 2
  exact Finset.prod_congr rfl fun b hb => tube_erase h o tag code s x j b (by simpa only [he] using (Finset.ne_of_mem_erase hb).symm)

lemma season_applies : ∑ i : Fin r, ∫ x, varied Finset.univ o h (fun _=>d) (fmark s) x i ∂data G N =
     ∑ j∈s, ∫ x, linkChange h o tag code x j * line Finset.univ o h (fun _=>d) (fmark (s.erase j)) x ∂data G N := by
  rw [←integral_finsetSum,←integral_finsetSum]; congr 2; exact funext (varied_total h o tag code s)
  exact fun _ _=> (Tame.mul (brush_tame ..) (line_tame ..)).integrable
  exact fun _ _=> (varied_tame ..).integrable
end YM.Pert.First
