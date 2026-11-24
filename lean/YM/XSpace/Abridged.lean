import YM.XSpace.Garment
import YM.XSpace.Reversal
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio

/-!
# Trees at order one: no zero Hessian, Jacobian term zero as literal Haar

Push each poly through `T.Key` linear charges. No forward claims yet about using a
covariance that isn't the tree's (arbitrary changes require Ward etc).
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Chart2
open CubicMatch Filter Lattice RG Next.Rank.Normal Contraction Wilson Bare Finsupp
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {R : Period} (T : R.Tree)
abbrev Roller (R:Period) (G:Gauge) := Rollers R.Bonds G

def stub (u:T.Field G) (i:Roller R G):ℝ := T.covering u i.1 i.2

def earmark (i: Roller R G):T.Key G →₀ ℂ:= ∑ j:T.Key G, Finsupp.single j (stub T (T.basis G j) i:ℂ)
lemma earmark_reads (u:T.Field G) (i:Roller R G): reads (earmark T) (fun j=> ((T.basis G).repr u j:ℂ)) i= numbers (T.covering u) i:=by
  simp only [reads,earmark,_root_.map_sum,linearCombination_single,smul_eq_mul]
  conv_rhs=> unfold numbers; rw [← (T.basis G).sum_repr u,map_sum]; simp only [Finset.sum_apply,WithLp.ofLp_sum, map_smul,Pi.smul_apply,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_sum,Complex.ofReal_mul]
  exact Finset.sum_congr rfl fun _ _=>mul_comm ..
abbrev tea := exchange (earmark T (G:=G))
lemma log_path (u:T.Field G) (P : St (Per R.side) G): Taylor.evalAt (T.basis G) u (tea T P)=pit (T.covering u) P:=by
  change MvPolynomial.aeval _ (exchange _ P)=_; rw [reads_val]; unfold pit; congr 2; exact funext (earmark_reads T u)

def treeCov (G : Gauge): Cov (Roller R G):= scope (earmark T) (Q T G)
lemma transfers (P : St (Per R.side) G): blend (Q T G) 0 (tea T P)=blend (treeCov T G) 0 P:=by rw [tea, wets, show reads (earmark T (G:=G)) 0=0 from funext fun i=> by simp [reads]]; rfl

lemma relative_sym (G:Gauge): ∀ᶠ x:T.Field G in 𝓝 0, relative T (-x) = relative T x:=by
  have h (i : T.Free) : ∀ᶠ x:T.Field G in 𝓝 0, (chart G).J (-(x i)) = (chart G).J (x i):=by
    filter_upwards [((continuous_apply i).tendsto (0:T.Field G)).eventually (Metric.ball_mem_nhds _ (chart_ratio G).patch)] with x hx
    exact (Next.SectorChange.ratio_even (chart_ratio G) hx).symm
  filter_upwards [eventually_all.mpr h] with x hx; simp [relative,hx]
lemma no_haar1 (G:Gauge): PowerSeries.coeff 1 (haar T G)=0:= Taylor.from_real (T.basis G) _ _ (fun x=>by rw [map_zero (Taylor.evalAt _ _),haar_coeff, ← along x _ (relative_smooth T G),iteratedDeriv_one,(Next.SectorChange.still_even ((relative_smooth T G).differentiableAt (by simp)) (relative_sym T G) x).deriv]; simp)

def cubic (R:Period) (G:Gauge): St (Per R.side) G:= (2:ℂ)⁻¹ • ∑ p : Face (Per R.side), V3 G p
lemma fits_tree (x:T.Field G) (e:R.Bonds): Fits (fun t:ℝ=> T.links (t • x) e) (native (T.covering x) e):= by
  simp_rw [T.links_apply,map_smul,Pi.smul_apply]; exact Fits.along_a _
lemma cubic_pays (x:T.Field G): pit (T.covering x) (cubic R G)= ↑(term 3 (fun t:ℝ => T.action (t • x))):=by
  let L (p:Face (Per R.side)) (t:ℝ):= G.price (faceValue (T.links (t • x)) p)
  have he (p : Face (Per R.side)): ContDiffAt ℝ ω (L p) 0:= Work.F03.price_smooth (carries_face (fun t:ℝ=> T.links (t • x)) _ (fits_tree T x) p).smooth
  let g (t:ℝ):= ∑ p, L p t; have h : ContDiffAt ℝ ω g 0:= ContDiffAt.sum (fun i (_:i∈Finset.univ)=> he i)
  rw [cubic,_root_.map_smul,_root_.map_sum]; simp_rw [price_at]
  have hi : term 3 (fun t:ℝ => T.action (t • x))= (∑ p,term 3 (L p))/2:=by
    let Q : ℝ→L[ℝ] ℝ:= (2:ℝ)⁻¹ • ContinuousLinearMap.id ℝ ℝ
    rw [show (fun t:ℝ => T.action (t • x))=(fun t=> Q (g t)) from funext fun t=> by change g t / 2 = (2:ℝ)⁻¹ * g t; rw [div_eq_inv_mul],
      term_linear _ (h.of_le le_top),show term 3 g=_ from term_sum (fun p (_:p∈Finset.univ)=> (he p).of_le (show ((3:ℕ):ℕ∞ω)≤ ω from le_top))]
    rw [div_eq_inv_mul]; rfl
  rw [hi]; simp_rw [show ∀ p,term 3 (L p)=diagnostic p (T.covering x) from fun p=> diagnostic_price p (fun t:ℝ => T.links (t • x)) (T.covering x) (fits_tree T x)]
  push_cast; ring

lemma weighed (G:Gauge): PowerSeries.coeff 1 (weight T G)= -tea T (cubic R G):=by
  rw [Bare.weight,PowerSeries.coeff_one_mul,no_haar1,zero_mul,zero_add,haar_initial,mul_one,exponential_formula]; norm_num [Finset.sum_range_succ]
  apply Taylor.from_real (T.basis G); intro x; rw [map_neg,log_path,cubic_pays,interaction_coeff _ _ (by norm_num),term,along x _ (T.continuousJet G)]; rfl
lemma no_vacuum1 (G:Gauge): PowerSeries.coeff 1 (vacuum T G)=0:=by
  have h:= congr_arg (PowerSeries.coeff 1) (reverse_diagrams T (1:Series T G)); rw [map_one, PowerSeries.coeff_rescale] at h
  change PowerSeries.coeff 1 (vacuum T G) = _ at h
  apply (mul_left_injective₀ (b:=(2:ℂ)) (by norm_num)); dsimp only; rw [zero_mul,mul_two]; conv_lhs=>arg 1; rw [h]; simp only [pow_one, neg_one_mul]; rw [← vacuum]
  exact neg_add_cancel _
lemma order1 (G:Gauge) (Y:Series T G) (A B:St (Per R.side) G) (ha:PowerSeries.constantCoeff Y=tea T A) (hb:PowerSeries.coeff 1 Y=tea T B): PowerSeries.coeff 1 (normalized T G Y)=blend (treeCov T G) 0 (B-cubic R G *A):=by
  have h:= congr_arg (PowerSeries.coeff 1) (normalize_denominator T G Y); rw [PowerSeries.coeff_one_mul,vacuum_start,mul_one,no_vacuum1,zero_mul, add_zero,diagram_coeff, PowerSeries.coeff_one_mul,weighed, weight_one,mul_one,ha,hb,neg_mul,add_comm,← sub_eq_add_neg,← map_mul, ← map_sub,transfers] at h; exact h
end YM.XSpace.Chart2
