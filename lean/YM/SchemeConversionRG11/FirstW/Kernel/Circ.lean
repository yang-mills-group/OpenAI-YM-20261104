import YM.SchemeConversionRG11.FirstW.Kernel.Diff
import YM.Pert.Fourier.Return
/-! Massless torus inverse uniform bound (finite order differentiated), includes origin.
Reuse proved low/oscillatory-high split with DISPLACEMENT-dependent length. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Filter Function Lattice Pert Pert.Align Topology
variable {n : Side} {s h : ℝ}
def linGreen (n : Side) (x : Site n) : ℝ := (Full.toroid x).re
lemma combine_green (D : List Axis) : combine D (Full.toroid (n:=n)) = fun x=>∑ p : Site n, Full.char p x *(Full.topWeight n p*Band.claw D p) := by
  induction D with
  | nil=> ext1 x; unfold Full.toroid; simp [combine,Band.claw,mul_comm]
  | cons a D ih=> rw [combine,ih]; ext1 x; unfold up; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun p _=>by rw [Full.char_add,Band.claw,Band.claw]; simp only [List.map_cons,List.prod_cons]; ring)
lemma lin_scalar (D : List Axis) (s : ℝ) (x : Site n) : (s^(D.length+2))⁻¹ * combine D (linGreen n) x = (Band.joint s D x).re := by
  change _ * combine D (Complex.reLm.toAddMonoidHom ∘ Full.toroid) x = _
  rw [show combine D _ x = _ from congrFun (combine_map D Complex.reLm.toAddMonoidHom (@Full.toroid n)) x, combine_green, Band.joint]
  have he : ((s:ℂ)^(-(D.length+2:ℤ))) = (↑((s^(D.length+2:ℕ))⁻¹:ℝ):ℂ) := by rw [zpow_neg];norm_cast
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero];rfl
variable (T : Itinerary)
lemma fixed_lin (p : Cover) (D : List Axis) : Tendsto (fun i=>combine D (linGreen (T.period i)) (wrap (T.period i) p)) atTop (𝓝 (combine D Cellular.coverLine p)) := by
  induction D generalizing p with
  | nil=>
    have H := (Cellular.strike_two T.period T.gap T.positive T.even_at T.huge T.cutoff 0 p).add (tendsto_const_nhds (x:=Cellular.coverLine p))
    simp only [Nat.cast_zero,neg_zero,zpow_zero,mul_one,sub_add_cancel,zero_add] at H; exact H
  | cons a d ih=> simp only [combine,up]; apply ((ih (p+step a)).sub (ih p)).congr (fun i=>by rw [map_add,wrap_step])
lemma scaled_lin (D : List Axis) : ∀ s > 0, ∃ C > 0, ∀ (n : Side) (x : Site n) (h : ℝ), 0<h → h*s ≤ 1/2 → Full.mesh n * ((D.length+4:ℕ):ℝ) ≤ h*s → (1:ℝ)/2 ≤ ‖Full.incVec h (lift x)‖ → ‖(h^(D.length+2))⁻¹ * combine D (linGreen n) x‖ ≤ C := by
  intro s hs
  obtain ⟨B,hp,H⟩ := Band.upper_tail D (1/2) (by norm_num)
  refine ⟨B/s + Band.purse*s^(D.length+2),by unfold Band.purse;positivity,fun n x h hh hv he hx=>?_⟩
  rw [lin_scalar]
  apply le_trans (Complex.abs_re_le_norm ..)
  nth_rw 1 [← sub_add_cancel (Band.joint h D x) (Band.piece h s D x)]
  exact (norm_add_le ..).trans (add_le_add (H hh hs hv he x hx) (Band.lower _ _ hs hh (by linarith) x D))
-- small region fixed lattice units by FCC quadrature; macroscopic still with uniform differentiated decay here
lemma tor_decay (D : List Axis) : ∃ C>0,∀ᶠ i in atTop, ∀ x : Site (T.period i), (cy x)^(D.length+2) * ‖combine D (linGreen (T.period i)) x‖ ≤ C := by
  let s := (2*Real.pi)*((D.length+4:ℕ):ℝ)*2+1
  have hs : 1≤s := by unfold s; exact le_add_of_nonneg_left (by positivity)
  obtain ⟨C,hC,H⟩ := scaled_lin D s (lt_of_lt_of_le (by norm_num) hs)
  obtain ⟨k,hk⟩ := exists_nat_gt (2*s)
  let K (p:Cover) := (stepY p)^(D.length+2)*(‖combine D Cellular.coverLine p‖+1)
  have hK p : 0 ≤ K p := mul_nonneg (pow_nonneg (zero_le_one.trans (unit_stepY p)) _) (by positivity)
  refine ⟨C+∑ p∈boxN k,K p, add_pos_of_pos_of_nonneg hC (Finset.sum_nonneg fun p _=>hK p),?_⟩
  have ev : ∀ᶠ i in atTop,∀ p∈boxN k, (stepY p)^(D.length+2)* ‖combine D (linGreen (T.period i)) (wrap (T.period i) p)‖ ≤ K p := by
    rw [eventually_all_finset]
    intro p _
    exact ((fixed_lin T p D).norm.eventually (ge_mem_nhds (lt_add_one _))).mono fun i hi => mul_le_mul_of_nonneg_left hi (pow_nonneg (zero_le_one.trans (unit_stepY p)) _)
  refine ev.mono fun i hi x=> ?_
  let Y:=cy x
  by_cases h : Y<2*s
  · have hh : lift x ∈ boxN k := by
      rw [mem_boxN]; have hy : ((yard (lift x):ℕ):ℝ) ≤ k := by dsimp only [Y,cy,stepY] at h; linarith
      exact_mod_cast hy
    have e := (hi (lift x) hh).trans (Finset.single_le_sum (fun p _=>hK p) hh); rw [wrap_lift] at e
    exact e.trans (le_add_of_nonneg_left hC.le)
  have hy : 2*s ≤ Y := not_lt.mp h
  have hy1 : 1≤Y := unit_cy _; have hy0 : 0<Y := zero_lt_one.trans_le hy1
  have hm : Full.mesh (T.period i)*((D.length+4:ℕ):ℝ) ≤ Y⁻¹ * s := by
    let n:= T.period i
    rw [inv_mul_eq_div,le_div_iff₀ hy0]
    apply le_trans (mul_le_mul_of_nonneg_left (done_cy x) (by unfold Full.mesh; positivity))
    change 2*Real.pi/(n.val:ℝ)*_*(2*(n.val:ℝ)) ≤ _
    unfold s; have hv : 0 < (n.val:ℝ) := by positivity
    field_simp; linarith
  have he := H _ x Y⁻¹ (inv_pos.mpr hy0) (by rw [inv_mul_eq_div, div_le_iff₀ hy0]; linarith) hm (le_trans (show 1/2 ≤ Y⁻¹*(Y-1) from by rw [inv_mul_eq_div, le_div_iff₀ hy0]; linarith) (low_at x (by positivity)))
  rw [inv_pow,inv_inv,norm_mul,Real.norm_of_nonneg (pow_nonneg hy0.le _)] at he
  exact he.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun p _=>hK p))
lemma tor_limit (D : List Axis) {v : E4} (hv : v ≠ 0) (o : ∀ i, Site (T.period i)) (ho : Tendsto (fun i=> Full.incVec (T.gap i) (lift (o i))) atTop (𝓝 v)) : Tendsto (fun i=>(T.gap i^(D.length+2))⁻¹ * combine D (linGreen (T.period i)) (o i)) atTop (𝓝 ((Band.casual D v).re)) := by
  simp_rw [lin_scalar]
  exact Complex.continuous_re.continuousAt.tendsto.comp (Band.joint_casual _ _ _ _ o hv T.grid_eq T.positive T.clears T.cutoff ho)
end YM.RG11.FirstW
