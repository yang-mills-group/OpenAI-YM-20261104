import YM.RG11Scheme.Mesh.Terrain
import YM.Pert.Fourier.Visits

/-! Quantitative toroid-vs-cover, retaining distance dependence for polynomial ranges. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11Scheme.Mesh
open Lattice Function Filter Set MeasureTheory Pert Pert.Full Pert.Cellular Metric
open scoped Topology BigOperators Classical
variable {n : Side}

def field (x:Site n) := (toroid x).re

theorem intercell {x:E4} (hn : Even n.val) (h : ∀ s : Axis,x s≠ -(1/2) ∧ x s ≠ (1/2)) (hp : x ∈ cells) : visit n x∈cells := by
    apply (cells_cube (visit n x)).mpr
    unfold visit; obtain ⟨p,hh⟩ := (marked_cell n hn h).mp hp;rw [←hh,visit_defensive]; apply moment_cube

lemma corner_bound (p : Cover) (u v : E4) : |clock p u-clock p v| ≤ 2*Band.turn*wide p*‖u-v‖ := by
    have he x k : corner x k=inner ℝ (row x) k := by unfold corner; simp_rw [PiLp.inner_apply]; refine Finset.sum_congr rfl fun i _ => ?_; rw [RCLike.inner_apply', row_axis]; simp
    unfold clock; simp_rw [he]
    let k := Band.turn
    have hl := Real.lipschitzWith_cos.dist_le_mul (inner ℝ (row p) (k • u)) (inner ℝ (row p) (k • v))
    simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hl
    apply hl.trans
    rw [←inner_sub_right, ← smul_sub]
    apply (abs_real_inner_le_norm ..).trans
    rw [norm_smul,Real.norm_of_nonneg (show 0≤Band.turn by positivity)]; grw [axis_elev]; unfold wide; ring_nf
    have hv : 0≤ k := by unfold k; positivity
    dsimp [k] at *; nlinarith [Real.pi_pos, mul_nonneg (show 0≤Band.turn by positivity) (norm_nonneg (u-v))]

lemma trace_zero (x:E4) : trace (0:Cover) x=(dtype x)⁻¹ := by simp [trace,clock,corner]

lemma tracing : ∃ A>0,∀ {r : ℝ}, 0<r → r≤1 → ∀ {n : Side}, 8*(n.val:ℝ)⁻¹ ≤ r → ∀ p x, x∈cells → visit n x∈cells → r<‖x‖ →
   ‖trace p (visit n x)-trace p x‖ ≤ A*wide p*(n.val:ℝ)⁻¹ /r^4 := by
    obtain ⟨B,hB,hb⟩ := linear_der (0:Cover)
    refine ⟨B+8*Band.turn,by positivity,?_⟩; intro r hr he n hn p x hx hy hw
    let y:=visit n x; let C:=(n.val:ℝ)⁻¹
    have hl:=corner_bound p y x
    have hp:=wide_one p
    have hm : |clock p y-clock p x| ≤ 2*Band.turn*wide p*(4*C) := hl.trans (mul_le_mul_of_nonneg_left (visit_eps n x) (by positivity))
    have hd : ‖trace (0:Cover) x‖ ≤ (r^4)⁻¹ := (inv_rate _ hx).trans (by gcongr; nlinarith only [hw,hr, he,show r^4=r^2*r^2 from by ring,pow_le_one₀ hr.le he (n:=2)])
    rw [show trace p (visit n x)-trace p x=(trace 0 y-trace 0 x)*clock p y+trace 0 x * (clock p y-clock p x) from by simp_rw [trace_zero,trace];ring]
    apply (norm_add_le ..).trans; simp only [norm_mul]
    apply (add_le_add (mul_le_mul (hb hr he hn hx hy hw) (clock_price p y) (abs_nonneg _) (by positivity)) (mul_le_mul hd hm (abs_nonneg _) (by positivity))).trans
    grw [mul_one]
    have hbx : B ≤ B*wide p:= le_mul_of_one_le_right hB hp
    dsimp [C]; rw [add_mul,add_mul,add_div]
    apply add_le_add (by gcongr) (le_of_eq (by ring))

lemma clearing : ∃ C≥0,∃ A≥0,∀ {n : Side}, Even n.val → ∀ {r : ℝ}, 0< r → r≤1 → 8*(n.val:ℝ)⁻¹ ≤ r → ∀ p,
       ‖field (wrap n p)-coverLine p‖ ≤ C*r^2 + A*wide p*(n.val:ℝ)⁻¹ / r^4 := by
   obtain ⟨A,hA,H⟩ := tracing
   let v:=A*volume.real cells
   have hp (x r) : 0 ≤ spike r x := indicator_nonneg (f:=fun x:E4=>(‖x‖^2)⁻¹) (fun a _=>by positivity) x
   refine ⟨26*∫ k,spike 1 k, by apply mul_nonneg (by positivity) <| integral_nonneg (hp · 1),v,(mul_nonneg hA.le ENNReal.toReal_nonneg),?_⟩
   intro n he r hr h1 hn p
   let D := A*wide p*(n.val:ℝ)⁻¹ / r^4
   have hD : 0 ≤ D := by unfold D; have := wide_pos p; positivity
   let F:=cells.indicator (fun _ => D)
   have hF : Integrable F volume := (integrable_indicator_iff cells_closed.measurableSet).2 (integrableOn_const cells_compact.measure_ne_top)
   unfold field; rw [weighted p n he,cover_interp,←integral_sub (integrate_visit n he (trace p)).1 (strike p n)]
   apply le_trans (norm_integral_le_of_norm_le (g:=fun x => 26*spike r x+F x) (((spike_int r).const_mul 26).add hF) ?_) (le_of_eq ?_)
   · filter_upwards [cell_AE] with x hx
     by_cases ht : x∈cells
     · have hv := intercell he hx ht
       unfold F; rw [indicator_of_mem ht,indicator_of_mem ht,indicator_of_mem ht]
       by_cases hh : ‖x‖ ≤ r
       · unfold spike; rw [indicator_of_mem (show x ∈ ball (0:E4) (2*r) by rw [mem_ball,dist_zero_right]; linarith)]
         exact (inv_visits p n x ht hv).trans (le_add_of_nonneg_right hD)
       exact (H hr h1 hn p x ht hv (lt_of_not_ge hh)).trans (le_add_of_nonneg_left (mul_nonneg (by positivity) (hp x r)))
     unfold F; rw [indicator_of_notMem ht,indicator_of_notMem ht,indicator_of_notMem ht,sub_self,norm_zero];have := hp x r;positivity
   rw [integral_add ((spike_int r).const_mul _) hF, integral_const_mul, spike_pos hr]
   unfold F; rw [integral_indicator cells_closed.measurableSet, setIntegral_const, smul_eq_mul]; unfold D v; ring

lemma upper : ∃ C>0,∀ n : Side,Even n.val → ∀ x:Site n, ‖field x‖ ≤ C := by
   have hp x r : 0 ≤ spike r x := indicator_nonneg (fun a (_:a∈ball (0:E4) (2*r))=>inv_nonneg.2 (sq_nonneg _)) x
   refine ⟨27*(∫ x,spike 2 x) + 1, ?_,?_⟩ -- parenthesize
   · have he : 0 ≤ ∫ x,spike 2 x:= integral_nonneg (hp · 2); linarith
   intro n he x; let p:=lift x
   change ‖(toroid x).re‖ ≤ _; rw [show x=wrap n p from (wrap_lift _).symm,weighted p n he]
   refine le_trans (norm_integral_le_of_norm_le (g:=fun k=>27*spike 2 k) ((spike_int 2).const_mul 27) ?_) ?_
   · filter_upwards [cell_AE] with k hk
     by_cases ht : k∈cells
     · rw [indicator_of_mem ht,spike,indicator_of_mem (show k∈ball (0:E4) (2*2) by rw [mem_ball,dist_zero_right]; linarith [cells_bd ht])]
       have h := inv_visits p n k ht (intercell he hk ht)
       calc _ ≤ ‖trace p (visit n k)-trace p k‖+‖trace p k‖ := by simpa using! norm_add_le (trace p (visit n k)-trace p k) (trace p k)
            _ ≤ _ := by linarith [inv_rate p ht]
     rw [indicator_of_notMem ht,norm_zero];have := hp k 2;positivity
   rw [integral_const_mul]; linarith
end YM.RG11Scheme.Mesh
