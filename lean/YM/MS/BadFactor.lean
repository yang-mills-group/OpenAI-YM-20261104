import YM.MS.ChargeValue
/-! # The forbidden jet cannot survive the power-log bound. Charge is an
  ordinary example: its comparison at large R implies its first jets. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS
open Function Filter Set LogTime Real MeasureTheory
open scoped Topology ContDiff
open LogTime.IntervalFamily Plane Wire
variable {ι E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {R : IntervalFamily ι} {j : ℕ}
    {ζ : ℤ} {y : ℝ}
lemma zero_taylor (hi : ∀ i, R.window i = Ici (R.beg i)) (hh : weak ζ y j) {f : ι → ℝ → E→ F}
    (hd : Bound R.primary (here f) (fun i=> R.primary.length i ^ ζ * rate R y i)) (i:ι):
    Tendsto (fun t=> iteratedFDeriv ℝ j (f i t) 0) atTop (𝓝 0) := by
   obtain ⟨C,hC,b,H⟩:= hd.quoted j
   let K := C*R.logPart i^b
   let W := fun t=> K* LogTime.polyExp (-((ζ:ℝ)-y+j)) b t
   have hW : Tendsto W atTop (𝓝 0):= by simpa only [W,mul_zero] using (vanishes (show 0 < -((ζ:ℝ)-y+j) from neg_pos.mpr hh) b).const_mul K
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ?_ hW
   filter_upwards [eventually_ge_atTop (R.beg i)] with t0 ht
   let v:= R.choose i t0 (by rwa [hi]); apply (H v (0:E) trivial).trans
   change C * (R.logPart i*(1+t0)* R.primary.weight v (0:E))^b * ((R.primary.length v ^ ζ * _) * _ ) ≤ _
   rw [small_fact, Scale.weight_zero]; change C* (R.logPart i*(1+t0)*1)^b*((1 * _)*exp t0^j) ≤ W t0
   apply le_of_eq; unfold W K polyExp -- maybe pays hidden
   simp only [mul_one,neg_neg, add_mul, Real.exp_add,Real.exp_nat_mul,mul_pow, t,v,choose]; ring

lemma zero_charge (hi : ∀ i, R.window i= Ici (R.beg i)) {f g:E→F} (H : Like R.primary.full R.primary (rate R y) (fun _=>f) (fun _=>g) (fun i _=> R.primary.length i ^ ζ))
    (hh : weak ζ y j) [Nonempty ι] : iteratedFDeriv ℝ j f 0=iteratedFDeriv ℝ j g 0 := by
  obtain ⟨k⟩ := (inferInstance : Nonempty ι)
  have h:= zero_taylor hi hh (f:=fun _ _=> f-g) H.gain k
  have hp:=tendsto_nhds_unique (f:= fun (x:ℝ)=> iteratedFDeriv ℝ j (f-g) 0) tendsto_const_nhds h
  have hl : ContDiff ℝ ∞ f:= H.lat.smooth (R.start k); have hs : ContDiff ℝ ∞ g:= H.std.smooth (R.start k)
  exact sub_eq_zero.mp (by rwa [iteratedFDeriv_sub_apply (hl.contDiffAt.of_le (by exact_mod_cast le_top)) (hs.contDiffAt.of_le (by exact_mod_cast le_top))] at hp)
end YM.MS
