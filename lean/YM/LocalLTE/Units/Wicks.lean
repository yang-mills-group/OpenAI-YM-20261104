import YM.LocalLTE.Units.Cone
/-! Bill comparison trade from analytic height of real with value-only for approximation on true sunny.
 Poly carries complete support, not Healthy mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Cabana
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Frond Poll Coat SliceRows
open AbsoluteSums Animals PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard
open Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c:Side}(L:Side){η a q:ℝ}
-- x paid A cone. r usable thermal factor; ψ upper same. Eventually after L delays.
section
local notation "coneW" => (fun t:ℝ => Inset.cone a (betaF G t L))
local notation "U" => (fun t:ℝ => Inset.cone η (betaF G t L)) -- SHRINK η negative
lemma trading (H P:ℝ){M Y : ℝ→ℝ} {j i:ℕ} (hp : Rate G L P Y)(hM:Rate G L H M)(hi:j < i) (h: -(1/2:ℝ)<a) (h':2*a < -(1/2:ℝ)) (hη:η<0) : ∃ V:ℝ→ℝ, Rate G L (max (H+(η+a)*i) P + (a+(1/2-η))*j) V ∧ ∀ᶠ t in atTop,
    let r:=coneW t
    ∀ (c:Side)(B: BudgetPoint), B.threshold=Pressure.temp t → B.threshold ≤ 2*Pressure.fiery G t L → ∀ (Q:Directions G c →L[ℝ] Directions G c), (∀ x,‖Q x‖≤‖x‖) → ∀ (d:ℕ), d ≤ i→ ∀ (f:Directions G c→ℝ)(g:Pkt (Directions G c) d) (F:ℝ),0≤F→
      (∀ x,‖x‖< r→ FrameBox.Grove.soloV (Q x)∈ sunny B→ ContDiffAt ℝ (↑i) f x ∧ ‖iteratedFDeriv ℝ i f x‖≤ F*|M t| ∧ ‖f x-Cabana.actual g x‖ ≤ F*|Y t|) → ∀ x,‖x‖ < r→ FrameBox.Grove.soloV (Q x)∈ sunny B → Brush j (F*|V t|) r⁻¹ (f-Cabana.actual g) x :=by
  obtain ⟨b,C,hb,hC,hD⟩:= Cabana.edging G
  obtain ⟨K,hK,Hc⟩:= Cabana.resurrect i j hi
  let W t:=coneW t; let A t:=U t; let s t:= A t*(b*Frond.mist G L t); let p t:=2*(A t*W t)
  let V t:=K*(|Y t|+|M t| *p t^i)*(W t*(s t)⁻¹)^j
  have ha: Rate G L a W:= Rate.power; have h₁:Rate G L η A:= Rate.power
  refine ⟨V,?_,?_⟩
  · have hu : Rate G L (1/2-η) (fun t:ℝ=> (s t)⁻¹):=by
      have hy : Rate G L (-η) (fun t:ℝ=> (A t)⁻¹):= Rate.congr Rate.power (by filter_upwards [Delay.shift_pos G L] with x hx; exact (Real.rpow_neg hx.le η).symm)
      unfold s; simp_rw [_root_.mul_inv_rev,Frond.mist,inv_inv]; exact show Rate G L (1/2+-η) _ from ((Rate.power (G:=G) (L:=L) (a:=1/2)).mul_right b⁻¹).mul hy
    have hy {a:ℝ→ℝ}{j:ℝ}(h:Rate G L j a):Rate G L j (fun t=> |a t|):= h.compare (Eventually.of_forall (fun i=>(abs_abs _).le))
    exact ((((hy hp).weaken (le_max_right ..)).add (((hy hM).mul (((h₁.mul ha).mul_left 2).pow i)).weaken (le_max_left ..))).mul_left K).mul ((ha.mul hu).pow j)
  have hh : a<0:=by linarith
  have ht := contraction G L (a:= b*2) (b:=1) zero_lt_one Rate.flame h
  have hz := contraction G L (a:=C) (b:=1) zero_lt_one (ha.pow 2) (show a*2 < -(1/2:ℝ) by linarith)
  filter_upwards [Delay.shift_pos G L,h₁.below hη 1 zero_lt_one, Frond.softly G L, hz,ht,ha.below hh 1 zero_lt_one] with t hx hu hy hv hb' ha r c B hk hT Q hQ d hd f g F hF hZ x h' hV
  simp only [one_mul] at hb' hv
  have hr : 0<r:= Real.rpow_pos_of_pos hx _; have hA: 0<A t:=Real.rpow_pos_of_pos hx _
  have hr': W t≤1:=le_trans (le_abs_self _) ha; have hA': A t≤1:= le_trans (le_abs_self _) hu
  have hB:b*B.threshold < r:= lt_of_le_of_lt (mul_le_mul_of_nonneg_left hT hb.le) (by rwa [← mul_assoc])
  have hm:= hD c B (A t) r Q x hA hA' h' hr' hB (hv.trans_le (by rw [hk]; rw [Real.rpow_neg hx.le]; exact hy.2)) hQ hV
  let c':= (-A t) • x; have hs : 0<s t:=mul_pos hA (mul_pos hb hy.1)
  have ht:s t≤A t*r:= mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left (hk.symm ▸ hy.2) hb.le).trans hB.le) hA.le
  have hc : ‖c'‖+s t≤ p t:=by rw [show ‖c'‖=A t*‖x‖ from by unfold c'; rw [norm_smul,norm_neg, Real.norm_of_nonneg hA.le]]; exact (add_le_add (mul_le_mul_of_nonneg_left h'.le hA.le) ht).trans_eq (by unfold p W; ring)
  obtain HZ := Hc (Directions G c) (f-Cabana.actual g) x c' (s t) (p t) (F*|M t|) (F*|Y t|) hs hc (mul_nonneg hF (abs_nonneg _)) (mul_nonneg hF (abs_nonneg _)) (by
    intro y hy'; have h: Dart ((-A t) • x) (A t*(b*B.threshold)) y:= by obtain ⟨z,h₁,h₂⟩:=hy'; refine ⟨z,h₁,h₂.trans (mul_le_mul_of_nonneg_left ?_ h₁.1)⟩; refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hk.symm ▸ hy.2) hb.le) hA.le
    have hv:= hm y h; obtain ⟨he,hT,hp⟩:= hZ _ hv.1 hv.2; refine ⟨he.sub (moves g _|>.contDiffAt),?_,hp⟩; rwa [iteratedFDeriv_sub_apply he (moves g _|>.contDiffAt),highPoly g _ hd,sub_zero])
  have hy: 1 ≤ r*(s t)⁻¹:= by rw [← div_eq_mul_inv,one_le_div hs]; exact ht.trans (mul_le_of_le_one_left hr.le hA')
  refine ⟨HZ.smooth,inv_nonneg.mpr hr.le,fun i hi=>?_⟩; refine (HZ.order _ hi).trans ?_
  have hb:0≤K*(F*|Y t|+ F*|M t| * p t^_):= HZ.nonneg
  change _ ≤ F*|V t| *r⁻¹^i; have hw : W t=r:=rfl
  have hv: 0≤p t:=le_trans (add_nonneg (norm_nonneg _) hs.le) hc
  rw [abs_of_nonneg (show 0 ≤ V t by unfold V; rw [hw]; positivity)]; unfold V; rw [hw]
  generalize hA': K = E₀
  -- rewrite (r*s⁻¹)^i * r^-i
  have he:(s t)⁻¹^i=(r*(s t)⁻¹)^i*r⁻¹^i:= by rw [← mul_pow]; field_simp -- edit
  -- only left!
  rw [he]
  subst E₀; apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hy hi) (pow_nonneg (inv_nonneg.mpr hr.le) _)) hb); apply le_of_eq; ring
end
end YM.LocalLTE.Cabana
