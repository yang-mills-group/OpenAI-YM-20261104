import YM.MatchingLedger.Compass.Tiled
import YM.MatchingLedger.Hessian.Pipes

/-! # Separate `alpha` from the the assembled draft equality

Adaptation of Pert.Kinetic.Branch etc. Exploit exact metric & VanishingLoop grade along
an axis. No E yet (true comparison coming later). Page independent cost. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.MatchingLedger.Compass
open Function Filter Set MeasureTheory Precision RG Tree Wilson Lattice Work Exterior
open WilsonStartup.Change Extension.UV.LoopRate Extension.UV.StationaryData Bid
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
namespace Lines
open F03 Pert Pert.Kinetic Mirrors Spring
variable {G:Gauge} {W:PathData G}{p:Clip}{σ C Λ:ℝ}(h:W.Bounds p σ C Λ) (α:ℝ)
    {n:Side}

def full (W:PathData G)(p:Clip)(α:ℝ)(y:Dir G n) := α*AT n p W y+ L n W y
include h
lemma sees : Matches 2 (full (n:=n) W p α) (draft α W p) 0:=
   let H:= rooted W (f:=n) p ⟨_,_,_,h⟩
   (H.1.refl_comp (u:=fun a:ℝ=>α * a) (contDiffAt_const.mul contDiffAt_id)).add (matches_self _ H.2.left)
lemma bills (x:fieldDir G n 1) : Tendsto (fun t:ℝ=> full W p α (t • x)/t^2) (𝓝[≠] 0) (𝓝 (actualPath (p:=p) W α (collect G x))):= multi_tangent h α (collect G x)
lemma resting : full (n:=n) W p α 0=0 ∧ fderiv ℝ (full (n:=n) W p α) 0=0:=by
   have he : ContDiffAt ℝ ω (full (n:=n) W p α) 0:= (sees h α).left
   have ha(x:Dir G n) : ContDiffAt ℝ ω (fun t:ℝ=> full W p α (t • x)) 0:= (show ContDiffAt ℝ ω (full W p α) ((0:ℝ) • x) from by simpa using he).comp (f:=fun t:ℝ=> t • x) _ (by fun_prop)
   have hc (x:Dir G n):= value_slope_of_sq_limit (ha x).continuousAt (bills h α x)
   exact ⟨by simpa using (hc 0).1, ContinuousLinearMap.ext fun x=> (Push.side (full W p α) (he.differentiableAt (by simp)) x).unique (hc x).2⟩
lemma axis (x:Directions G n) : actualPath (p:=p) W α x= (H₂ (draft α W p) ![lift1 x,lift1 x])/2:=by
   let y:=lift1 x; let F:=full W p α (n:=n); have hF:Matches 2 F (draft α W p) 0:= sees h α
   let f(t:ℝ):= F (t • y)
   have hz:Tendsto (fun t:ℝ=> f t / t^2) (𝓝[≠] 0) (𝓝 (actualPath (p:=p) W α x)):= by simpa only [back_wave] using! bills h α (lift1 x)
   have he₁: ContDiffAt ℝ 2 F 0:= hF.left.of_le le_top
   have he: ContDiffAt ℝ 2 f 0:=(show ContDiffAt ℝ 2 F ((0:ℝ) • y) from by simpa using he₁).comp (f:=fun t:ℝ=> t • y) _ (by fun_prop)
   obtain ⟨hx,hv⟩:= value_slope_of_sq_limit he.continuousAt hz
   rw [tendsto_nhds_unique hz (taylor_limit_two he hx hv.deriv), show iteratedDeriv 2 f 0=_ from line_second he₁ (resting h α).2 y, hF.jets 2 le_rfl]

def fee n (p:Clip) (W:PathData G)(α:ℝ)(c:G.Color) := (∑ b:Bool,(H₂ (draft α W p) ![lift1 (rowWave (n:=n) c b),lift1 (rowWave c b)])/2)/purchase n
lemma collection (hn:4≤n.val)(c:G.Color)(hc:‖c‖=1) : ‖fee n p W α c-α‖ ≤ Full.mesh n* (2*tone*windPrice σ C Λ α):=by
   unfold fee; simp_rw [← axis h α]; let f:=fuel n; let m:= Full.mesh n; let U:=∑ b:Bool, actualPath (n:=n) (p:=p) W α (rowWave c b); let e:=purchase n;let z:=windPrice σ C Λ α
   have hj:eigen n>0:= eigen_pos hn; have hF:= fuel_pos n; have he:e>0:= purchase_pos hn; have hm:m>0:=Full.mesh_pos
   have hx: ‖U-α*e‖≤ f*m^3*z:= by rw [show α*e=α/2* (Fintype.card (Site n):ℝ)*(4*Real.sin (Full.mesh n/2)^2) from (by unfold e purchase eigen fuel; ring)]; exact sum_rates h hn hc α
   have hF':0<f:=hF
   have hz : 0≤ z:= nonneg_of_mul_nonneg_right ((norm_nonneg _).trans hx) (mul_pos hF' (pow_pos hm 3))
   change ‖U/e-α‖≤ m*_ ; rw [show U/e-α=(U-α*e)/e from by field_simp, norm_div,Real.norm_of_nonneg he.le,div_le_iff₀ he]
   refine hx.trans ?_; have hL := mul_le_mul_of_nonneg_right (show m^2≤ tone*eigen n from eigen_price hn) (show 0≤ f*m*z from by positivity)
   unfold e purchase; linarith only [hL] -- fuel f unfold?
omit h in
lemma range_period (A:Levels G)(m:ℕ) : Tendsto (fun p=> Full.mesh (A.S.side m p)) atTop (𝓝 0):= by
  unfold Full.mesh; exact tendsto_const_nhds.div_atTop (size_grows A m)
lemma payout (A:Levels G)(m:ℕ)(c:G.Color)(hc:‖c‖=1): Tendsto (fun i:ℕ=> fee (A.S.side m i) p W α c) atTop (𝓝 α):=by
   refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun p'=> norm_nonneg _) (fun p'=> collection h α (by have hx := A.fits.sizeT m p'; change 100*(_+1)≤ (A.S.side m p').val at hx; omega) c hc) ?_)
   · simpa only [zero_mul] using! (range_period A m).mul_const (2*tone*windPrice σ C Λ α)
end Lines
end YM.MatchingLedger.Compass
