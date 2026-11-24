import YM.LocalLTE.Frame.Prices
/-! Price simultaneous log links Φ. This supplies leases BEFORE composing
any allocated authority on F. Room for AUX gauge rewrite loops while holding
θ and ALL fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Frame
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat SliceRows
open AbsoluteSums PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Inset
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
section fees
variable {X F Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {h : X → F} {g:F→Y} {j n : ℕ} {u a e f v : ℝ} {x:X}
lemma currency (hf:Brush j f 1 h x) (he:‖h x‖ ≤ u) (hd:0<a) (hc:u>0) (hp:a*f≤u) (hv:a≤1) :
    Brush j u a⁻¹ h x:= by
  refine ⟨hf.smooth,(inv_pos.mpr hd).le,fun i hi=>?_⟩
  rcases i with i|i
  · simpa only [normJ,norm_iteratedFDeriv_zero,pow_zero,mul_one]
  have ht : f ≤ u*a⁻¹:= by rw [← div_eq_mul_inv]; exact (le_div_iff₀ hd).mpr ((mul_comm f a).trans_le hp)
  exact ((Brush.offer.1 hf).inside (i+1) hi).trans (ht.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ ((one_le_inv₀ hd).2 hv) (by omega)) hc.le))
lemma cascade (hf:Brush j u a h x) (hp:Brush j v u⁻¹ g (h x)) (hu:u>0) : Brush j (j.factorial*v) a (g∘h) x:= by
  let Q:= u • ContinuousLinearMap.id ℝ F
  let f': X→F:= fun y=>u⁻¹ • h y; have hh y:Q (f' y)=h y:= by simp [Q,f',smul_smul,hu.ne']
  have he : Brush j v 1 (g ∘ Q) (f' x):= by
    have h': ‖Q‖ ≤u:= by unfold Q; rw [norm_smul,Real.norm_of_nonneg hu.le]; exact mul_le_of_le_one_right hu.le ContinuousLinearMap.norm_id_le
    have hc:= Brush.reading Q (hh x|>.symm ▸ hp) h'; rwa [inv_mul_cancel₀ hu.ne'] at hc
  have hc : Brush j 1 a f' x:= by
    have hp:= hf.smul u⁻¹; rwa [norm_inv,Real.norm_of_nonneg hu.le,inv_mul_cancel₀ hu.ne'] at hp
  apply (Brush.compound he hc.smooth hc.pos (fun i _ hi=> by simpa only [one_mul] using hc.order i hi)).shimmy; exact Eventually.of_forall fun i=> congr_arg g (hh i).symm
end fees
variable {G : Gauge} {L : Side} {j n : ℕ} {a Y d₀ d v k H : ℝ} {f : ℝ → ℝ} {χ:Chi}
-- Growth promises exactly stage `x ≤ monitor^- ...`.
structure Lease (G:Gauge) (j : ℕ) (w : ℝ) (c : Side) (u d : ℝ) (χ:Chi): Prop where
  ok : 0 < d
  fine : 0< u
  books (V:Positions (Uniform.Primary c G)) (hh:‖V‖< d) (i:G.El) :
      let f := convertLinks (G:=G) (c:=c) χ w i
      actual ∘ f ∘ actual =ᶠ[𝓝 V] fun y=> chainT i (actual y) -- uniform in angular parameter? individually; sufficient.
  arcs (V:Positions (Uniform.Primary c G)) (hh:‖V‖< d) (i:G.El) : let f:= convertLinks (G:=G) (c:=c) χ w i
      ‖f (actual V)‖<u ∧ Brush j u d⁻¹ (f ∘ actual) V

lemma leased (G:Gauge) (j:ℕ) (hk : Reliable G k H) (v w:ℝ) (hz : w<v) (hb : v<0) (hf: Rate G L 0 f) : ∀ᶠ p in atTop,
    ∀ c : Side, (c.val:ℝ) ≤ f p → Lease G j k c (cone v (betaF G p L)) (cone w (betaF G p L)) χ:=by
  obtain ⟨C,R,hC,hR,hL⟩:= chord_chart_cost G
  obtain ⟨C₀,hC₀,hP⟩:=Blaze.expCost G j 1
  let S:= Uniform.shade G; have hS:0<S:= Uniform.shade_pos G
  obtain ⟨J,D,hD⟩:=Frond.cleanly G j _ zero_lt_one
  let Y p:= cone w (betaF G p L); let E p:= cone v (betaF G p L)
  let M p:= (8*f p+1)*(C*(S*Y p)); have hK : Rate G L w M := by
    have hh := ((hf.mul_left 8).add (Rate.const 1)).mul (((Rate.power (G:=G) (L:=L) (a:=w)).mul_left S).mul_left C); rwa [zero_add] at hh
  let e:= shine j C₀ S
  let b p:= (1+Blaze.royalty G)*expense G (f p) e; let b' p:= j.factorial*J*(1+b p)^j
  have hx : Rate G L 0 b := by
    let Z_ p:= 4*f p*(e*Blaze.royalty G); have h : Rate G L 0 Z_:= ((hf.mul_left _).mul_right _)
    unfold b expense; exact ((h.mul_right _).add ((Rate.const _).add h)).mul_left _
  have he : Rate G L 0 b':= by
    refine Rate.mul_left (by simpa only [zero_mul] using (((Rate.const 1).add hx).pow j)) _
  have h₀:= Rate.power (G:=G) (L:=L) (a:=w)
  have h₁:= h₀.mul_left S; have hy:= hz.trans hb
  filter_upwards [Delay.shift_pos G L,below' G L hK hy hk.down, below' G L h₀ hy zero_lt_one,
    below' G L h₁ hy (lt_min hR zero_lt_one), contraction G L (b:=1) (a:=H) zero_lt_one hK hz,
    contraction G L (b:=1) (a:=1) zero_lt_one (h₀.mul he) (by rw [add_zero]; exact hz), below' G L (hK.mul_left G.colorScale) hy hD.pos] with p hp hh hY hΛ hT hΔ hG c hv
  have ha:0<Y p:=Real.rpow_pos_of_pos hp _; have hs := le_of_lt (lt_min_iff.mp hΛ).2; have he := le_of_lt (lt_min_iff.mp hΛ).1
  have ht : 0 ≤ f p := (Nat.cast_nonneg _).trans hv
  let X:=Positions (Uniform.Primary c G)
  have ht (x:X) (hx: ‖x‖ < Y p) (u:G.El) i : G.chord (chainT u (actual x) i) ≤ M p := by
    apply minorChord hv
    · positivity
    intro i; exact lit_exp i _ hL hC.le (mul_le_mul_of_nonneg_left hx.le hS.le) he
  have hd x (hx : ‖x‖ < Y p)(u:G.El): ∀ᶠ y:X in 𝓝 x,∀ i,G.chord (chainT u (actual y) i)≤ k:= by
    filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds hx)] with y hy; exact fun i=> (ht _ hy u i).trans hh.le
  refine ⟨ha,Real.rpow_pos_of_pos hp _,fun x hx i=>mapped hk x i (hd x hx i),fun V hv' i=>?_⟩
  let g:= convertLinks (G:=G) (c:=c) χ k i
  have hx : ‖g (actual V)‖< E p:= (shortKey hk V i (M p) hh.le (ht V hv' i)).trans_lt (by rw [one_mul] at hT; exact hT)
  have hu: Brush j _ (b p) (g ∘ actual) V:= germPrice (a:=expense G (f p) e) hD hk V i (modeBasis V (mode_map hs hP V hv' hY.le) hv i) (fun j=> ?_) (hd V hv' i)
  · refine ⟨hx,currency hu.trim hx.le ha ((norm_nonneg _).trans_lt hx) ?_ hY.le⟩
    have he : Y p*b' p < E p:= by rw [one_mul,one_mul] at hΔ; exact hΔ
    exact he.le
  rw [← chord_dist]; exact (mul_le_mul_of_nonneg_left (ht V hv' i j) G.colorScale_pos.le).trans hG.le
end YM.LocalLTE.Frame
