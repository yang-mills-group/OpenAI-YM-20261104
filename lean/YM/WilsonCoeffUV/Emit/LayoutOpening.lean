import YM.WilsonCoeffUV.Emit.ProfileCharge
/-! # ζ openings and charges (ρ/native distance conversion)

All quantitative shelf coefficients are in formal units. Costs can be read
against exponential in Λ_k (flat here) or gate leakage; not the iteration.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Layout
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{W V E U U':Credit}{m b b' j e p i a:ℕ}{R:Realm G (e+1) E}{r z c t:ℝ}{T:Fin (a+1)→SealR G}{H:Hol G}
lemma exempt (A: Levels G)(g:G.Simple)(T:Credit)(h:0<c): ∀ᶠ m in atTop,T.buy (zz A m) ≤ c*longLog A m:=( (stamp_lim A g).eventually (absorbed T c h)).mono fun m hz=>by rw [spend] at hz; exact hz.trans (mul_le_mul_of_nonneg_left (by unfold longLog; linarith) h.le)
lemma back_paid (H: Hol G)(T:Fin (a+1)→SealR G)(C E W V L U:Credit)(e:ℕ): ∃ X:Credit,∀ z,1≤z→hgate H T E W V L U e (C.buy z)≤ X.buy z:=by
   let g:= (dictated H T E W V L e).choose; let P:= iceBill G (fun i=>(T i).D) (asp T) (asp T) e g U E; let B:= ((pur 2).prodC P.behind).prodC U.behind; refine ⟨B.usingC C,fun z hz=>?_⟩; rw [Credit.stock_up]; let Z:= C.buy z; unfold B; rw [Credit.products,Credit.products]; have hx:=C.purchase hz; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pure_goal ..) (zero_le_one.trans (P.behind.purchase hx))) (zero_le_one.trans (U.behind.purchase hx))

def middle (d r:ℝ):=d*r/2
-- formal small opening. physical callers use r≥Λ^B, B>20. Allows entire [Λ^B,Λ^{B+1}]
lemma gale_paid (H: Hol G)(T:Fin (a+1)→SealR G)(C E W V L U:Credit)(d:ℝ)(h:0<d)(e:ℕ)(A:Levels G)(g:G.Simple): ∀ᶠ m in atTop,∀ r:ℝ, longLog A m^2 ≤ r → middle d r +14 ≤ d*r ∧ hgate H T E W V L U e (C.buy (zz A m)) ≤ middle d r :=by
    obtain ⟨X,hX⟩:= back_paid H T C E W V L U e; filter_upwards [(stamp_lim A g).eventually_ge_atTop 1, (toward A g).eventually_ge_atTop (28/d), exempt A g X (half_pos h)] with m hm hU v
    intro r hr; let Z:= longLog A m; let z:=zz A m; have hx:1≤ Z:=by linarith [long_pos A m]
    have he: Z≤r:=(le_trans (b:=Z^2) (by nlinarith only [hx]) hr); unfold middle; have h':28 ≤Z*d:=(div_le_iff₀ h).mp hU; have ht:= mul_le_mul_of_nonneg_left he h.le
    refine ⟨by linarith,le_trans (hX z hm) (v.trans ?_)⟩; change d/2*Z≤_; linarith
lemma portraits (H:Hol G)(T: Fin (a+1)→SealR G) (P V E W L U:Credit)(e:ℕ)(d:ℝ)(g:0<d):∃ Z:Credit,∀ (R:Realm G (e+1) E), R.y=zz R.draws → ∀ᶠ m in atTop,∀ b j a r (_p:Windows R.draws a m b j r)(B:ℕ) (φ:Wilt T)(A:Fin _→ℝ)(t:1≤r), R.anchor≤ j → longLog R.draws m^2 ≤ r → r ≤ P.buy (longLog R.draws m)→ Scenery T φ B d A →
    Shipfit R.draws.S T (sceneGrow t φ) m b (middle d r) (Z.buy (zz R.draws m)) (fun i=> r⁻¹^4*A i) B∧ hgate H T E W V L U e (Z.buy (zz R.draws m)) ≤ middle d r ∧ PadRank R b m (Z.buy (zz R.draws m)):=by
   obtain ⟨A,Z,h⟩:= soft_cost (G:=G) (e:=e+1) P E; refine ⟨Z,fun R hp=>(gale_paid H T Z E W V L U d g e R.draws R.hG).mono (fun m hm b j a r p B φ V t v x y u=>?_)⟩
   obtain ⟨ht,hz,hv⟩:= h R a m b j r p v t y hp; obtain ⟨c,d⟩:= hm r x; refine ⟨⟨p.capture.le,hv,fun i=>zoom_charge t (φ i) (u.stations i), fun i=>mul_le_mul (u.sizeT i) p.firstC (zero_le_one.trans t) (by positivity), fun i j h x' a y' b=> c.trans (clearance (u.gaps i j h) t _ a _ b)⟩,d,hz⟩

/-- Even inverse widths after backstop. Numerical savings per coefficient. -/
theorem earned (C U:Credit)(d:ℝ)(h:0<d)(A:Levels G)(g:G.Simple)(z:ℝ)(p:0<z): ∀ᶠ m in atTop,∀ r:ℝ, longLog A m^2 ≤ r→ ∀ i≥ m,
    Real.exp (-penaltyB U (C.buy (zz A m)) (middle d r) (snowP A.S m i)) ≤ Real.exp (-(z* longLog A m)*Real.exp (snowP A.S m i/8)) :=by
    let c:=d/(4*z); have hc:0<c:=by unfold c; positivity
    filter_upwards [exempt A g (U.behind.usingC C) hc,(stamp_lim A g).eventually_ge_atTop 1] with m hm hM
    intro r x i _; unfold penaltyB; apply Real.exp_le_exp.mpr; rw [neg_mul_eq_neg_mul]; refine mul_le_mul_of_nonneg_right (neg_le_neg ?_) (by positivity)
    let Z:=longLog A m; let t:= U.behind.buy (C.buy (zz A m)); have hf:1≤ t:= U.behind.purchase (C.purchase hM); refine (le_div_iff₀ (show 0<2*t by positivity)).mpr ?_
    rw [Credit.stock_up] at hm; unfold middle; change z*Z*(2*t)≤_; change t≤ c*Z at hm; have hZ:= (show 0≤Z by linarith [long_pos A m]); calc
       _ ≤ z*Z*(2*(c*Z)):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm (by norm_num)) (by positivity)
       _ = d*Z^2/2:=by unfold c; field_simp; ring
       _ ≤ _ := by gcongr
-- translation under hp to YM numeric
lemma band_savings (A:Levels G)(δ:ℝ)(h:0<δ)(m:ℕ) (β:ℝ)(p:0<β)(u:β≤2*A.clock.hatBeta m): Real.exp (-(δ*longLog A m))≤ ((Real.sqrt β)⁻¹)^δ:=by
    let T:=A.clock.hatBeta m; have hp:0<T:=zero_lt_one.trans (A.fits.delayed m)
    rw [Real.rpow_def_of_pos (by positivity),Real.log_inv,Real.log_sqrt p.le]; refine Real.exp_le_exp.mpr ?_
    have hb:= Real.log_le_log p u; rw [Real.log_mul (by norm_num) hp.ne'] at hb; have hx:Real.log 2 ≤ 1:= by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (2:ℝ)>0)]
    unfold longLog; nlinarith only [h,hb,hx,Real.log_pos (A.fits.delayed m)]
end YM.WilsonCoeffUV.Layout
