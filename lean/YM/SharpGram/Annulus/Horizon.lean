import YM.SharpGram.Annulus.Telescope

/-!
# Reflected norm at arbitrary intermediate all-scale points

Filtered functional prices & Gram bounds from the adjacent Schur
near-isometry assumption. OS monotonicity guarantees both estimates all the
way to lengths falling inside integer log steps. Consume Mantle along every
large UV k. Does NOT confuse projection-valued assistance with a basis of
top offshell representatives. The resulting prices pay exact ticket, in
Lenses. Use the same gauge curvature normalization for both comparisons.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Annulus
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Climb RG Lattice
open Org Spec Next.UVStress Lenses Weak.Portfolio OPE OPE.Log
open scoped Topology ContDiff BigOperators Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{u:Filter (ℕ×ℕ)}
variable {F: Final C f S}
local notation "P"=> C.path.levels.clock.hatBeta
local notation "V!"=>F.sector.derivatives
local notation "σ"=>F.room.kernel.spin
variable {d w i j : ℕ}
local instance (d : ℕ) : FiniteDimensional ℝ (S.Field d) := Module.Finite.trans ℂ _
variable (h : Fits F) (B : Mantle F u)

-- interim t measured in inverse radius logarithms
abbrev fill (r : ℝ) := - Real.log r
abbrev chin (r : ℝ) := Nat.floor (fill r)

lemma floor_round {r : ℝ} (hr : 0<r)(hu : r≤1): plank (chin r+1) ≤ r ∧ r ≤ plank (chin r) ∧
       plank (chin r) = epoch * plank (chin r+1) ∧ (chin r:ℝ) ≤ fill r := by
   have hb : (↑(chin r):ℝ) ≤ fill r:=Nat.floor_le (neg_nonneg.mpr (Real.log_nonpos hr.le hu))
   have hx : fill r<chin r+1:= Nat.lt_floor_add_one _
   have hz : -(chin r:ℝ) ≥ Real.log r:=by unfold fill at hb; linarith
   refine ⟨(Real.le_log_iff_exp_le hr).mp ?_, (Real.log_le_iff_le_exp hr).mp hz, ?_, hb⟩
   · push_cast; unfold fill at hx; linarith
   unfold plank epoch; rw [← Real.exp_add]; push_cast; ring_nf

lemma later : Tendsto (chin ∘ B.radius) atTop atTop := by
   have hp:= Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨B.small, Eventually.of_forall fun i=>B.positive i⟩)
   exact tendsto_nat_floor_atTop.comp (tendsto_neg_atBot_atTop.comp hp)


lemma rates (hG:G.Simple) : Wallet atTop P (fun k=> dial (chin (B.radius k)+1)) := by
   have hc : 0 < G.slopeConstant:= Gauge.slopeConstant_pos hG
   have he := Next.Rank.Station.hat_rate C.path.levels hG -- binder
   have ht : Wallet atTop P (fun k:ℕ=> P k * G.slopeConstant⁻¹ + 2) := ((Wallet.id he).mul (Wallet.const he _)).add he (Wallet.const he (2:ℝ))
   refine ht.of_le' (Eventually.of_forall fun _=> dial_pos _) ?_
   filter_upwards [B.proper,B.small.eventually (ge_mem_nhds zero_lt_one)] with k ⟨hk,hP⟩ hm
   let Z := C.path.levels.clock; let s:= C.S.a k; have hs:0<s:=C.S.a_pos _
   have hy : fill (B.radius k) ≤ C.S.scale k := by
      change _ ≤ Real.log _; rw [Real.log_inv]; exact neg_le_neg (Real.log_le_log hs hk)
   have hf : C.S.scale k ≤ P k / G.slopeConstant := by
     refine (le_div_iff₀ hc).2 ?_; rw [mul_comm,Calendar.hatBeta]; exact le_add_of_nonneg_left Z.bar_pos.le
   unfold dial; push_cast; rw [← div_eq_mul_inv]; linarith only [hy,hf,(floor_round (B.positive k) hm).2.2.2]

variable (hG : G.Simple)
include B h hG
lemma inbound_price (x : S.Field d): ∃ p : ℕ, ∀ᶠ k in atTop,
   ‖(B.lens k d).symm x‖ ≤ P k ^ p / C.S.a k^d := by
   obtain ⟨i,A,hA,hr⟩:=inbound h B d x
   obtain ⟨δ,hδ,hK⟩:=B.reflects d
   have hb:= Next.Rank.Station.hat_rate C.path.levels hG
   let D:= dial ∘ (fun k=> chin (B.radius k)+1); let c:=(Real.sqrt (δ/2))⁻¹
   obtain ⟨v,hv⟩:= (Wallet.const hb (c*A*epoch^d)).mul ((rates B hG).pow hb i)
   refine ⟨v,?_⟩
   have He := zero_lt_one.trans epoch_ge; have hc:0<c:=by unfold c; positivity
   have hQ:Tendsto (fun k=> chin (B.radius k)+1) atTop atTop:=tendsto_atTop_mono (fun k => Nat.le_succ _) (later B)
   filter_upwards [B.proper,B.small.eventually (ge_mem_nhds zero_lt_one), hK, hv, hQ.eventually hr] with k ⟨hk,_⟩ h0 ⟨_,hf⟩ hv ha
   let y:= (B.lens k d).symm x; let s:=B.radius k; let n:=chin s
   have hs:0<s:=B.positive _; have hp:0<plank (n+1):=Real.exp_pos _
   have hd : D k= dial (n+1):=rfl
   obtain ⟨hy,ht,hN,_⟩:=floor_round hs h0
   let r:= life F (n+1) x; have hh : ‖y‖ ≤ c*r:=by
      apply (le_inv_mul_iff₀' (Real.sqrt_pos.2 (half_pos hδ))).2
      apply (sq_le_sq₀ (by positivity) (positiveLife (F:=F) _ _)).mp
      rw [mul_pow,Real.sq_sqrt (half_pos hδ|>.le),show r^2= _ from Real.sq_sqrt (positive F.room.kernel hp x)]
      have he:=hf y; change _ ≤ glass S _ d _ ((B.lens k d) ((B.lens k d).symm x)) ((B.lens k d) ((B.lens k d).symm x)) at he; rw [LinearEquiv.apply_symm_apply] at he
      change _ ≤ roomRate F d (n+1) x x
      exact (mul_comm ..).trans_le (he.trans (expands F.room.kernel d x _ _ hp hy))
   have hS := C.S.a_pos k
   have ht':= dial_pos (n+1)
   have hC : C.S.a k ≤ epoch * plank (n+1):= hk.trans (ht.trans_eq hN)
   refine (hh.trans (mul_le_mul_of_nonneg_left ha hc.le)).trans ?_
   change c*(A*dial (n+1)^i / plank (n+1)^d) ≤ _
   calc
       _ ≤ c*A*epoch^d *dial (n+1)^i / (C.S.a k)^d := by
           rw [← mul_div_assoc,div_le_div_iff₀ (pow_pos hp _) (pow_pos hS _)]
           exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hS.le hC d) (by positivity)).trans_eq (by rw [mul_pow]; ring)
       _ ≤ _ := div_le_div_of_nonneg_right ((Real.le_norm_self _).trans hv) (pow_pos hS _|>.le)

lemma outbound_price (L : S.Field d →ₗ[ℂ] ℂ)(hw : w ≤ d)(hL : Kills (C:=C) (V!) hw L) :
   ∃ p : ℕ, ∀ᶠ k in atTop, ∀ x, ‖L ((B.lens k d) x)‖ ≤ P k^p * C.S.a k^w * ‖x‖:= by
   obtain ⟨i,K,hK,he⟩:=outbound h B w hw L hL
   obtain ⟨δ,hδ,H⟩:=B.reflects d
   let A:= Real.sqrt (δ/2+ ‖model C d‖)
   have hb:= Next.Rank.Station.hat_rate C.path.levels hG
   obtain ⟨p,hp⟩:= (((Wallet.const hb (K*epoch^w*A)).mul ((rates B hG).pow hb i)).mul ((Wallet.id hb).pow hb (2*w)))
   refine ⟨p,?_⟩; filter_upwards [B.proper,B.small.eventually (ge_mem_nhds zero_lt_one),H,hp,(later B).eventually he] with k ⟨hk,hb⟩ ht ⟨hD,hZ⟩ hf hw x
   let y := B.lens k d x; let r:=B.radius k; let n:= chin r
   have hr:= B.positive k; change 0 < r at hr; have hh:= Weak.Portfolio.normBy hD
   have hu := dial_pos (n+1);have hz:= dial_pos n; have hP : 0≤ A:= by unfold A; positivity
   obtain ⟨hΘ,hq,hq',_⟩:=floor_round hr ht
   have hp : plank n ≤ epoch * r := hq'.trans_le (mul_le_mul_of_nonneg_left hΘ (Real.exp_pos _|>.le))
   have hpr : plank n ≤ epoch*(C.S.a k*P k^2):=hp.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _|>.le))
   have hv : life F n y ≤ A*‖x‖ := by
      apply (sq_le_sq₀ (positiveLife _ _) (mul_nonneg hP (norm_nonneg _))).mp
      rw [life,Real.sq_sqrt (positive F.room.kernel (Real.exp_pos _) y),mul_pow,show A^2=_ from Real.sq_sqrt (add_nonneg (half_pos hδ|>.le) (norm_nonneg (model C d)))]
      apply (expands F.room.kernel d y r _ hr hq).trans
      change B.reflectAt k d x x ≤ _
      exact (realUpper _ x).trans (mul_le_mul_of_nonneg_right hh (sq_nonneg _))
   have he:= zero_lt_one.trans epoch_ge; have ha:= C.S.a_pos k
   have hd:dial n ≤ dial (n+1):=by unfold dial; norm_num
   have hr':0< P k:= zero_lt_one.trans (C.path.levels.fits.delayed k)
   refine (hw y).trans ?_
   change K*dial n^i*plank n^w *life F n y ≤ _
   calc
      _ ≤ K * dial (n+1)^i * (epoch*(C.S.a k * P k^2))^w * (A * ‖x‖) := by
        have hh: 0 ≤ plank n:=Real.exp_nonneg _; gcongr 
      _ = (K* epoch^w*A* dial (n+1)^i *P k ^ (2*w)) * C.S.a k^w * ‖x‖:= by rw [pow_mul]; simp only [mul_pow];ring
      _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((Real.le_norm_self _).trans hf) (pow_pos ha _|>.le)) (norm_nonneg _)
end YM.SharpGram.Annulus
