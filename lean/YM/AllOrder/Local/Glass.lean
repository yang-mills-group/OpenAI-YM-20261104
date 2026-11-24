import YM.AllOrder.Local.Cumulant

/-!
# Uniformly after `L`, polynomial-period small-field Laplace comparison

All `s ≥ k+1`, `BallGeom` costs paid in `H`, preserve ∥jets∥ even
higher than comparison order, scale `r⁻¹`. Uniform in any real center BOTH
(b,x) on the stencil. `b` actual fine coupling; centered at zero with state.
Shard at radius `d*fineMonitor` supplied. Price not per polymer addresses yet.
Tail error independently flat; no limits in the spatial periods assumed.
Only `Golf` data indexed by beta_hat level pay these bills.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Vote
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix
open Lattice Wilson RG Gauge Pressure Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush PhysicalNext Repeat Lantern Poll Work.G05
open scoped Topology Classical ContDiff ENNReal
variable (G : Gauge) (L : Side) (j k : ℕ) (q : ℝ→ℝ) {F R : ℝ→ℝ} {a e d c D : ℝ}
    (hq : Bolt G L q) (hF : Rate G L 0 F) (ha : a<0) (hR : Rate G L a R) (hd : 0<d) (hc : 0<c)
local notation "z" => (fun t=> betaF G t L)
local notation "p" => (fun t=> d*Delay.fineMonitor G L t)
include hd
lemma bounds1 : ∀ᶠ t in atTop, 1 ≤ p t := by
  filter_upwards [Delay.monitor_pays G L 0 (inv_pos.mpr hd).le zero_lt_one] with x hx
  rw [pow_zero,mul_one,Real.rpow_one] at hx; exact ((inv_le_iff_one_le_mul₀ hd).mp hx).trans_eq (mul_comm ..)

omit hd in
lemma mul_free {V H : ℝ → ℝ} (h : Rate G L a H) (he : Rate G L 0 V) : Rate G L a (fun x=> H x*V x) := by simpa only [add_zero] using! h.mul he

include hc ha hq hF hR
set_option maxHeartbeats 200000 in
theorem prism (hj : k+1 ≤ j) (e : ℝ) : ∃ H : ℝ→ℝ, Rate G L 0 H ∧ ∀ᶠ t in atTop,
    ∀ (E: Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (ι:Type) [Fintype ι] [DecidableEq ι]
      (φ ψ:E×Body ι→ℝ) (ρ:E→Body ι) (M : E→Matrix ι ι ℝ),
    (Fintype.card ι:ℝ) ≤ q t → Golf φ ψ ρ M j (p t) (R t) (R t) (F t) →
    (∀ x:ι→ℝ,dotProduct x ((M 0)⁻¹ *ᵥ x) ≤ c*dotProduct x x) →
    ∀ x:ℝ×E, ∀ r:ℝ, ‖x‖≤r → r<R t → 0 < r →
      Brush j (H t*r^(k+1) + z t^e) (r⁻¹)
        (cleanLog φ ψ ρ M (p t)-connected φ ψ ρ M k) x := by
  let s:= Real.exp (-1)*(1/2); have hs:0<s:=by unfold s; positivity
  obtain ⟨C,hC,hE⟩:= Brush.compact (f:=Real.exp) (k:=j) (s:=Icc (-1:ℝ) 1) isCompact_Icc fun y _=> Real.contDiff_exp.contDiffAt
  obtain ⟨B,hB,hℒ⟩:= Brush.compact (f:=Real.log) (k:=j) (s:=Icc s (Real.exp 1)) isCompact_Icc fun y hz=> Real.contDiffAt_log.mpr (hs.trans_le hz.1).ne'
  obtain ⟨K,hK,hY⟩:= Log.price1 k (b:=Real.exp 1) hs
  obtain ⟨T,hT,hI⟩:= Log.priceInv k
  -- use t=z^(-w), tail ≤ z^(2*w), w< min(0,e).
  let U:=min e 0; let w:= U-1
  have hw: w < e:= by unfold w U; linarith [min_le_left e 0]
  have hw':w < 0:= by unfold w U; linarith [min_le_right e 0]
  let l:=2*((j+2)*j); let q' t:= z t^(2*w); let Y t:= z t^w
  let D:=p; let A t:=fee j (F t) (D t); let W t:=clump j (A t) C; let H t:= clump j (W t) B
  let J t:= W t*(Y t+volumeCost c l (q t)* Y t); let I t:= (k+1)*J t
  let V t:=clump k (W t+1) T; let P t:= Log.t2 k (I t * V t); let S t:= (k+1)*Log.t2 k (P t*clump k (1+Log.t2 k (1*V t)) K)
  have hA := fareRate j hF (Rate.monitor|>.mul_left d); have hW:= lumpRate j hA (Rate.const C); have hH := lumpRate j hW (Rate.const B)
  have hV : Rate G L 0 V:= lumpRate k (hW.add (Rate.const 1)) (Rate.const T)
  have hJ : Rate G L w I:= by
    have hy: Rate G L w (fun t=> Y t+volumeCost c l (q t)*Y t):= Rate.power.add ((v_rate hq.uses c l|>.mul Rate.power).weaken (zero_add w).le)
    exact (hW.mul hy|>.weaken (zero_add w).le).mul_left _
  have hP : Rate G L w P := (mul_free G L hJ hV).mul_right _
  have h' : Rate G L w S:= ((mul_free G L hP (lumpRate k ((Rate.const 1).add ((hV.mul_left 1).mul_right _)) (Rate.const K))).mul_right _).mul_left _
  have hfee:= (hA.mul hR|>.weaken (zero_add a).le).below ha 1 zero_lt_one
  have hh:= walls G L hq hc hd (2*w)
  refine ⟨H,hH,?_⟩; filter_upwards [bounds1 G L hd,hfee,hh,h' e hw, (Rate.power (G:=G) (L:=L) (a:=2*w)).below (by linarith only [hw']) (1/2) (by norm_num),hJ.below hw' 1 zero_lt_one, Delay.shift_pos G L] with t h₁ he hh hB' hy hI' hz E _ _ _ ι _ _ φ ψ ρ M hp h hv x r hr ht hr₀
  let μ:=sweep (M 0)⁻¹; let f:=ratify φ ψ ρ M (D t); let Z:= closedBall (0:Body ι) (D t)
  have ht' : R t≤1:=h.small
  have ha' : 0 ≤ W t:= (cl (c:=1) j (fn _ (golf_cost h) h.off) hC.le le_rfl).1
  have hu: fee j (F t) (D t)*max (R t) (R t)≤1:= by rw [max_self]; exact (le_abs_self _).trans he
  have hZ : μ.real Zᶜ=1-μ.real Z:=by rw [measureReal_compl (measurableSet_closedBall),probReal_univ]
  have he : 1 - μ.real Z ≤ z t^(2*w):= hh _ _ hp (m_origin h).inv hv
  have hv' : 1/2 ≤ μ.real Z:= by linarith only [he, (le_abs_self _).trans hy] -- he shadows hu not he predicate
  have hg (x:ℝ×E) (he:‖x‖≤r): Brush j (W t) 1 f x ∧ f x∈ Icc s (Real.exp 1) := by
    have hx := (norm_snd_le x).trans_lt (he.trans_lt ht); have he':= (norm_fst_le x).trans_lt (he.trans_lt ht); have hh:=burs _ h hx he' (by omega) hu hE hC.le; exact ⟨hh.1,temperature _ h hx he' (by omega) hu hh.2 hv'⟩
  let g:=cleanLog φ ψ ρ M (D t); have hr' := ht.le.trans ht'; have ha := Taylor.forecast (f:=g) hr₀ hr' hj (fun v hv=> composite (hg v hv).1 (hℒ _ (hg v hv).2)) hr
  have hG:= hg 0 (norm_zero.trans_le hr₀.le); have hi : k ≤ j:=by omega
  have hz' : 0< Y t:= Real.rpow_pos_of_pos hz _
  have hy' : z t ^ (2*w)=(Y t)^2 := by unfold Y; rw [mul_comm, Real.rpow_mul (le_of_lt hz), Real.rpow_two]
  let f':= aggregation φ ψ ρ M k
  have hR' (i:ℕ) (hl : i≤k) : i.factorial* ‖moment φ ψ ρ M i-Tensor.coeff f i 0‖ ≤ J t := by
    have H := moment_limit h h₁ hv hp (hE 0 (by simp)) (hl.trans hi) (Y t)⁻¹ (inv_pos.mpr hz')
    -- tail and division bookkeeping
    have hT: (Y t)⁻¹ * μ.real Zᶜ ≤ Y t := by rw [hZ]; apply le_trans (mul_le_mul_of_nonneg_left (he.trans_eq hy') (inv_pos.mpr hz').le); rw [sq,← mul_assoc,inv_mul_cancel₀ hz'.ne',one_mul]
    change _≤ W t*((Y t)⁻¹ * μ.real Zᶜ+ volumeCost c l (q t)/(Y t)⁻¹) at H; rw [div_inv_eq_mul] at H
    exact H.trans (mul_le_mul_of_nonneg_left (add_le_add hT le_rfl) ha')
  have hJ' : Brush k (I t) 1 (f'-blockTaylor k f) 0:= term_brush _ _ _ _ hR' (norm_zero.trans_le zero_le_one) k
  have hM : Brush k (I t) 1 (f'-f) 0:= comparison0 hJ' (hG.1.smaller hi).smooth
  have hs' : Brush j (S t) 1 (blockTaylor k g-connected φ ψ ρ M k) x := cumul_fee (by rw [← neg_sub]; exact hM.opposite) (show I t≤1 from (le_abs_self _).trans hI') (hG.1.smaller hi) hI (hs.trans_le hG.2.1) (hY _ hG.2) (hr.trans hr')
  exact (ha.gathering (hs'.climb (show S t≤ z t^e from (le_abs_self _).trans hB') ((one_le_inv₀ hr₀).2 hr'))).shimmy (Eventually.of_forall fun _=> by simp; rfl)
end YM.AllOrder.Local.Vote
