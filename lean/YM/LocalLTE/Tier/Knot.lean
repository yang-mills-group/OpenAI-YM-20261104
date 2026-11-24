import YM.LocalLTE.Tier.Stock
/-! Local LTE reiteration of the bookkeeping adapted from
`PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Typhos`.
New increment n₀ Arbitrary on non-inherited beyond-bulk grades.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}

open PhysicalNext.Repeat.Height
def wool (g : ℕ → ℝ) (c f : Side) : LogLetter c f→ ℝ:= Sum.elim g (fun _=>1)
lemma wax (f' : ℕ→ℝ)(h:∀ i,1≤ f' i) (i:LogLetter c f): 1≤ wool f' c f i:= by cases i <;> first | exact h _| exact le_rfl
lemma lessen {ι:Type*} {B:ℕ}{a b d:ℝ} {p:ι→Support c} {r z:ι→ℝ}{v:ι→ℕ}(hr:∀ i,1≤r i)
    (he:Sales B a b p (fun i=>r i*z i) v d) : Sales B a b p z v d:=by
  have hf i:0≤ z i:= nonneg_of_mul_nonneg_right (he.nonneg i) (zero_lt_one.trans_le (hr i))
  refine ⟨hf,fun x=>budget_mono (he.hit x) (fun i=> ?_) (fun i=>?_)⟩
  · split; next => change 0≤ z i * Real.exp _ * _; exact mul_nonneg (mul_nonneg (hf i) (Real.exp_pos _).le) (Real.exp_pos _).le
    exact le_rfl
  split; next => unfold Reserves.tariff; gcongr; exact le_mul_of_one_le_left (hf _) (hr _)
  exact le_rfl
/- Optional pre-census. Version of Raw.inherit_bills with grades. -/
theorem startsTier (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ r' P' : ℝ, ∀ n₀:ℕ,
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R → ∀ Y : ℕ→ℝ, Pumps R Y (P'*incomingE G L x) →
      ∃ z : LogLetter c f → ℝ, (∀ U V i, |expo T x R U V i| ≤ z i) ∧
        Sales (radiusB x) a ε (space T l (radiusB x) R) (fun i=>wool Y c f i * (grow G L x^chargeN n₀ c f i*z i)) (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) (betaF G x L ^ r') := by
  obtain ⟨n,hn⟩ := core_bills P l he ha hx
  obtain ⟨N,hH⟩:= aquifer P l he ha hx
  refine ⟨n⊔N,fun L hL r hv r' P' n₀ => ?_⟩
  obtain ⟨s,hm,hs⟩ := exists_between hv
  have ht := (Rate.hat (L:=L) (G:=G)).mul_left 2
  have hr := Rate.const (G:=G) (L:=L) P.top.paths
  have hp : 4*ε < P.top.width := by linarith
  have H := Rate.const (G:=G) (L:=L) (1:ℝ)
  let f:= -(15/16:ℝ)
  have hx₁:= (Rate.power (G:=G) (L:=L) (a:=3/8)).mul (Rate.power (a:=f)) s (by unfold f; linarith only [hm])
  have hx₂:= ((Rate.power (G:=G) (L:=L) (a:=3/8)).pow (n₀+2)).mul (Rate.power (a:=-(n₀:ℝ)-2)) s (by push_cast; linarith [hm])
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hx₁,hx₂,hn L (le_sup_left.trans hL) f r' (by dsimp [f]; linarith), hH L (le_sup_right.trans hL) P' f (by unfold f; norm_num), atoms_meet G L 3 l he ha hp ht hr (r:=s) (by push_cast; linarith),
    atoms_meet G L 4 l he ha hp ht hr (r := f) (by unfold f; push_cast; linarith),
    atoms_meet G L 2 l he ha hp H (loopBill_rate G L) (r:=f) (by unfold f; push_cast; linarith),
    tails_meet G L L 1 l (s:=P.top.clip) (C:=P.top.paths) he (by decide) ha hy ht (-(n₀:ℝ)-2),
    tails_meet G L scaleOne L.val l (s:=P.below.clip) (C:=P.below.paths) he L.property ha hz ht (-(n₀:ℝ)-2),
    ((Rate.power (G:=G) (L:=L) (a:=s)).mul_left 6) r hs] with x hA hv hz hb hB hc hq hK hU hD h
  intro c f S T R hS hR Y hY
  let p := S.ratio
  have hl : p.count = L := hS
  obtain ⟨-,b,-,-,H3,H4⟩ := hb S T R hS hR
  obtain ⟨w,H1,H2⟩:= hB c f S T R hS hR Y hY
  let θ := -orientation*R.beta
  have ho : |-orientation|≤1 := by rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2
  obtain ⟨hlh,hy'⟩ := hR.window
  have hθ : |θ| ≤ 2*betaF G x L := by
    rw [← hS]; unfold θ; rw [abs_mul, abs_of_nonneg hR.positive.le]
    exact le_trans (mul_le_of_le_one_left hR.positive.le ho) hy'
  have hpaths := hR.cap.paths
  have hF : R.p.threshold = fiery G x L := by rw [hR.received.temp,hS]
  obtain ⟨w₁,e₁,B₁⟩ := hc c f p hl R.path.cubic hpaths.three θ hθ R.p hF
  obtain ⟨w₂,e₂,B₂⟩ := hq c f p hl R.path.quartic hpaths.four θ hθ R.p hF
  rw [hS] at hpaths
  obtain ⟨w₀,e₀,B₀⟩ := hK c f p hl R.path.loop hpaths.two (-orientation) ho R.p hF
  have hu : R.clip = P.top.clip := hR.received.clip.trans hR.ready.high
  rw [hu] at hpaths
  obtain ⟨w₃,e₃,B₃⟩ := hU c f p hl R.path _ hpaths θ hθ
  obtain ⟨_,_,_,hk⟩ := hR.ready.feeds
  obtain ⟨w₄,e₄,B₄⟩ := hD c c (atOne _) rfl T.down _ hk (-θ) (by simpa only [abs_neg] using hθ)
  let z := Sum.elim w (Sum.elim w₁ (Sum.elim w₂ (Sum.elim w₀ (Sum.elim w₃ w₄))))
  let X:=grow G L x
  have hp:1≤ X:= Real.one_le_rpow hA (by norm_num); have hkX:=zero_le_one.trans hp
  have h1:X*betaF G x L ^ (-(15/16):ℝ) ≤ betaF G x L ^ s:= (le_abs_self _).trans hv
  have h2:X^(n₀+2)*betaF G x L ^ (-(n₀:ℝ)-2)≤betaF G x L ^ s:= (le_abs_self _).trans hz
  have hHg:= (Sales.together ((boost_price H2 hkX).raise h1) (B₁.together (((boost_price B₂ hkX).raise h1).together
    (((boost_price B₀ hkX).raise h1).together (((boost_price B₃ (pow_nonneg hkX (n₀+2))).raise h2).together ((boost_price B₄ (pow_nonneg hkX (n₀+2))).raise h2))))))
  refine ⟨z,?_,?_,b,H3,H4⟩
  · intro U V i
    rcases i with i| (i | (i | (i | (i | i))))
    · dsimp only [z,expo,Sum.elim]; rw [abs_neg]; exact H1 i U
    · exact e₁ ..
    · exact e₂ ..
    · exact e₀ ..
    · dsimp only [expo,z,Sum.elim]; rw [hu]; exact e₃ ..
    dsimp only [expo,z,Sum.elim]
    rw [hR.ready.low,hS]; exact e₄ ..
  convert hHg.raise (hg:=show _ ≤ betaF G x L^r from ?_) using 1
  · rfl
  · funext i; rcases i with i|i|i|i|i|i <;> simp [z,chargeN,X,wool]; ring
  · rfl
  linarith only [h,le_abs_self (6*betaF G x L^s)]

end YM.ConnectedActivityE6.Raw
