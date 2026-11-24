import YM.RGComparison01.Tithe

/-!
# Reserve on true RG optional exponents

A simultaneous price (on growth, arity and long paths/profile, with a
chosen E ticket). At the width-support demand of the actual output
bill. Vital: `Ticket` on E is consumed *only* on original reads of those
terms; mask failures with their seed footprints to be separately covered. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Tithe
open Function Filter Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Push.AbsoluteSums.Footprint
open Precision Exterior Next.Fluctuations SectorMeasure Oriented Reserves
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open PhysicalNext PhysicalNext.Repeat PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G}
    {T : Tube G S} {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : RG.Rep G f} {μ q C' d v Y A b r B s α a i : ℝ}
    {k j n ℓ : ℕ} {χ : Chi} {H : Cash W s μ L Q o α T R}

-- Extra multiplier profile

/-- "Bill." Retain the original fugacity estimates (e.g. `grow`, `horn`)
as well. Page `t` on *both* Pairs path tails. -/
def page (c f : Side) (V : ℕ → ℝ) (t : ℝ) : LogLetter c f → ℝ :=
    Sum.elim V (Sum.elim (fun _=>1) (Sum.elim (fun _=>1) (Sum.elim (fun _=>1) fun _=>t)))

def bill (c f : Side) (V : ℕ → ℝ) (t d : ℝ) (i : LogLetter c f) := page c f V t i * d ^ Raw.extraA c f i
lemma page_ge (V : ℕ → ℝ) (t : ℝ) (h : 1 ≤ t) (hv : ∀ i, 1 ≤ V i) (p : LogLetter c f) : 1 ≤ page c f V t p := by
  rcases p with p|p|p|p|p; exact hv _; exact le_rfl; exact le_rfl; exact le_rfl; exact h
lemma bill_ge {V : ℕ → ℝ} {t d : ℝ} (h : 1 ≤ t) (hv : ∀ i,1 ≤ V i) (hd : 1 ≤ d) (p : LogLetter c f) :
    1 ≤ bill c f V t d p := one_le_mul_of_one_le_of_one_le (page_ge V t h hv p) (one_le_pow₀ hd)

-- conservatively pay t arbitrary fixed grow-power
open Height
lemma scale_bought (G : Gauge) (L : Side) (l k : ℕ) (u : ℝ) : ∃ r : ℝ, r<0 ∧ ∀ᶠ x in atTop,
    (grow G L x ^ l * grow G L x ^ k) * betaF G x L ^ r ≤ betaF G x L ^ u := by
  obtain ⟨r,hr⟩ := exists_lt (min (0:ℝ) (u-((3/8:ℝ)*l+(3/8:ℝ)*k)))
  obtain ⟨hr,hv⟩:= lt_min_iff.mp hr
  have hp : Rate G L (3/8) (grow G L) := Rate.power
  exact ⟨r,hr,((((hp.pow l).mul (hp.pow k)).mul (Rate.power (a:=r))) u (by linarith)).mono (fun x hx=> (le_abs_self _).trans hx)⟩

/-- Enhanced census, simultaneously room in arity and pair tails. Choose lower floor on L
 BEFORE `P` applied to intake clocks. -/
theorem first_sales (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ (r' : ℝ) (k : ℕ),
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R → ∀ V : ℕ → ℝ, Ticket R.activities R.p V (2 * incomingE G L x) →
      ∃ z : LogLetter c f → ℝ, (∀ U W i, |expo T x R U W i| ≤ z i) ∧
        Sales (radiusB x) a ε (space T l (radiusB x) R) (fun i=>bill c f V (grow G L x^k) (grow G L x) i*z i)
          (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) (betaF G x L ^ r') := by
  obtain ⟨n,hn⟩ := core_bills P l he ha hx
  obtain ⟨m,hm⟩ := shore P l he ha hx
  refine ⟨n+m,fun L hL r hv r' k => ?_⟩
  obtain ⟨s,hu,hs⟩ := exists_between hv
  have ht := (Rate.hat (L:=L) (G:=G)).mul_left 2
  have hr := Rate.const (G:=G) (L:=L) P.top.paths
  have hp : 4*ε < P.top.width := by linarith
  have H := Rate.const (G:=G) (L:=L) (1:ℝ)
  let f₀:= -(15/16:ℝ)
  have hq: -(11/10:ℝ)<f₀:= by norm_num [f₀]
  have hx₁:= (Rate.power (G:=G) (L:=L) (a:=3/8)).mul (Rate.power (a:=f₀)) s (by unfold f₀; linarith only [hu])
  obtain ⟨t,-,hv₀⟩ := scale_bought G L k 2 s
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hx₁,hv₀,hn L (by omega) f₀ r' hq,
    hm L (by omega) f₀ hq,
    atoms_meet G L 3 l he ha hp ht hr (r:=s) (by push_cast; linarith only [hu]),
    atoms_meet G L 4 l he ha hp ht hr (r:=f₀) (by unfold f₀; push_cast; linarith),
    atoms_meet G L 2 l he ha hp H (loopBill_rate G L) (r:=f₀) (by unfold f₀; push_cast; linarith),
    tails_meet G L L 1 l (s:=P.top.clip) (C:=P.top.paths) he (by decide) ha hy ht t,
    tails_meet G L scaleOne L.val l (s:=P.below.clip) (C:=P.below.paths) he L.property ha hz ht t,
    ((Rate.power (G:=G) (L:=L) (a:=s)).mul_left 6) r hs] with x hd hh h₁ hA hB hc hq' hK hU hD hh'
  intro c f S T R hS hR V hV
  let p := S.ratio; have hlu : p.count=L := hS
  obtain ⟨w,h,Qw⟩:= hB _ _ S T R hS hR V hV
  obtain ⟨-,b,-,-,H₃,H₄⟩ := hA S T R hS hR
  let θ := -orientation*R.beta
  have ho : |-orientation|≤1 := by rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2
  have hθ : |θ| ≤ 2*betaF G x L := by
    rw [← hS]; unfold θ; rw [abs_mul, abs_of_nonneg hR.positive.le]
    exact le_trans (mul_le_of_le_one_left hR.positive.le ho) hR.window.2
  have hpaths := hR.cap.paths
  have hF : R.p.threshold = fiery G x L := by rw [hR.received.temp,hS]
  obtain ⟨w₁,e₁,B₁⟩ := hc c f p hlu R.path.cubic hpaths.three θ hθ R.p hF
  obtain ⟨w₂,e₂,B₂⟩ := hq' c f p hlu R.path.quartic hpaths.four θ hθ R.p hF
  rw [hS] at hpaths
  obtain ⟨w₀,e₀,B₀⟩ := hK c f p hlu R.path.loop hpaths.two (-orientation) ho R.p hF
  have hb : R.clip = P.top.clip := hR.received.clip.trans hR.ready.high
  rw [hb] at hpaths
  obtain ⟨w₃,e₃,B₃⟩ := hU c f p hlu R.path _ hpaths θ hθ
  obtain ⟨_,_,_,hk⟩ := hR.ready.feeds
  obtain ⟨w₄,e₄,B₄⟩ := hD c c (atOne _) rfl T.down _ hk (-θ) (by simpa only [abs_neg] using hθ)
  let z := Sum.elim w (Sum.elim w₁ (Sum.elim w₂ (Sum.elim w₀ (Sum.elim w₃ w₄))))
  let X:=grow G L x
  have hp:1≤ X:= Real.one_le_rpow hd (by norm_num); have hkX:=zero_le_one.trans hp
  have h1:X*betaF G x L ^ f₀ ≤ betaF G x L ^ s:= (le_abs_self _).trans hh
  have h2:0≤ X^k*X^2 :=mul_nonneg (pow_nonneg hkX _) (pow_nonneg hkX _)
  have hHg:= (Sales.together ((boost_price Qw hkX).raise h1) (B₁.together (((boost_price B₂ hkX).raise h1).together
    (((boost_price B₀ hkX).raise h1).together (((boost_price B₃ h2).raise h₁).together ((boost_price B₄ h2).raise h₁))))))
  refine ⟨z,?_,?_,b,H₃,H₄⟩
  · intro U W i
    rcases i with i| (i | (i | (i | (i | i))))
    · dsimp only [z,expo,Sum.elim]; rw [abs_neg]
      by_cases hi : Healthy R.p.threshold (R.activities.reg i).support U
      · rw [Activities.regularOccurrence, masked_eq _ _ _ _ hi]; exact (h i).2 _ hi [] (Nat.zero_le _) (by simp)
      rw [Activities.regularOccurrence, masked_ne _ _ _ _ hi,abs_zero]; exact (h i).1
    · exact e₁ ..
    · exact e₂ ..
    · exact e₀ ..
    · dsimp only [expo,z,Sum.elim]; rw [hb]; exact e₃ ..
    dsimp only [expo,z,Sum.elim]
    rw [hR.ready.low,hS]; exact e₄ ..
  convert hHg.raise (hg:=show _ ≤ betaF G x L^r from ?_) using 1
  · rfl
  · funext i; rcases i with i|i|i|i|i|i <;> simp [bill,page,z,extraA,X]; ring
  · rfl
  linarith only [hh',le_abs_self (6*betaF G x L^s)]
end YM.RGComparison01.Tithe
