import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Horns
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}

open PhysicalNext.Repeat.Height

/-! # All requested powers and distinction on already accounted residual E heads.
Does not modify sector measure or profile charts; only changes budget proofs.
Bills are taken from actual masked inputs; `Sealed` only asks additional sum bounds
on the stated capacities of actual E entries. Modified from Census/* & Receiving. -/
structure Sealed (b : ℕ→ℝ)(R:Rep G f)(x:ℝ): Prop where
 ink : ∃ τ:ℕ→ℝ, (∀ i,R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support (R.activities.E i) (τ i)) ∧ ∀ u:Site f, SumBudget (fun i=> if (R.activities.reg i).site=u then R.p.mass (R.activities.reg i).support ((b*τ) i) else 0) x
private lemma pillarL (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0 < ε)
    (ha : 0 ≤ a) (hr : 4*ε < P.top.supportExponent) :
    ∃ n : ℕ, ∀ (c f : Side) (p : Ratio c f), n ≤ p.count.val →
      reserve (P.top.supportExponent-2*ε) a (conversion p (l+5)) ε :=
  Fees.exponent (l+5) he ha (by linarith)

/-- Both classes of Activity on *their own* aperture. -/
lemma fathom (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a) (hr : 4*ε<P.top.supportExponent) :
    ∃ n : ℕ, ∀ L : Side, n≤L.val → ∀ (u v : ℝ), -(11/10:ℝ)<u → ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L → Intake P T x R → ∀ (Ω:ℕ→ℝ), (∀ i:ℕ,(1:ℝ)≤Ω i) → Sealed Ω R (2*incomingE G L x) →
      let p := S.ratio; let B := radiusB x
      ∃ E K : ℕ → ℝ, (∀ i U, |R.activities.regularOccurrence R.p i U| ≤ E i) ∧
        Sales B a ε (regularFoot p l B R) (Ω*E) (regularExtra R) ((betaF G x L)^u) ∧
        (∀ i U, |R.activities.K i U| ≤ K i) ∧ Sales B a ε (forcedFoot p l B R) K (forcedExtra R) ((betaF G x L)^v) := by
  obtain ⟨n,hn⟩ := pillarL P l he ha hr
  refine ⟨n,fun L hL u v hv => ?_⟩
  let J (x : ℝ) := extentCost (l+5) (radiusB x)
  let bill (x d : ℝ) := Footprint.payment (L.val^4) (J x) 0 ε 1 d a (preCost (l+5))
  have hk {r : ℝ} {z : ℝ → ℝ} (h : Rate G L r z) : Rate G L r (fun x => bill x (z x)) := by
    have hh : Rate G L 0 (fun x : ℝ => (J x:ℝ)) := by simpa [extentCost,J] using
      (Rate.transfers (G:=G) (L:=L) (l+5+20) 0)
    simpa only [zero_add,bill] using! Rate.payment (Rate.const 1) h hh (L.val^4) 0 ε a _
  filter_upwards [hk ((incomingE_rate G L).mul_left 2) u hv, hk (incomingK_rate G L (v-1)) v (by linarith),
    Fees.horizons G L l he ha (show 2*ε<P.top.supportExponent by linarith)] with x hx hy hh
  intro c f S T R hP hR s hs hg p B
  have hP' : p.count=L := hP
  obtain ⟨b,hw,h⟩ := hg.ink
  obtain ⟨d,hD,h'⟩ := hR.cap.labels.boundK
  refine ⟨b,d,fun i U => ?_,?_,fun i U => (hD i).2 _,?_⟩
  · by_cases he' : Healthy R.p.threshold (R.activities.reg i).support U
    · rw [Activities.regularOccurrence, masked_eq _ _ _ _ he']; exact (hw i).2 _ he' [] (Nat.zero_le _) (by simp)
    rw [Activities.regularOccurrence,masked_ne _ _ _ _ he',abs_zero]; exact (hw i).1
  · let Y i := (R.activities.reg i).support
    have H (i:ℕ): 0≤ (s*b) i:=mul_nonneg (zero_le_one.trans (hs i)) (hw i).1
    have hY : Anchored (fun i => (R.activities.reg i).site) (s*b) (regularExtra R) (P.top.supportExponent)
        (2*incomingE G L x) := by
      rw [hR.exponent]
      intro x; convert h x using 1; ext i; simp only [BudgetPoint.mass,regularExtra]; rw [mul_comm]
    have hm := Sales.anchored_sale (z := (s*b)) (l:=l+5) (M := R.p.B) p (fun i => (R.activities.reg i).site) (Y := Y)
      (fun i => (R.activities.reg i).anchor) hY (fun i => H i)
      (X:=regularFoot p l B R) (fun i => inspected_price p l B (Y i) hh.1) hh.1
      (by rw [hR.sizes,hP]; exact hh.2.1) (hn c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one
      (fun i => ⟨H i,by simp⟩)
    apply hm.raise; rw [hP']; exact (le_abs_self _).trans hx
  · let Y i := (R.activities.forced i).support
    choose o ho using fun i => (R.activities.forced i).inventory_ne
    have ht i : o i ∈ Y i := (R.activities.forced i).inventory_sup (ho i)
    have hk : Ac.Hit Y R.p.B d P.top.supportExponent (incomingK G L x) := by
      rw [hR.exponent]; rw [hP] at h'
      intro x; convert h' x using 1; ext i
      unfold Y BudgetPoint.mass; rw [mul_comm]
    have hm := Sales.anchored_sale (z := d) (l:=l+5) p o ht (Labels.anchor_weaker Y _ (fun i => (hD i).1) hk _ ht)
      (fun i => (hD i).1) (X:=forcedFoot p l B R) (fun i => inspected_price p l B (Y i) hh.1) hh.1
      (by rw [hR.sizes,hP]; exact hh.2.1) (hn c f p (hP'.symm ▸ hL)) 0 (C:=1) zero_le_one
      (fun i => ⟨(hD i).1,by simp⟩)
    apply hm.raise; rw [hP']; exact (le_abs_self _).trans hy

def stallA (k : ℕ) (c f : Side) : LogLetter c f → ℕ := Sum.elim (fun _=>1) (Sum.elim (fun _=>0) (Sum.elim (fun _=>1) (Sum.elim (fun _=>1) (Sum.elim (fun _=>k) fun _=>k))))

-- Plain distinction support. multiplicative on atoms.
def ule (u:ℕ→ℝ)(x:LogLetter c f) : ℝ := Sum.elim u (fun _=>1) x
lemma atleast (u:ℕ→ℝ)(h:∀ i,1≤u i)(x:LogLetter c f) : 1≤ule u x:= by rcases x with x|x; exact h x; exact le_rfl
-- stripping arbitrary price
lemma thinner {ι:Type*} {X:ι→Support c} {w u:ι→ℝ} {e:ι→ℕ} {a b γ : ℝ} {n:ℕ}
    (pu:∀ i,1≤u i) (h:Sales n a b X (fun i=> u i*w i) e γ): Sales n a b X w e γ:= by
  have hp i:0≤w i:= nonneg_of_mul_nonneg_right (h.nonneg i) (zero_lt_one.trans_le (pu i))
  convert! h.shift zero_le_one hp (fun i=> by simpa only [one_mul] using le_mul_of_one_le_left (hp i) (pu i)) using 1
  simp
/- Optional pre-census. Version of Raw.inherit_bills with grades. -/
theorem inherit_piers (k:ℕ) (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ r' : ℝ,
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R → ∀ Δ:ℕ→ℝ, (∀ i,1≤Δ i) → Sealed Δ R (2*incomingE G L x) →
      ∃ z : LogLetter c f → ℝ, (∀ U V i, |expo T x R U V i| ≤ z i) ∧
        Sales (radiusB x) a ε (space T l (radiusB x) R) (fun i=>grow G L x^stallA k c f i*(ule Δ i * z i)) (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) (betaF G x L ^ r') := by
  obtain ⟨n,hn⟩ := fathom P l he ha hx
  refine ⟨n,fun L hL r hv r' => ?_⟩
  obtain ⟨s,hm,hs⟩ := exists_between hv
  have ht := (Rate.hat (L:=L) (G:=G)).mul_left 2
  have hr := Rate.const (G:=G) (L:=L) P.top.paths
  have hp : 4*ε < P.top.width := by linarith
  have H := Rate.const (G:=G) (L:=L) (1:ℝ)
  let f:= -(15/16:ℝ)
  have hx₁:= (Rate.power (G:=G) (L:=L) (a:=3/8)).mul (Rate.power (a:=f)) s (by unfold f; linarith only [hm])
  have hx₂:= ((Rate.power (G:=G) (L:=L) (a:=3/8)).pow k).mul (Rate.power (a:=-(k:ℝ)-1)) s (by push_cast; linarith only [hm, Nat.cast_nonneg (α:=ℝ) k])
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hx₁,hx₂,hn L hL f r' (by dsimp [f]; linarith), atoms_meet G L 3 l he ha hp ht hr (r:=s) (by push_cast; linarith),
    atoms_meet G L 4 l he ha hp ht hr (r := f) (by unfold f; push_cast; linarith),
    atoms_meet G L 2 l he ha hp H (loopBill_rate G L) (r:=f) (by unfold f; push_cast; linarith),
    tails_meet G L L 1 l (s:=P.top.clip) (C:=P.top.paths) he (by decide) ha hy ht (-(k:ℝ)-1),
    tails_meet G L scaleOne L.val l (s:=P.below.clip) (C:=P.below.paths) he L.property ha hz ht (-(k:ℝ)-1),
    ((Rate.power (G:=G) (L:=L) (a:=s)).mul_left 6) r hs] with x hA hv hz hb hc hq hK hU hD h
  intro c f S T R hS hR Δ hΔ hlΔ
  let p := S.ratio
  have hl : p.count = L := hS
  obtain ⟨w,b,H1,H2,H3,H4⟩ := hb S T R hS hR Δ hΔ hlΔ
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
  have h2:X^k*betaF G x L ^(-(k:ℝ)-1)≤betaF G x L ^ s:= (le_abs_self _).trans hz
  have hHg:= (Sales.together ((boost_price H2 hkX).raise h1) (B₁.together (((boost_price B₂ hkX).raise h1).together
    (((boost_price B₀ hkX).raise h1).together (((boost_price B₃ (pow_nonneg hkX k)).raise h2).together ((boost_price B₄ (pow_nonneg hkX k)).raise h2))))))
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
  · funext i; rcases i with i|i|i|i|i|i <;> simp [z,ule,stallA,X]
  · rfl
  linarith only [h,le_abs_self (6*betaF G x L^s)]

end YM.ConnectedActivityE6.Raw
