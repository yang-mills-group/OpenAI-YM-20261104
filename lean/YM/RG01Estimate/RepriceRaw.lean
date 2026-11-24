import YM.RG01Estimate.InheritedSales

/-! Construct new Eager witnesses, instead of assuming an estimate on short
real occurrences after dropping the masked or long-tail contributions. Keep
the projection metric and sum over both Pair families (before cancelling).
Vary along a Mode with *fixed U* for these nonsmooth inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Inherit

open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Coat Raw
open Blaze Brush Scroll Vine Polar Frond Silica Clutch
open Push.AbsoluteSums.Footprint
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

-- arbitrary weights with Rate cap -- note extra ε export to both V and U pair families.
variable {G : Gauge} (P : Teller G) (l : ℕ) {α A v t t' η σ W s b μ : ℝ}

-- adapt absolute path sales to uniform larger weights for the long-pair rows; E gets a sharp price.
theorem priors {a ε : ℝ} (hp : 0 < ε) (ha : 0≤a) (hr : 4*ε < P.top.supportExponent) (ht : 8*ε < P.top.width)
    (hy : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n≤L.val → ∀ (u v w p:ℝ), -(1/2:ℝ)<p → u+v<p →
    ∀ (X E K f g : ℝ→ℝ), Rate G L u X → Rate G L v E → Rate G L w K →
      (∀ᶠ x in atTop,1 ≤ E x) → (∀ᶠ x in atTop,1 ≤ K x) →
      Rate G L (-(1/2:ℝ)) f → Rate G L (-(1/2:ℝ)) g →
    ∀ (χ : Chi) (i : ℕ) (c : ℝ), ∃ B : ℝ→ℝ, Rate G L 0 B ∧ (∀ x, 0 ≤ B x) ∧
    ∀ᶠ s : ℝ in atTop, ∀ (n m : Side) (S : StepData n m) (T : Tube G S) (R : Rep G m),
      S.patch.L=L → Intake P T s R → ∀ Y : Set ℕ, Debits R Y (X s) →
        ∃ w : Raw.LogLetter n m → ℝ,
          let o:= Raw.space T l (radiusB s) R
          let e:= Raw.extra T R
          Sales (radiusB s) a ε o (fun i=>weight n m Y (E s) (K s) i*w i) e (betaF G s L^p) ∧
          ∀ (F : Forest S.ratio) (X : Coat T F) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
            (A : Config G m) (V:E→ Config G n) (Y:E→ Directions G m) (q:E) (W:E→ Air m G) (t:Air m G),
            X.x=s → X.χ=χ → Mode V q i (f s) → Clutch X t c R.beta (g s) q i V Y W →
              ∀ j, Brush i (w j) (B s*(coverNumber (radiusB s) (o j)+(e j:ℝ)))
                (fun y=> frost (vary X (V y)) c R (Y y) A j) q := by
  obtain ⟨n,hn⟩:= core_bills P l hp ha hr; obtain ⟨m,hM⟩:= project P l hp ha hr
  refine ⟨max n m, fun L hL u v w p h hu X E K f g hx he hk hE hK hf hg χ i c=>?_⟩
  obtain ⟨s,hs,hs'⟩:= exists_between (show max (-(1/2:ℝ)) (u+v)<p from max_lt h hu)
  have hx': u<s-v:= by linarith only [hs,le_max_right (-(1/2:ℝ)) (u+v)]
  have hy' : -(1/2:ℝ)<s:=lt_of_le_of_lt (le_max_left _ _) hs
  obtain ⟨q,hq,hD,hV⟩:= Clutch.dicers P L (w:=s-w) (by norm_num) ha hp hy hf i l
  obtain ⟨U,hU,hU',hH⟩:= Clutch.central G L χ i hg (2*c)
  let ℓ s':= q s'+U s'
  have hl : Rate G L s (fun x=> betaF G x L ^ s) := Rate.power
  have hx₁ : Rate G L s (fun x=> E x * betaF G x L ^ (s-v)):= by
    have he := he.mul (Rate.power (a:=s-v)); rw [show v+(s-v)=s by ring] at he; exact he
  have hx₂ : Rate G L s (fun x=> K x * betaF G x L ^ (s-w)):= by
    have he := hk.mul (Rate.power (a:=s-w)); rw [show w+(s-w)=s by ring] at he; exact he
  have hr₁ := (Rate.hat (L:=L) (G:=G)).mul_left 2; have hr₂ := Rate.const (G:=G) (L:=L) P.top.paths
  have ht' : 4*ε < P.top.width := by linarith
  have H := Rate.const (G:=G) (L:=L) (1:ℝ)
  refine ⟨ℓ,hq.add hU,fun i=>add_nonneg (hD _) (hU' _),?_⟩
  filter_upwards [hn L ((le_max_left ..).trans hL) s p (by linarith only [hy']),hM L ((le_max_right ..).trans hL) _ _ X hx hx',
    atoms_meet G L 3 l hp ha ht' hr₁ hr₂ (r:=s) (by push_cast; linarith only [hy']),
    atoms_meet G L 4 l hp ha ht' hr₁ hr₂ (r:=s) (by push_cast; linarith only [hy']),
    atoms_meet G L 2 l hp ha ht' H (loopBill_rate G L) (r:=s) (by push_cast; linarith only [hy']),
    tails_meet G L L 1 l (s:=P.top.clip) (C:=P.top.paths) hp (by decide) ha ht hr₁ (s-w), hE,hK,hV,hH,
    (((hx₁.add (hl.mul_left 4)).add (hx₂.mul_left 2)) p hs')]
    with x hb hv hc hq hJ hT he' heK hV hH h' n m S T R hL hR I hI
  let B := radiusB x
  obtain ⟨a',b,H₁,H₂,-,-⟩:= hb S T R hL hR
  obtain ⟨d,hd,hv⟩:= hv S T R hL hR I hI
  let e i:= if i∈I then d i else a' i
  have hL' : S.ratio.count=L:=hL
  have hdi : Sales B a ε (Raw.regularFoot S.ratio l (radiusB x) R) (fun i=> (sees I (E x) i)*e i) (Raw.regularExtra R)
      (E x*betaF G x L^(s-v)+betaF G x L^s) := by
    convert fee_cases (fee_times hv (zero_le_one.trans he')) H₂ (fun i=>i∈I) using 1
    funext i; unfold e sees; split; rfl; rw [one_mul]
  let t := -orientation*R.beta
  have hθ : |t| ≤ 2*betaF G x L:= by
    rw [← hL]; unfold t; rw [abs_mul, abs_neg, abs_of_nonneg orientation_range.1.le, abs_of_nonneg hR.positive.le]
    exact le_trans (mul_le_of_le_one_left hR.positive.le orientation_range.2) hR.window.2
  have hpaths:= hR.cap.paths
  have hF : R.p.threshold = fiery G x L := by rw [hR.received.temp,hL]
  obtain ⟨w₁,e₁,B₁⟩:= hc n m S.ratio hL' R.path.cubic hpaths.three t hθ R.p hF
  obtain ⟨w₂,e₂,B₂⟩:= hq n m S.ratio hL' R.path.quartic hpaths.four t hθ R.p hF
  rw [hL] at hpaths
  obtain ⟨w₀,e₀,B₀⟩:= hJ n m S.ratio hL' R.path.loop hpaths.two (-orientation)
    (show |-orientation|≤1 by rw [abs_neg,abs_of_nonneg orientation_range.1.le]; exact orientation_range.2) R.p hF
  have hu : R.clip = P.top.clip := hR.received.clip.trans hR.ready.high
  rw [hu] at hpaths
  obtain ⟨w₃,e₃,B₃⟩:= hT n m S.ratio hL' R.path _ hpaths t hθ
  obtain ⟨w₄,e₄,B₄⟩:= hV n m S T R hL hR
  let u := Sum.elim e (Sum.elim w₁ (Sum.elim w₂ (Sum.elim w₀ (Sum.elim w₃ w₄))))
  have hB:= hdi.together (B₁.together (B₂.together (B₀.together ((fee_times B₃ (zero_le_one.trans heK)).together
    (fee_times e₄ (zero_le_one.trans heK))))))
  let U0 := betaF G x L ^ s
  let K0 := K x * betaF G x L ^ (s-w)
  let E0 := E x * betaF G x L ^ (s-v)
  refine ⟨u,?_⟩; intro T₁ T₂
  refine ⟨?_,?_⟩
  · apply Sales.raise (γ:=E0 + U0 + (U0 + (U0 + (U0 + (K0 + K0)))))
    · convert hB using 1
      · rfl
      · funext i; rcases i with i|i|i|i|i|i <;> simp only [u,weight,Sum.elim,one_mul]
      · rfl
    calc
      _ = E0 + 4*U0 + 2*K0 := by ring
      _ ≤ _ := (le_abs_self _).trans h'
  intro F X J _ _ A V Y y W t' hX hφ hV hC j
  have hq' := hD x; have hQ := hU' x
  -- explicit equality at X.x
  have hv (o O : Support n) (ht : o⊆O) := hH n m S T F X hX hφ hL
    (show 0 < 2*c * X.t by rw [mul_assoc]; exact mul_pos (by norm_num) hC.pulse) J t' c R.beta y V Y W hC o O ht
  have hsub i : Raw.space T 0 X.B R i ⊆ Raw.space T l X.B R i:= by
    have h' {f n} (p : Ratio n f) (Y : Support f) : enlargement p 0 X.B Y ⊆ enlargement p l X.B Y :=
      Corona.halo_mono (by omega) (Subset.refl _)
    rcases i with i|i|i|i|i|i
    · exact h' _ _
    all_goals exact Finset.image_subset_image (h' _ _)
  have hZ i' : Brush i (u i') (q x*(Raw.extra T R i':ℝ)) (fun y=> nest T X.x (V y) A R i') y := by
    rw [hX]; rcases i' with i'|i'|i'|i'|i'|i'
    · change Brush _ (if i'∈ I then d i' else a' i') _ (fun (_:J)=> -(R.activities.regularOccurrence R.p i' A)) _
      have hE' := Brush.certified (k:=i) (E:=J) (x:=y) (mul_nonneg hq' (Nat.cast_nonneg (α:=ℝ) (Raw.extra T R (.inl i')))) (-(R.activities.regularOccurrence R.p i' A))
      rw [norm_neg,Real.norm_eq_abs] at hE'
      split
      next hh => exact hE'.climb (hd i' hh A) le_rfl
      next => exact hE'.climb (H₁ i' A) le_rfl
    · exact (Brush.certified (mul_nonneg hq' (Nat.cast_nonneg _)) _).climb (e₁ i' A) le_rfl
    · exact (Brush.certified (mul_nonneg hq' (Nat.cast_nonneg _)) _).climb (e₂ i' A) le_rfl
    · exact (Brush.certified (mul_nonneg hq' (Nat.cast_nonneg _)) _).climb (e₀ i' A) le_rfl
    · have h := e₃ i' R.p.threshold A; rw [←hu] at h
      exact (Brush.certified (mul_nonneg hq' (Nat.cast_nonneg _)) _).climb h le_rfl
    · have hk := B₄ J y V hV i'; rw [← hL] at hk
      -- rewrite affected V x?
      exact hk
  have hX' : Brush i (u j*1) (q x*(Raw.extra T R j:ℝ) + U x*(coverNumber X.B (Raw.space T l X.B R j)))
      (fun y=> frost (vary X (V y)) c R (Y y) A j) y:= (hZ j).paints (hv _ _ (hsub j))
  apply hX'.climb (mul_one _).le
  let F:ℝ:= Raw.extra T R j
  have hc : X.B=radiusB x:= congr_arg radiusB hX
  rw [hc]; change q x* F + U x*_ ≤ (q x+U x)*_
  nlinarith only [hq',hQ,show 0 ≤ F from Nat.cast_nonneg _,Nat.cast_nonneg (α:=ℝ) (coverNumber (radiusB x) (T₁ j))]

end YM.RG01Estimate.Inherit
