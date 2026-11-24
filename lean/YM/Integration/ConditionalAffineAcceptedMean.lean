import YM.Integration.ConditionalAffineMeanTariff
import YM.Integration.ConditionalAffineRegularMean

/-! A purchased local mean, independently rooted at any one original physical position. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ConditionalAffineAcceptedMean
open Function Filter Set Lattice Wilson RG Precision Tree Matrix Bloch Push.SectorMeasure
open Pressure Pressure.Tube Pressure.Stores FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Stars
open PhysicalNext.Repeat.Greenbelt ConditionalTreeCovarianceJets ConditionalTreeCovarianceSums ConditionalCovarianceCutoff
open ConditionalAffineMeanPrice ConditionalAffineLoadPrices
open PhysicalAffineScalarAperture (noHole)
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Genuine one-ended jet in the common pre-tree fine color alphabet. -/
def entry (T : Tube G S) (x : ℝ) (k : S.Choices) (r : Reserve S) (q : Chi) (ε : ℝ)
    (Y : LinkArray G (Frozen (noHole S) x (allot r))) {j : ℕ} (i : raw G f) (l : Fin j→ raw G c) :=
  iteratedFDeriv ℝ j (column (ConditionalAffineMeanDifference.error T x k r q ε Y)) 0 (ray G c∘l) i ()

def kernel (T : Tube G S) (x : ℝ) (k : S.Choices) (r s : Site c→Reserve S) (q : Chi) (ε : ℝ)
    (Y : ∀ z, LinkArray G (Frozen (noHole S) x (allot (r z))))
    (Z : ∀ z, LinkArray G (Frozen (noHole S) x (allot (s z)))) {j : ℕ}
    (i : raw G f) (z : Site c) (l : Fin j→ raw G c) :=
  entry T x k (s z) q ε (Z z) i l-entry T x k (r z) q ε (Y z) i l

/-- Differentiation commutes with this physical change of free charts once
both curves are measured in the genuine deposited fine alphabet. -/
theorem kernel_of_smooth (T : Tube G S) (x : ℝ) (k : S.Choices) (r s : Site c→Reserve S) (q : Chi) (ε : ℝ)
    (Y : ∀ z, LinkArray G (Frozen (noHole S) x (allot (r z))))
    (Z : ∀ z, LinkArray G (Frozen (noHole S) x (allot (s z)))) {j : ℕ}
    (i : raw G f) (z : Site c) (l : Fin j→ raw G c)
    (hs : ContDiffAt ℝ j (column (ConditionalAffineMeanDifference.error T x k (s z) q ε (Z z))) 0)
    (hr : ContDiffAt ℝ j (column (ConditionalAffineMeanDifference.error T x k (r z) q ε (Y z))) 0) :
    kernel T x k r s q ε Y Z i z l =
      iteratedFDeriv ℝ j (column (fun B => ConditionalAffineMeanDifference.error T x k (s z) q ε (Z z) B-
        ConditionalAffineMeanDifference.error T x k (r z) q ε (Y z) B)) 0 (ray G c∘l) i () := by
  let A := column (ConditionalAffineMeanDifference.error T x k (s z) q ε (Z z))
  let D := column (ConditionalAffineMeanDifference.error T x k (r z) q ε (Y z))
  change _ = iteratedFDeriv ℝ j (A-D) 0 (ray G c∘l) i ()
  rw [iteratedFDeriv_sub_apply hs hr]; rfl

/-- The quantified source, geometry and exponent precede the periodic torus, its
forest, its exterior-independent Gaussian aperture and every varied tag. -/
theorem joint_smooth (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) :
    ∃ γ C κ : ℝ, 0<γ ∧ 0<C ∧ 0<κ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
      100*(1+radiusB x)≤c.val → ∀ (k : S.Choices) (r s : Site c→Reserve S),
      (∀ z w, w≠z → r z w=s z w) → ∀ (q : Chi) (ε : ℝ)
      (Y : ∀ z, LinkArray G (Frozen (noHole S) x (allot (r z))))
      (Z : ∀ z, LinkArray G (Frozen (noHole S) x (allot (s z)))),
      ∀ j : ℕ, j≤n → ∀ y : Site c,
      NearStar j (taxi c) (home S) id hearth y (visitors S y) γ
        (C*Real.exp (-κ*(radiusB x:ℝ))) (kernel T x k r s q ε Y Z) ∧
      (∀ j₀ : ℕ, j₀+1≤n →
        NearStar j₀ (taxi c) (home S) hearth hearth y (ConditionalAffineRegularMean.visit S y) γ
          (C*Real.exp (-κ*(radiusB x:ℝ))) (fun i a l => iteratedFDeriv ℝ (j₀+1)
            (column (ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y)))
            0 (ray G c ∘ Fin.cons a l) i ())) ∧
      ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y) 0=0 ∧
      ContDiffAt ℝ n (column (ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y))) 0 := by
  obtain ⟨u,N,D,D',hu,hN,hD,hD',pay⟩ := charges G P Pt hp n
  let w := width G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width
  have hw : 0<w := (gauged G P Pt.bind Pt.top.clip (n+1) Pt.top.width_pos Pt.top.paths_pos.le).pos
  let δ := min u (w/(n+1:ℕ))
  have hδ : 0<δ := lt_min hu (div_pos hw (by positivity))
  have hwu : ((n+1:ℕ):ℝ)*δ≤w := by
    rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp (min_le_right ..)
  let γ := δ/(2*((n+3:ℕ):ℝ))
  have hγ : 0<γ := div_pos hδ (by positivity)
  let κ := ConditionalAffineMeanTariff.rate G P Pt n
  have hκ : 0<κ := ConditionalAffineMeanTariff.rate_pos P Pt n
  let V := torusPay (Co P.L (PAC G 1)) δ
  let A := census G P.L γ
  let Q := max 1 A
  let F := ConditionalAffineMeanTariff.coefficient G P Pt n D D'
  let C := Q*Q*Q^n*((2:ℝ)^n*((1+V)*(1+|F|)))
  have hV : 0≤V := torusPay_nn _ _ hδ
  have hQ : 1≤Q := le_max_left ..
  have hA : 0≤A := (torusPay_nn (Co P.L (PAC G 1)) γ hγ).trans (le_max_left ..)
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨γ/4,C,κ,div_pos hγ (by norm_num),hC,hκ,?_⟩
  filter_upwards [pay,ConditionalAffineMeanTariff.shield G P Pt n hN.le hD.le hD'.le,
    Work.E01.radiusB_tendsto.eventually_ge_atTop (max 100000 (macroR P)),eventually_gt_atTop (1:ℝ)] with x hx hmoney hrad hβ
  intro c f S T hS hT hs k r s h q ε Y Z j hj y
  have h100 : 100000≤radiusB x := (le_max_left ..).trans hrad
  have hρ : 0<temp x := Work.E09.temp_pos (zero_lt_one.trans hβ)
  have hfund := hx S T hS hT hs hρ (allot (r y)) k
  have hkernel : S.patch.Branches S.kernel G := hT.knobs.symm ▸ hT.kernel
  have hbox : 100*macroR S.patch≤f.val := by
    rw [hS,S.ratio.exact_size]
    refine le_trans ?_ (Nat.le_mul_of_pos_right _ S.ratio.count.property)
    have h' := (le_max_right 100000 (macroR P)).trans hrad
    omega
  have he : Bid.Larger (G:=G) S := ⟨hkernel,hbox,by omega⟩
  obtain ⟨b,y₀,H₁,H₂⟩ := hT.feeds
  have hb : T.up.Bounds T.high Pt.top.width Pt.top.paths b := by rw [hT.high]; exact H₁
  have hh : ((n+1:ℕ):ℝ)*δ≤width G S.patch S.kernel T.high (n+1) Pt.top.paths Pt.top.width := by
    rw [hS,hT.knobs,hT.high]; exact hwu
  let B := (radiusB x:ℝ)
  let M := windowPrice G P Pt.bind Pt.top.clip (n+1) Pt.top.paths Pt.top.width 0 (radiusB x/60:ℕ) +
    diminish G P Pt.bind Pt.top.clip (n+1) (till x) Pt.top.paths Pt.top.width 0
  let J := ConditionalAffineMeanTariff.invFee G P Pt n
  let U := ordinaryFee G P Pt n N D D' x
  let E := tailFee G P Pt n N D D' x
  have hfire : 0≤fiery G x P.L := by unfold fiery temp; positivity
  have hU : 0≤U := by dsimp [U,ordinaryFee,fullFee,sourceFee,jacFee]; positivity
  have hE : 0≤E := by dsimp [E,tailFee,fullFee,sourceFee,jacFee,jacTail]; positivity
  have hw₀ := window_price_nonneg (G:=G) (S:=S) (p:=T.high) (n:=n+1) (R:=(radiusB x/60:ℕ)) Pt.top.width_pos Pt.top.paths_pos.le (le_refl 0)
  have hd₀ := cut_nonneg (G:=G) (S:=S) (p:=T.high) (n:=n+1) Pt.top.width_pos Pt.top.paths_pos.le (le_refl 0) (till x)
  have hM : 0≤M := by dsimp [M]; rw [hS,hT.knobs,hT.high] at hw₀ hd₀; exact add_nonneg hw₀ hd₀
  have hf := ConditionalAffinePanelWindow.funded (G:=G) (S:=S) (p:=T.high) (n:=n+1) (u:=0)
    Pt.top.width_pos Pt.top.paths_pos.le (radiusB x) h100
  dsimp only at hf
  rw [hS,hT.knobs,hT.high] at hf
  have hmw : M≤ConditionalAffineMeanTariff.wFee G P Pt n*Real.exp (-ConditionalAffineMeanTariff.panelRate G P Pt n*B) := by
    apply (show M≤_*Real.exp (-ConditionalAffineMeanTariff.panelRate G P Pt n*B) from by
      simpa [M,B,ConditionalAffineMeanTariff.panelRate,till,drain] using hf.2).trans
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
  have hm : M*U+J*E≤F*Real.exp (-κ*B) := hmoney M hM hmw
  have hz := ConditionalAffineMeanPrice.positions (T:=T) (k:=k) r s h q ε Y Z he Pt.top.width_pos Pt.top.paths_pos.le hb
    (by omega) n hδ hU hE hh
    (hfund.1.weaken (min_le_left ..) le_rfl) (hfund.2.weaken (min_le_left ..) le_rfl) j hj y
  have hinv : 0≤J := by dsimp [J,ConditionalAffineMeanTariff.invFee]; positivity
  have htotal : 0≤M*U+J*E := add_nonneg (mul_nonneg hM hU) (mul_nonneg hinv hE)
  have hm' : M*U+J*E≤(1+|F|)*Real.exp (-κ*B) :=
    hm.trans (mul_le_mul_of_nonneg_right ((le_abs_self F).trans (by linarith)) (Real.exp_pos _).le)
  have common (t : ℕ) (ht : t≤n) :
      Q*Q*Q^t*((2:ℝ)^n*((M*U+J*E)*(1+V)))≤C*Real.exp (-κ*B) := by
    calc
      _ ≤ Q*Q*Q^n*((2:ℝ)^n*(((1+|F|)*Real.exp (-κ*B))*(1+V))) := by
        gcongr
      _ = _ := by dsimp [C]; ring
  have charged (w : Reserve S) (W : LinkArray G (Frozen (noHole S) x (allot w))) :=
    ConditionalAffineRegularMean.charged T k w q ε W he Pt.top.width_pos Pt.top.paths_pos.le hb (by omega) n
      hδ hU hE hh (hfund.1.weaken (min_le_left ..) le_rfl) (hfund.2.weaken (min_le_left ..) le_rfl)
  have hk : (kernel T x k r s q ε Y Z (j:=j)) = (fun i z l =>
      iteratedFDeriv ℝ j (column (fun B => ConditionalAffineMeanDifference.error T x k (s z) q ε (Z z) B-
        ConditionalAffineMeanDifference.error T x k (r z) q ε (Y z) B)) 0 (ray G c∘l) i ()) := by
    funext i z l
    exact kernel_of_smooth T x k r s q ε Y Z i z l
      (TestD.smooth_of_le (charged (s z) (Z z)).smooth hj) (TestD.smooth_of_le (charged (r z) (Y z)).smooth hj)
  rw [hk]
  refine ⟨⟨hz.limit.trans ?_⟩,?_,ConditionalAffineRegularMean.flat T k (r y) q ε (Y y) he Pt.top.width_pos Pt.top.paths_pos.le hb (by omega),(charged (r y) (Y y)).smooth⟩
  · rw [hS,hT.knobs,hT.high]
    change A*A*A^j*((2:ℝ)^j*(M*U*V+J*E*V)) ≤ _
    rw [←add_mul]
    apply le_trans _ (common j hj)
    gcongr <;> first | exact le_max_right .. | exact hj | linarith
  · intro j₀ hj₀
    have hsC := charged (r y) (Y y)
    have hsource : Paid (home S) δ ((2:ℝ)^n*(M*U+J*E)) n (ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y)) := by
      apply hsC.weaken (le_refl δ)
      rw [hS,hT.knobs,hT.high]
      gcongr
      exact le_rfl
    have hh := ConditionalAffineRegularMean.positions hδ (mul_nonneg (by positivity) htotal) hsource j₀ hj₀ y
    refine ⟨hh.limit.trans ?_⟩
    rw [hS]
    let Z := max (torusPay (Co P.L (PAC G 1)) γ) (torusPay (PAC G 1) γ)
    have hZ : 0≤Z := (torusPay_nn (PAC G 1) γ hγ).trans (le_max_right ..)
    have hZQ : Z≤Q := (max_le (le_max_left ..) ((le_max_right ..).trans (le_max_right ..))).trans (le_max_right ..)
    change Z*Z*Z^j₀*((2:ℝ)^n*(M*U+J*E)) ≤ _
    apply le_trans _ (common j₀ (by omega))
    gcongr
    first | exact hZQ | nlinarith

/-- Position and one-parent projections of the same original smooth purchase. -/
theorem joint (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) :
    ∃ γ C κ : ℝ, 0<γ ∧ 0<C ∧ 0<κ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
      100*(1+radiusB x)≤c.val → ∀ (k : S.Choices) (r s : Site c→Reserve S),
      (∀ z w, w≠z → r z w=s z w) → ∀ (q : Chi) (ε : ℝ)
      (Y : ∀ z, LinkArray G (Frozen (noHole S) x (allot (r z))))
      (Z : ∀ z, LinkArray G (Frozen (noHole S) x (allot (s z)))),
      ∀ j : ℕ, j≤n → ∀ y : Site c,
      NearStar j (taxi c) (home S) id hearth y (visitors S y) γ
        (C*Real.exp (-κ*(radiusB x:ℝ))) (kernel T x k r s q ε Y Z) ∧
      (∀ j₀ : ℕ, j₀+1≤n →
        NearStar j₀ (taxi c) (home S) hearth hearth y (ConditionalAffineRegularMean.visit S y) γ
          (C*Real.exp (-κ*(radiusB x:ℝ))) (fun i a l => iteratedFDeriv ℝ (j₀+1)
            (column (ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y)))
            0 (ray G c ∘ Fin.cons a l) i ())) ∧
      ConditionalAffineMeanDifference.error T x k (r y) q ε (Y y) 0=0 := by
  obtain ⟨γ,C,κ,hγ,hC,hκ,H⟩ := joint_smooth G P Pt hp n
  refine ⟨γ,C,κ,hγ,hC,hκ,H.mono fun x hx => ?_⟩
  intro c f S T hS hT hs k r s h q ε Y Z j hj y
  have hy := hx S T hS hT hs k r s h q ε Y Z j hj y
  exact ⟨hy.1,hy.2.1,hy.2.2.1⟩


theorem positions (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) (n : ℕ) :
    ∃ γ C κ : ℝ, 0<γ ∧ 0<C ∧ 0<κ ∧ ∀ᶠ x : ℝ in atTop,
      ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T →
      100*(1+radiusB x)≤c.val → ∀ (k : S.Choices) (r s : Site c→Reserve S),
      (∀ z w, w≠z → r z w=s z w) → ∀ (q : Chi) (ε : ℝ)
      (Y : ∀ z, LinkArray G (Frozen (noHole S) x (allot (r z))))
      (Z : ∀ z, LinkArray G (Frozen (noHole S) x (allot (s z)))),
      ∀ j : ℕ, j≤n → ∀ y : Site c,
      NearStar j (taxi c) (home S) id hearth y (visitors S y) γ
        (C*Real.exp (-κ*(radiusB x:ℝ))) (kernel T x k r s q ε Y Z) := by
  obtain ⟨v,C,κ,hv,hC,hκ,H⟩ := joint G P Pt hp n
  refine ⟨v,C,κ,hv,hC,hκ,H.mono fun x hx => ?_⟩
  intro c f S T hS hT hs k r s h q ε Y Z j hj y
  exact (hx S T hS hT hs k r s h q ε Y Z j hj y).1

end YM.Integration.ConditionalAffineAcceptedMean
