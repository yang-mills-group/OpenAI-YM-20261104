import YM.Integration.WilsonLimitConstruction.FundedDictionaryRenderPrices
import YM.Integration.FullQLocalNumericLogarithmicCost

/-! Uniform payment of the actual kernel, patch and fine-stage constants. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedDictionaryPatchPrices

open Filter Lattice Wilson RG RG.Supply Precision Marker FullQLocal FullQLocal.RenderedStep
open PhysicalNext PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Daisy.Charity.RG12
open ActualOriginalQCountableRequests FullQLocal.PreRun
open scoped Classical Topology BigOperators

variable {G : Gauge} {hG : G.Simple} {P : ActualQlocalRequestFamily.Recipe}

abbrev Cost := Patch → KernelChoices → Stage → ℕ → ℝ

def selected (C : Cost) (R : Run G) (m period k : ℕ) : ℝ :=
  let L := R.family.path.levels
  C (L.clock.op m period).patch L.clock.kernel (L.params (m+1)) k

private theorem patch_eq {X Y : Patch} (hL : X.L.val=Y.L.val) (hj : X.J=Y.J) : X=Y := by
  have hs : X.L=Y.L := Subtype.ext hL
  cases X
  cases Y
  cases hs
  cases hj
  rfl

/-- A patch has only its purchased block length and profile index as data. -/
def post (C : Cost) (s : Sheet G) (lengths : ℕ → ℕ) (k i : ℕ) : ℝ :=
  if h : ∃ D : Patch, D.L.val=lengths i ∧ D.J=i then
    C (Classical.choose h) s.kernel (s.profile i) k
  else 0

theorem sampled (C : Cost) (R : Run G) (s : Sheet G) (n : ℕ → ℕ)
    (sheet : R.metals.p = ThroughLaunch.raise s n) (m period k : ℕ) :
    let L := R.family.path.levels
    post C s (fun i => (L.clock.factor i).val) k (L.clock.J (m+1)) =
      selected C R m period k := by
  let L := R.family.path.levels
  let j := L.clock.J (m+1)
  let D := (L.clock.op m period).patch
  have hL : D.L = L.clock.factor j := by
    change (R.alloy.B.a.clock.op m period).patch.L = R.alloy.B.a.clock.factor _
    rw [R.alloy.B.valid.lengths]
    exact Push.PriceCompiler.block_eq R.alloy.B.valid m
  have hj : D.J=j := (Pressure.Testing.proceeds R.alloy.B (m+1) m period (Nat.lt_succ_self m)).atStep
  have found : ∃ E : Patch, E.L.val=(L.clock.factor j).val ∧ E.J=j :=
    ⟨D,congrArg Subtype.val hL,hj⟩
  have hD : Classical.choose found = D :=
    patch_eq ((Classical.choose_spec found).1.trans (congrArg Subtype.val hL).symm)
      ((Classical.choose_spec found).2.trans hj.symm)
  have hK : L.clock.kernel = s.kernel := by
    calc
      _ = R.metals.p.kernel := R.alloy.B.valid.kernel
      _ = _ := by rw [sheet]
  have hP : L.params (m+1) = s.profile j := by
    calc
      _ = R.metals.p.profile j := Push.PriceCompiler.params_eq R.alloy.B.valid (m+1)
      _ = _ := by rw [sheet]
  change post C s (fun i => (L.clock.factor i).val) k j =
    C D L.clock.kernel (L.params (m+1)) k
  rw [post,dif_pos found,hD,hK,hP]

theorem at_edge (C : Cost) {R : Run G} (S : CommonConstruction.CostDictionarySupply hG P R)
    (m period k : ℕ) :
    let L := R.family.path.levels
    post C S.purchase.sheet (fun i => (L.clock.factor i).val) k (L.clock.J (m+1)) =
      selected C R m period k :=
  sampled C R S.purchase.sheet S.purchase.n S.purchase.sheet_eq m period k

def Covered (C : Cost) (R : Run G) : Prop :=
  let L := R.family.path.levels
  ∀ k, ∀ᶠ m : ℕ in atTop, ∀ period,
    |selected C R m period k| ≤ 1+Real.log (Real.log (L.clock.hatBeta m)) ∧
    ∀ {V : Type} {J : Request V} (T : NumericSchedule R.family J),
      |selected C R m period k| ≤ T.admittedCost m

theorem covered (C : Cost) (R : Run G) (hG : G.Simple) (s : Sheet G) (n : ℕ → ℕ)
    (sheet : R.metals.p = ThroughLaunch.raise s n)
    (hA : NativeDiagonalClockRequest.PaidRequests
      (post C s (fun i => (R.family.path.levels.clock.factor i).val)) R.family.path.levels) :
    Covered C R := by
  intro k
  let L := R.family.path.levels
  let q := fun m => Real.log (Real.log (L.clock.hatBeta m))
  have qlate : Tendsto q atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (WardBin.bell L hG))
  obtain ⟨first,hf⟩ := hA.2 k
  filter_upwards [eventually_ge_atTop first,qlate.eventually_ge_atTop 1] with m hm hq
  intro period
  have h := hf m hm (L.clock.J (m+1)) le_rfl
  rw [sampled C R s n sheet m period k] at h
  refine ⟨h,?_⟩
  intro V J T
  have hmon : 1+q m ≤ L.clock.monitor m := by
    change 1+q m ≤ Real.exp ((q m)^2)
    have hsq : q m ≤ (q m)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (zero_le_one.trans hq)]
    linarith [Real.add_one_le_exp ((q m)^2)]
  have hp : 0 ≤ L.clock.monitor (m+1) := (Real.exp_pos _).le
  exact h.trans (hmon.trans ((le_add_of_nonneg_right hp).trans (T.monitor_cost m)))

/-- Choose any countable table of genuine coefficients before the lengths
and beta purchases. All periods and every numerical schedule are covered. -/
theorem buy (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe) (Δ : Decal G)
    {ε : ℝ} (hε : 0<ε) (available : ∀ s q, Nonempty (FundedCostDictionary.Demand hG P s q))
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction)) (C : Cost) :
    ∃ A : FundedCostDictionary.PredictionPurchase hG P Δ ε (@prediction), Covered C A.original.run := by
  obtain ⟨A,hA⟩ := FundedDictionaryRenderPrices.paid_rows hG P Δ hε available
    (@prediction) paid (fun s _ _ => post C s)
  let S := A.original.dictionary.purchase
  exact ⟨A,covered C A.original.run hG S.sheet S.n S.sheet_eq hA⟩

def combined (C D E : Cost) : Cost := fun S K a k =>
  max |C S K a k| (max |(D S K a k)⁻¹| |E S K a k|)

/-- A reciprocal decay bought at one logarithmic clock suffices for every
power after multiplying by the full radius of the genuine physical block. -/
theorem cooling {b a c d : ℝ} (hb : 1 < b) (hl : 1 ≤ Real.log b)
    (ha : 0<a) (hd : 0≤d) (hc : |c|≤1+Real.log (Real.log b))
    (hi : a⁻¹≤1+Real.log (Real.log b))
    (hlarge : (d+2)*(1+Real.log (Real.log b)) ≤ Real.log b) :
    |c| *Real.exp (-a*(Pressure.radiusB b:ℝ)) ≤ b^(-d) := by
  let l := Real.log b
  let u := 1+Real.log l
  have hbu : 1≤a*u := by
    have h := mul_le_mul_of_nonneg_left hi ha.le
    simpa only [mul_inv_cancel₀ ha.ne'] using h
  have hmain : d+1 ≤ a*l := by
    have h₁ := mul_le_mul_of_nonneg_left hlarge ha.le
    have h₂ := mul_le_mul_of_nonneg_left hbu (show 0≤d+2 by linarith)
    change a*((d+2)*u)≤a*l at h₁
    nlinarith only [h₁,h₂]
  have hceil : l^2 ≤ (Pressure.radiusB b:ℝ) := Nat.le_ceil _
  have hh := mul_le_mul_of_nonneg_right hmain (zero_le_one.trans hl)
  have hfull := mul_le_mul_of_nonneg_left hceil ha.le
  have event : Real.exp (-a*(Pressure.radiusB b:ℝ)) ≤ b^(-(d+1)) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hb)]
    apply Real.exp_le_exp.mpr
    change -a*(Pressure.radiusB b:ℝ) ≤ l*(-(d+1))
    nlinarith only [hh,hfull]
  have hc' : |c|≤b := by
    have h₁ := Real.log_le_sub_one_of_pos (Real.log_pos hb)
    have h₂ := Real.log_le_sub_one_of_pos (zero_lt_one.trans hb)
    linarith
  calc
    _ ≤ b*b^(-(d+1)) := mul_le_mul hc' event (Real.exp_pos _).le (zero_le_one.trans hb.le)
    _ = b^(1:ℝ)*b^(-(d+1)) := by rw [Real.rpow_one]
    _ = b^(-d) := by rw [←Real.rpow_add (zero_lt_one.trans hb)]; congr 1; ring

theorem enough (L : Levels G) (hG : G.Simple) {d : ℝ} (hd : 0≤d) :
    ∀ᶠ m : ℕ in atTop, 1 < L.clock.hatBeta m ∧ 1 ≤ Real.log (L.clock.hatBeta m) ∧
      (d+2)*(1+Real.log (Real.log (L.clock.hatBeta m))) ≤ Real.log (L.clock.hatBeta m) := by
  let v := d+2
  have hv : 0<v := by dsimp [v]; linarith
  let f := fun m => Real.log (L.clock.hatBeta m)
  have hf : Tendsto f atTop atTop := Real.tendsto_log_atTop.comp (WardBin.bell L hG)
  have small : ∀ᶠ m : ℕ in atTop, ‖Real.log (f m)‖ ≤ (2*v)⁻¹*‖f m‖ := by
    simpa only [pow_one,id_eq] using hf.eventually ((Real.isLittleO_pow_log_id_atTop (n:=1)).bound
      (inv_pos.mpr (mul_pos (by norm_num) hv)))
  filter_upwards [small,hf.eventually_ge_atTop (2*v),hf.eventually_ge_atTop 1]
    with m hs hb hl
  rw [Real.norm_of_nonneg (Real.log_nonneg hl),Real.norm_of_nonneg (zero_le_one.trans hl)] at hs
  have ht : Real.log (f m) ≤ f m/(2*v) := by simpa only [div_eq_mul_inv,mul_comm] using hs
  have tt := (le_div_iff₀ (mul_pos (by norm_num) hv)).mp ht
  exact ⟨L.fits.delayed m,hl,by change v*(1+Real.log (f m)) ≤ f m; nlinarith only [tt,hb]⟩

def Decay (fee rate auxiliary : Cost) (R : Run G) : Prop :=
  let L := R.family.path.levels
  ∀ k (d : ℝ), 0≤d → ∀ᶠ m : ℕ in atTop, ∀ period,
    let c := selected fee R m period k
    let a := selected rate R m period k
    let e := selected auxiliary R m period k
    (∀ {V : Type} {J : Request V} (T : NumericSchedule R.family J),
      |c|≤T.admittedCost m ∧ a⁻¹≤T.admittedCost m ∧ |e|≤T.admittedCost m) ∧
    (0<a → |c| * Real.exp (-a*(L.clock.coverSize m:ℝ)) ≤ (L.clock.hatBeta m)^(-d))

theorem decay_on (R : Run G) (hG : G.Simple) (fee rate auxiliary : Cost)
    (hA : Covered (combined fee rate auxiliary) R) : Decay fee rate auxiliary R := by
  dsimp only [Decay]
  intro k d hd
  let L := R.family.path.levels
  filter_upwards [hA k,enough L hG hd] with m bought window
  intro period
  let c := selected fee R m period k
  let a := selected rate R m period k
  let e := selected auxiliary R m period k
  let t := max |c| (max |a⁻¹| |e|)
  have hc : |c| ≤ |t| := (le_max_left _ _).trans (le_abs_self _)
  have ha : a⁻¹ ≤ |t| := (le_abs_self _).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_abs_self _)))
  have he : |e| ≤ |t| := (le_max_right _ _).trans ((le_max_right _ _).trans (le_abs_self _))
  have h := bought period
  refine ⟨fun T => ⟨hc.trans (h.2 T),ha.trans (h.2 T),he.trans (h.2 T)⟩,?_⟩
  intro live
  exact cooling window.1 window.2.1 live hd (hc.trans h.1) (ha.trans h.1) window.2.2

theorem decay (hG : G.Simple) (P : ActualQlocalRequestFamily.Recipe) (Δ : Decal G)
    {ε : ℝ} (hε : 0<ε) (available : ∀ s q, Nonempty (FundedCostDictionary.Demand hG P s q))
    (prediction : FundedCompanySelection.Prediction G)
    (paid : FundedPredictionSupply.AllPrices (@prediction)) (fee rate auxiliary : Cost) :
    ∃ A : FundedCostDictionary.PredictionPurchase hG P Δ ε (@prediction),
      Decay fee rate auxiliary A.original.run := by
  obtain ⟨A,h⟩ := buy hG P Δ hε available (@prediction) paid (combined fee rate auxiliary)
  exact ⟨A,decay_on A.original.run hG fee rate auxiliary h⟩

end YM.Integration.WilsonLimitConstruction.FundedDictionaryPatchPrices
end
