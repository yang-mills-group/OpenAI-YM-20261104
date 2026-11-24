import YM.Integration.CappedCensusFusion
import YM.Integration.CensusTailCost

/-! Polynomial charges for hard fusion at fixed field, distance and support
orders. Both tail counting radii remain positive at every stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CensusFusionEnvelope

open Filter Lattice Wilson RG Push.AbsoluteSums
open AnalyticBridge VerifiedReset Collection Quotes Residual Geo
open PhysicalNext.Repeat.Legato IterationFour FullQLocal FullQLocal.RenderedStep
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

private def Bounded (a f : ℕ → ℝ) : Prop := ∃ d : ℕ, ∀ᶠ m : ℕ in atTop, |f m| ≤ a m^d

private theorem Bounded.mono {a f g : ℕ → ℝ} (hi : ∀ᶠ m : ℕ in atTop, |f m| ≤ |g m|)
    (h : Bounded a g) : Bounded a f := by
  obtain ⟨d,hd⟩ := h
  refine ⟨d,?_⟩
  filter_upwards [hi,hd] with m hm hn
  exact hm.trans hn

private theorem Bounded.mul {a f g : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    (h : Bounded a f) (k : Bounded a g) : Bounded a (fun m => f m*g m) := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨e,he⟩ := k
  refine ⟨d+e, ?_⟩
  filter_upwards [hd,he] with m hm hn
  rw [abs_mul,pow_add]
  exact mul_le_mul hm hn (abs_nonneg _) (pow_nonneg (ha m) _)

private theorem Bounded.add {a f g : ℕ → ℝ} (ha : ∀ᶠ m : ℕ in atTop, 2 ≤ a m)
    (h : Bounded a f) (k : Bounded a g) : Bounded a (fun m => f m+g m) := by
  obtain ⟨d,hd⟩ := h
  obtain ⟨e,he⟩ := k
  refine ⟨d+e+1, ?_⟩
  filter_upwards [ha,hd,he] with m hm hF hE
  have h1 : 1 ≤ a m := by linarith
  have hp := pow_nonneg (zero_le_one.trans h1) (d+e)
  calc
    |f m+g m| ≤ |f m|+|g m| := abs_add_le _ _
    _ ≤ a m^(d+e)+a m^(d+e) := add_le_add
      (hF.trans (pow_le_pow_right₀ h1 (by omega))) (hE.trans (pow_le_pow_right₀ h1 (by omega)))
    _ ≤ a m^(d+e+1) := by rw [pow_succ]; linarith [mul_le_mul_of_nonneg_left hm hp]

private theorem Bounded.pow {a f : ℕ → ℝ}
    (h : Bounded a f) (k : ℕ) : Bounded a (fun m => f m^k) := by
  obtain ⟨d,hd⟩ := h
  refine ⟨d*k, ?_⟩
  filter_upwards [hd] with m hm
  rw [abs_pow,pow_mul]
  exact pow_le_pow_left₀ (abs_nonneg _) hm k

private lemma radius_inv {σ : ℝ} (hs : 0 < σ) :
    (CappedCensusFusion.radius σ)⁻¹ ≤ 1+4*σ⁻¹ := by
  by_cases h : σ/4 ≤ 1
  · have he : (σ/4)⁻¹ = 4*σ⁻¹ := by field_simp [hs.ne']
    rw [CappedCensusFusion.radius,min_eq_left h,he]
    linarith
  · norm_num [CappedCensusFusion.radius,min_eq_right (le_of_not_ge h)]
    positivity

private lemma geometric_loss {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (1-Real.exp (-x))⁻¹ ≤ Real.exp 1*x⁻¹ := by
  have h : 0 < 1-Real.exp (-x) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hl : x ≤ (1-Real.exp (-x))*Real.exp x := by
    rw [sub_mul,one_mul,← Real.exp_add,neg_add_cancel,Real.exp_zero]
    linarith [Real.add_one_le_exp x]
  have he := mul_le_mul_of_nonneg_left (Real.exp_monotone hx1) h.le
  rw [← div_eq_mul_inv, le_div_iff₀ hx,inv_mul_eq_div,div_le_iff₀ h]
  linarith only [hl,he, mul_comm (1-Real.exp (-x)) (Real.exp 1)]

private lemma geometry (R : Run G) (A : NumericSchedule R.family J) (m : ℕ) :
    let L := R.family.path.levels
    (L.clock.coverSize m : ℝ) ≤ A.admittedCost m ∧
    (L.params m).width⁻¹ ≤ A.admittedCost m ∧ (L.params m).paths ≤ A.admittedCost m := by
  let L := R.family.path.levels
  have h := A.cost_covers_geometry m
  have hm (i : ℕ) : 0 ≤ L.clock.monitor i := (Real.exp_pos _).le
  have hl (i : ℕ) : 0 ≤ L.clock.loopCap i := mul_nonneg (by norm_num)
    (Real.rpow_nonneg (hm i) _)
  have hp i := (L.params i).paths_pos.le
  have hc i := (L.params i).columns_ge
  have hr i := (L.params i).clip.radius_pos.le
  have ht : 12 ≤ (L.params m).clip.relaxation*(L.params m).width := (L.params m).slow_selector
  have hi : (L.params m).width⁻¹ ≤ (L.params m).clip.relaxation :=
    by simpa only [one_div] using (div_le_iff₀ (L.params m).width_pos).2
        (by linarith only [ht] : (1:ℝ) ≤ (L.params m).clip.relaxation*(L.params m).width)
  change 1+(L.clock.coverSize m:ℝ)+(L.clock.coverSize (m+1):ℝ)+L.clock.monitor m+
    L.clock.monitor (m+1)+L.clock.loopCap m+L.clock.loopCap (m+1)+(L.params m).paths+
    (L.params (m+1)).paths+(L.params m).columns+(L.params (m+1)).columns+
    (L.params m).clip.relaxation+(L.params (m+1)).clip.relaxation ≤ A.admittedCost m at h
  have hge : (L.clock.coverSize m:ℝ) ≤ A.admittedCost m ∧
      (L.params m).clip.relaxation ≤ A.admittedCost m ∧ (L.params m).paths ≤ A.admittedCost m := by
    have hB0 := Nat.cast_nonneg (α := ℝ) (L.clock.coverSize m)
    have hB1 := Nat.cast_nonneg (α := ℝ) (L.clock.coverSize (m+1))
    refine ⟨?_,?_,?_⟩
    all_goals linarith only [h,hm m,hm (m+1),hl m,hl (m+1),hp m,hp (m+1),hc m,hc (m+1),hr m,hr (m+1),hB0,hB1]
  exact ⟨hge.1,hi.trans hge.2.1,hge.2.2⟩

def block (B : ℕ) : ℝ := ((B+B+1 : ℕ):ℝ)^4

def coefficient (G : Gauge) (p : BudgetPoint) (c : Clip) (σ C : ℝ) : ℝ :=
  block p.B * (Quotes.softReset G p 1 + (2 + (2:ℝ)⁻¹*pairBill G p)*CappedCensusFusion.low p c σ C)

/-- Every geometric and analytic charge for the hard fuser is polynomial
in the explicitly admitted cost, with an exponent fixed before the cutoff. -/
theorem eventual (R : Run G) (hG : G.Simple) (A : NumericSchedule R.family J)
    (hclip : ∀ᶠ m : ℕ in atTop, (R.family.path.levels.params m).clip.direct ≤ 1) :
    ∃ d : ℕ, ∀ᶠ m : ℕ in atTop, let S := R.family.path.levels.params m
      coefficient G (A.outputNorm m) S.clip S.width S.paths ≤ A.admittedCost m^d ∧
      block (A.outputNorm m).B ≤ A.admittedCost m^d := by
  let a := A.admittedCost
  let L := R.family.path.levels
  let q := A.outputNorm
  let s := L.params
  let rad (m : ℕ) := CappedCensusFusion.radius ((s m).width)
  have ha m : 0 ≤ a m := A.admitted_cost_nonnegative m
  have hg (c : ℝ) : ∀ᶠ m : ℕ in atTop, c ≤ a m := by
    have hz := Real.tendsto_log_atTop.comp (WardBin.bell L hG)
    filter_upwards [hz.eventually_ge_atTop 1,hz.eventually_ge_atTop c] with m h1 hc
    change 1 ≤ Real.log (L.clock.hatBeta m) at h1
    change c ≤ Real.log (L.clock.hatBeta m) at hc
    have hsq : c ≤ (Real.log (L.clock.hatBeta m))^2 := by
      exact hc.trans (by simpa only [pow_two] using le_mul_of_one_le_right (zero_le_one.trans h1) h1)
    exact hsq.trans ((Nat.le_ceil _).trans (geometry R A m).1)
  have cst (c : ℝ) : Bounded a (fun _ => c) := ⟨1,by simpa using hg |c|⟩
  have add (f g : ℕ → ℝ) := @Bounded.add a f g
  have mul (f g : ℕ → ℝ) := @Bounded.mul a f g
  have pw (f : ℕ → ℝ) := @Bounded.pow a f
  have haB : Bounded a a := ⟨1,Eventually.of_forall fun m => by rw [abs_of_nonneg (ha m),pow_one]⟩
  have hB m : ((q m).B:ℝ) ≤ a m :=
    (A.output_norm m).block ▸ (geometry R A m).1
  have hBnd : Bounded a (fun m => ((q m).B:ℝ)) :=
    haB.mono (Eventually.of_forall fun m => by rw [abs_of_nonneg (Nat.cast_nonneg _),abs_of_nonneg (ha m)]; exact hB m)
  have hspan (b : ℕ → ℕ) (hb : Bounded a (fun m => (b m:ℝ))) :
      Bounded a (fun m => (Footprint.spread 1 (b m) : ℝ)) := by
    simpa only [Footprint.spread,Push.AbsoluteSums.Animals.ballCost,one_mul,Nat.cast_pow,
      Nat.cast_add,Nat.cast_one] using pw _ (add _ _ (hg 2) (add _ _ (hg 2) hb hb) (cst 1)) 4
  have hblk : Bounded a (fun m => block (q m).B) := by
    simpa only [Footprint.spread,Push.AbsoluteSums.Animals.ballCost,one_mul,Nat.cast_pow,block]
      using hspan (fun m => (q m).B) hBnd
  have hB' : Bounded a (fun m => (Footprint.spread 1 (4*(q m).B+2):ℝ)) := by
    apply hspan
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
      add _ _ (hg 2) (mul _ _ ha (cst 4) hBnd) (cst 2)
  have hfields m : (q m).power = (q 0).power ∧ (q m).order = (q 0).order ∧
      (q m).supportExponent = (q 0).supportExponent := ⟨(A.output_norm m).distance.trans
        (A.output_norm 0).distance.symm,(A.output_norm m).order.trans (A.output_norm 0).order.symm,
        (A.output_norm m).reserve.trans (A.output_norm 0).reserve.symm⟩
  have hpair m : pairBill G (q m) = pairBill G (q 0) := by
    unfold pairBill; rw [(hfields m).1,(hfields m).2.1]
  have hreset m : resetLoss G (q m) = resetLoss G (q 0) := by
    unfold resetLoss multiplier; rw [hpair m]
  let e := Real.exp (((q 0).supportExponent+1)*81)*resetLoss G (q 0)*
    (((1:ℝ)⁻¹)^4 * (4:ℕ).factorial * Real.exp 1) * (1-Real.exp (-1))⁻¹
  have hsreset : Bounded a (fun m => Quotes.softReset G (q m) 1) := by
    have he m : Quotes.softReset G (q m) 1 = e*Footprint.spread 1 (4*(q m).B+2) := by
      unfold Quotes.softReset Footprint.payment Footprint.degreeIncome e
      rw [(hfields m).2.2,hreset m]
      norm_num only [Nat.reduceAdd]
      ring
    simpa only [he] using mul _ _ ha (cst e) hB'
  have hr m : 0 < rad m := lt_min (by linarith [(s m).width_pos]) zero_lt_one
  have hr1 m : rad m ≤ 1 := min_le_right _ _
  have hri : Bounded a (fun m => (rad m)⁻¹) :=
    (add _ _ (hg 2) (cst 1) (mul _ _ ha (cst 4) haB)).mono
      (Eventually.of_forall fun m => by
        rw [abs_of_pos (inv_pos.mpr (hr m)),abs_of_nonneg (by linarith only [ha m] : 0 ≤ 1+4*a m)]
        exact (radius_inv (s m).width_pos).trans (by linarith [(geometry R A m).2.1]))
  have her : Bounded a (fun m => Real.exp (rad m)) := (cst (Real.exp 1)).mono <|
    Eventually.of_forall fun m => by
      rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
      exact Real.exp_monotone (hr1 m)
  have hsum : Bounded a (fun m => (1-Real.exp (-(rad m)))⁻¹) :=
    (mul _ _ ha (cst (Real.exp 1)) hri).mono (Eventually.of_forall fun m => by
      have hs : 0 < 1-Real.exp (-(rad m)) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (hr m)))
      simpa only [abs_of_pos (inv_pos.mpr hs),abs_of_pos (mul_pos (Real.exp_pos _) (inv_pos.mpr (hr m)))] using
        geometric_loss (hr m) (hr1 m))
  have hpath : Bounded a (fun m => (s m).paths) := haB.mono <|
    Eventually.of_forall fun m => by rw [abs_of_pos (s m).paths_pos,abs_of_nonneg (ha m)]; exact (geometry R A m).2.2
  have hdir : Bounded a (fun m => (s m).clip.direct) := (cst 1).mono <|
    hclip.mono fun m hm => by simpa only [abs_of_pos (s m).clip.quadratic_pos,abs_one] using hm
  let k := Real.exp (((q 0).supportExponent+1)*lowCount)*(Fintype.card Signed:ℝ)*
    (Fintype.card PlaqAxes:ℝ)*(4:ℕ).factorial
  have hlow : Bounded a (fun m => CappedCensusFusion.low (q m) (s m).clip (s m).width (s m).paths) := by
    have he m : CappedCensusFusion.low (q m) (s m).clip (s m).width (s m).paths =
        k*((s m).clip.direct+(s m).paths*(s m).paths)*Footprint.spread 1 (q m).B*
        (rad m)⁻¹^4*Real.exp (rad m)*(1-Real.exp (-(rad m)))⁻¹ := by
      unfold CappedCensusFusion.low Footprint.payment Footprint.degreeIncome lowerSize k rad
      rw [(hfields m).2.2]
      norm_num only [Nat.reduceAdd]
      ring
    simpa only [he] using mul _ _ ha (mul _ _ ha (mul _ _ ha (mul _ _ ha (mul _ _ ha
      (cst k) (add _ _ (hg 2) hdir (mul _ _ ha hpath hpath))) (hspan _ hBnd))
      (pw _ hri 4)) her) hsum
  have hcoef : Bounded a (fun m => coefficient G (q m) (s m).clip (s m).width (s m).paths) := by
    simpa only [coefficient,hpair] using mul _ _ ha hblk (add _ _ (hg 2) hsreset
      (mul _ _ ha (cst (2+(2:ℝ)⁻¹*pairBill G (q 0))) hlow))
  obtain ⟨d,hd⟩ := hcoef
  obtain ⟨e,he⟩ := hblk
  refine ⟨d+e,?_⟩
  filter_upwards [hd,he] with m h1 h2
  have hh := A.admitted_cost_ge_one m
  exact ⟨(le_abs_self _).trans (h1.trans (pow_le_pow_right₀ hh (by omega))),
    (le_abs_self _).trans (h2.trans (pow_le_pow_right₀ hh (by omega)))⟩

end YM.Integration.CensusFusionEnvelope
end
