import YM.RG01.Vacuum.Select

/-!
# Fixed power at arbitrary reserve and small-arity survivors

A seed population counted by `Mixed.shares` even inside the logarithm
pays every fixed order, **without** an additional large-mark Rank delay.
Key: use the profit guarantee on the corresponding hard account to
recover a lower bound on the same mark gain in `beacon`! Add the full
address decision (including extremely long depth) and price all these
sectors simultaneously.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01.Vacuum
open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext Repeat Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Progress.DirectedRecipe
open Real
section weights
variable {G:Gauge} {P:Teller G} {L:Side} (Q : YM.ConnectedActivityE6.Target G P) (μ s : ℝ) (h:1 ≤ betaF G s L)
include h
lemma overture_floor (n : ℕ) :
    (sqrt (betaF G s L))⁻¹ ≤ Q.overture L μ s n:= by
  let y:=betaF G s L
  have hp : 0<y:=zero_lt_one.trans_le h
  have he:1 ≤ Reserves.extract Q.ε n 0 0 := by
    unfold Reserves.extract Reserves.polyPrice
    simpa only [mul_zero,neg_zero,sub_zero,Real.exp_zero,mul_one,add_zero,one_pow] using! (polynomial_cost Q.usable le_rfl n)
  have hu : (sqrt y)⁻¹ ≤ (Q.costs L μ 1 s 0).rootHit:= by
    change (sqrt y)⁻¹ ≤ Real.exp _ + (y^Q.rate:ℝ)
    rw [Real.sqrt_eq_rpow,← Real.rpow_neg hp.le]
    exact (Real.rpow_le_rpow_of_exponent_le h Q.start.le).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  unfold Target.overture Target.quantum Mixed.Costs.ceiling treeYield
  simp only [pow_zero,mul_one,Nat.cast_zero,mul_zero]
  change (sqrt y)⁻¹ ≤ Reserves.extract Q.ε n 0 0 * ((Q.costs L μ 1 s 0).rootHit * (1-(1/2:ℝ))⁻¹)
  have hz:1≤ (1-1/2:ℝ)⁻¹:= by norm_num
  have hS:0≤(Q.costs L μ 1 s 0).rootHit:=(by positivity : (0:ℝ)≤(sqrt y)⁻¹).trans hu
  apply hu.trans ((le_mul_of_one_le_right hS hz).trans (le_mul_of_one_le_left (mul_nonneg hS (zero_le_one.trans hz)) he)) -- wrong hz.le'

lemma recover_mark (n : ℕ) {r : ℝ} (hr : Cash.armK Q L μ s 0 n ≤ r) :
    exp (-(Q.mark L μ s)) ≤ r*(sqrt (betaF G s L)) := by
  have ht := overture_floor Q μ s h n
  let y:=sqrt (betaF G s L); let p:= exp (-(Q.mark L μ s)); have hy : 0<y:=sqrt_pos.mpr (zero_lt_one.trans_le h); have hp:0≤p:=(exp_pos _).le
  have h' : y⁻¹ ≤ 20*Q.overture L μ s n*(1-1/2)⁻¹ := by
    change y⁻¹ ≤ _ at ht
    have hz:(0:ℝ) ≤ (y⁻¹:ℝ):=by positivity
    nlinarith only [ht,hz] -- inv (2 numeric)
  change p ≤ r*y
  rw [← div_le_iff₀ hy,div_eq_mul_inv]
  apply le_trans (mul_le_mul_of_nonneg_left h' hp) (b:=p*(20*Q.overture L μ s n*(1-1/2)⁻¹))
  simpa only [Cash.armK,pow_zero,inv_one,one_mul,ConnectedActivityE6.Target.mergeScale] using hr
end weights

section purchase
variable {G : Gauge} {X: Metals G} {D: Rolls X.p} {A : Alloy X D} (R:Factor A)
    {m n N : ℕ}

abbrev cashMark (m) := (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).mark
  (D.L (A.B.a.clock.J (m+1))) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (A.B.a.clock.hatBeta m)

/-- Even though the old schedule only requests a cubic mark lower bound on
beacons, one *share* is coupling-flat at the actual step. This bound holds
already on numerical prices (hence can be used for the unforced log).
Use the same `μ` from Cash or can't infer it. -/
theorem markCurrency (hG:G.Simple) (d:ℕ) : ∃ c:ℝ,0 ≤ c ∧
    ∀ (m N : ℕ), m < N → ∀ b ∈ band A.B.a (m+1),
      exp (-(cashMark R m))*voucher (A:=A) m^3 ≤ c*(sqrt b)⁻¹^d := by
  obtain ⟨c,hc,h⟩:=Flat.currency A.B.a hG d 4
  refine ⟨c,hc,?_⟩
  intro m N hm b hb
  let L:=D.L (A.B.a.clock.J (m+1)); let s:=A.B.a.clock.hatBeta m
  let y:= betaF G s L; let w:=A.B.a.clock.forcedAllowance m
  have he:y=A.B.a.clock.hatBeta (m+1):= (Push.PriceCompiler.beta_eq A.B.valid m).symm
  have hy:1≤y := he ▸ (A.B.a.fits.delayed _).le
  have hx:0≤y:=zero_le_one.trans hy
  have ht:0<w:=Real.exp_pos _
  have hw:w≤1:= Real.exp_le_one_iff.mpr (by
    have hp:0 < A.B.a.clock.monitor m := Real.exp_pos _
    exact neg_nonpos.mpr (Real.rpow_nonneg hp.le _))
  have hu:b>0:= lt_of_lt_of_le (half_pos (zero_lt_one.trans (A.B.a.fits.delayed _))) hb.1
  -- Opera.backing binder X : Rep... needs beta; can probe stub Rep? easier markCurrency takes actual u; else build stub impossible? all Reps can replace beta but need examples PathData; A.B kin provides. define.
  let p:=A.B.a
  have hR : Nonempty (ForcedAddress G (p.S.side (m+1) 0)):=⟨⟨{0},{0},singleton_nonempty 0,Subset.rfl,fun _=>True⟩⟩
  let F:RG.Rep G (p.S.side (m+1) 0):= ⟨A.B.kin.path N (m+1),(p.params (m+1)).clip,⟨fun _=>⟨0,{0},mem_singleton_self 0⟩,fun _=>Classical.choice hR,0,0⟩,p.budget (m+1),b,0⟩
  have hp:= Opera.backing (X:=F) A.B R.shape R.pledging.conducts.income (show F.beta ∈ band p (m+1) from hb)
  have hp' : exp (-(cashMark R m)) ≤ w * sqrt y := recover_mark _ _ _ hy _ (hp.trans (hard_le R _ hm b hb))
  have hD : voucher (A:=A) m ≤ y := (Real.rpow_le_rpow_of_exponent_le hy (show (3/8:ℝ)≤1 from by norm_num)).trans_eq (Real.rpow_one y)
  calc
    _ ≤ (w*sqrt y)*y^3 := mul_le_mul hp' (pow_le_pow_left₀ (Real.rpow_nonneg hx _) hD 3) (pow_nonneg (Real.rpow_nonneg hx _) _) (mul_nonneg ht.le (sqrt_nonneg _))
    _ ≤ (sqrt w*y)*y^3:= by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx _)
      rw [Real.sqrt_eq_rpow (x:=y)] -- binder
      refine mul_le_mul ?_ ((Real.rpow_le_rpow_of_exponent_le hy (by norm_num : (1/2:ℝ)≤1)).trans_eq (Real.rpow_one _)) (Real.rpow_nonneg hx _) (sqrt_nonneg _)
      have hS:=Real.mul_self_sqrt ht.le
      have hB:= Real.sqrt_le_sqrt hw; rw [Real.sqrt_one] at hB
      nlinarith only [hB,hS,Real.sqrt_nonneg w]
    _ = A.B.a.clock.hatBeta (m+1)^4*sqrt (A.B.a.clock.forcedAllowance m):= by rw [he]; unfold w; ring
    _ ≤ _ := h m b hu (.inl hb.2)

variable {u: RG.Rep G (A.B.a.S.side (m+1) n)}
   (H : Guide A.B R.shape N m n u) (O : Return.Wood A.B m n)
   (hH : Opera.Price A.B R.shape N m n u H) (hm:m<N) (hl : Lives A.B.bake N (m+1) n u) (hb : u.beta ∈ band A.B.a (m+1))

/-- Exceptional selectors proven small at every m<N with no new delay. Depth
threshold uses the receipt available; to throw out already at one cut need
improved path rate and delay. -/
def importedTail (d : ℕ) (z : H.fragrances) : Prop :=
    3+4*d ≤ degree H z ∨ 1 ≤ overlap H z ∨
      ((1+2*d:ℕ):ℝ)*Pressure.Stores.till (A.B.a.clock.hatBeta m) ≤ depth H z

include hH hm hl hb
/-- Native consumer, for specified torus and Guide (the ceremonial forest O
tracks the same unmarked vacuum scalar). -/
theorem rare (d : ℕ) {c:ℝ} 
    (hcM:exp (-(cashMark R m))*voucher (A:=A) m^3 ≤ c*(sqrt u.beta)⁻¹^d): -- uniform certificate in markCurrency
    Decision R H O (importedTail R H d) (Opera.earlyFee (p:=R.expense) A.B N m u.beta)
      ((sqrt 2^d+c)*(sqrt u.beta)⁻¹ ^ d) (A.B.a.clock.forcedAllowance m) := by
  let g := voucher (A:=A) m
  let h:= (g^(3+4*d))⁻¹ + exp (-(cashMark R m))
  let L:=D.L (A.B.a.clock.J (m+1)); let s:=A.B.a.clock.hatBeta m
  let y:= betaF G s L
  let Q:=R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)
  have he:y=A.B.a.clock.hatBeta (m+1):= (Push.PriceCompiler.beta_eq A.B.valid m).symm
  have hy:1≤y := he ▸ (A.B.a.fits.delayed _).le
  have hu:0<u.beta:= lt_of_lt_of_le (half_pos (zero_lt_one.trans (A.B.a.fits.delayed _))) hb.1
  have hg:1 ≤ g := Real.one_le_rpow hy (by norm_num)
  have hp:0<g:=zero_lt_one.trans_le hg
  have hm':0 < exp (-(cashMark R m)):=Real.exp_pos _
  have h':0≤h:=add_nonneg (by positivity) hm'.le
  have hD := choiceLocal R H O hH hm hl hb (importedTail R H d) h h' (by
    rintro z (hz|hz|hz)
    · apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hm'.le) ((pow_nonneg hp.le _).trans (beacon_ge hg z)))
      rw [mul_comm,←div_eq_mul_inv]; exact (one_le_div (pow_pos hp _)).mpr ((pow_le_pow_right₀ hg hz).trans (beacon_ge hg z))
    · have hK : 0 ≤ cashMark R m := H.laws.acquired.marked
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (show 0≤ (g^(3+4*d))⁻¹ from by positivity)) ((pow_nonneg hp.le _).trans (beacon_ge hg z)))
      rw [Real.exp_neg,mul_comm,←div_eq_mul_inv]
      apply (one_le_div (Real.exp_pos _)).2
      calc
        _ ≤ exp (cashMark R m * overlap H z) := by
          apply Real.exp_monotone; exact le_mul_of_one_le_right hK (by exact_mod_cast hz)
        _ ≤ _ := (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hg)).trans (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (mul_nonneg Q.usable.le (sum_nonneg fun _ _=> H.positive_volume _))))
    · have ht:= R.pledging.jewels _ _ (A.B.valid.pays m) _ (step_paid A.B.a m) |>.1
      let p:=(1+2*d:ℕ)
      have hu : g^(3*p) ≤ exp (Q.ε*depth H z) := by
        rw [pow_mul]; apply le_trans (pow_le_pow_left₀ (pow_nonneg hp.le _) ht p)
        rw [← Real.exp_nat_mul]
        change _ ≤ exp _
        apply Real.exp_monotone
        exact (le_of_eq (show (p:ℝ)*(Q.ε*Pressure.Stores.till s)=Q.ε*(p*Pressure.Stores.till s:ℝ) by ring)).trans (mul_le_mul_of_nonneg_left hz Q.usable.le)
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hm'.le) ((pow_nonneg hp.le _).trans (beacon_ge hg z)))
      rw [mul_comm,←div_eq_mul_inv]; apply (one_le_div (pow_pos hp _)).mpr
      apply le_trans (b:=g^(3*p)) (pow_le_pow_right₀ hg (by unfold p; omega))
      apply hu.trans
      apply le_mul_of_one_le_left (Real.exp_pos _).le
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ hg) (Real.one_le_exp (mul_nonneg H.laws.acquired.marked (Nat.cast_nonneg _))))
  unfold Decision at hD ⊢; dsimp only at hD ⊢; refine ⟨hD.1,?_ ,hD.2.2⟩
  obtain ⟨hF,hK,hM,⟨i,hi,hI⟩,hS⟩:=hD.2.1
  refine ⟨hF,hK,hM,⟨i,hi,fun x=> Cost.enlarge (hI x) ?_⟩,hS⟩
  change h*g^3 ≤ _; unfold h; rw [add_mul,pow_add,mul_inv_rev,mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp.ne'),mul_one,add_mul]
  exact add_le_add ((exchange d hy hu (show u.beta ≤ 2*y from he.symm ▸ (show u.beta ≤ 2*_ from hb.2))).trans_eq (mul_pow _ _ _)) hcM

end purchase
end YM.RG01.Vacuum
