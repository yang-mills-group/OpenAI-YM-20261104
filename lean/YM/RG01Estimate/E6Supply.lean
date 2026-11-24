import YM.RG01Estimate.RepriceVertex

/-! Units for warning costs and putting a Utopia back through the priority integral. New
parameterized re-purchase. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Reprice

open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Coat Raw Pulse Itinerary Footprint Shell Poll Pond Matter Control Window
open Blaze Brush Scroll Vine Polar Frond Silica Clutch Eider SliceRows Flux Shield Art Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P)

lemma supplied :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ D : Patch, D.Branches P.bind G → ∀ (u v w : ℝ),
    u+v<Q.rate → 0≤w → ∀ (X E K f g : ℝ→ℝ), Rate G L u X → Rate G L v E → Rate G L w K →
      (∀ᶠ x in atTop,1 ≤ E x) → (∀ᶠ x in atTop,1 ≤ K x) →
      Rate G L (-(1/2:ℝ)) f → (∀ᶠ x in atTop, 0 ≤ f x) → Rate G L (-(1/2:ℝ)) g →
    ∀ (χ : Chi) (i : ℕ) (W μ : ℝ), 0 < W → 0 < μ → ∀ o:Target.Order G W,
    ∃ (C':ℝ) (r:ℝ→ℝ), Rate G L 0 r ∧ ∀ᶠ x in atTop, ∀ (c f':Side) (S : StepData c f') (T: Tube G S), S.patch=D → Stamp T →
      ∀ (R:Rep G f') (C:ℝ) (H:Cash W x μ L Q o C T R) (J : Set ℕ), Inherit.Debits R J (X x) →
        ∃ Ξ : Utopia H i (f x) (g x) (r x) C' χ, Expense.Supports (weigh c f' J (E x) (K x)) Ξ := by
  obtain ⟨n,hn⟩:= logs P Q
  refine ⟨n, fun L hL D hD u v w h hv X E K f g hx he hk hE hK hf hp hg χ i W μ hw hm o=>?_⟩
  obtain ⟨p,hp',hy⟩:= exists_between (show max (u+v) (-(1/2:ℝ))<Q.rate from max_lt h Q.start)
  have hl : p < 0:= lt_trans hy Q.stop
  obtain ⟨C,hC,hΨ⟩:= Clutch.chimney P D L hD o.K o.γ W o.a χ i Q.table_exists hf hp hg μ o.indexPay o.f o.large hw o.gamma
  obtain ⟨B,J,hB,hBP,hJ,h⟩:= hn L hL D hD u v w p ((le_max_right ..).trans_lt hp') hl ((le_max_left ..).trans_lt hp') hv _ _ _ _ _ hx he hk hE hK hf hp hg χ i W o
  obtain ⟨A,hA,htQ,hQ⟩:= Clutch.ash G L χ i hg hf W o.a Q.halo (by have h:=Q.buys; omega)
  let z x:= betaF G x L ^ (p-w); let Z x:= B x+A x
  have hZ x:1≤Z x:= (hBP x).trans (le_add_of_nonneg_right (htQ x))
  have he':0≤Q.relative:= by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  obtain ⟨Y,hY,hF⟩:= Coat.alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (2*(p-w)-1) (half_pos o.rare)
  let u':= Coat.topStorm D+1; have hu' : 0 ≤ u' := by unfold u'; linarith [topStorm_one D]
  obtain ⟨b,hb,hH⟩:= exponent_fee G L Q.halo Q.relative Q.ε p u' he' (fun x=> K x*z x) (show Rate G L p _ from by
    convert hk.mul (Rate.power (a:=p-w)) using 1; ring)
  refine ⟨C,Z,hB.add hA,?_⟩
  filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hE,hK,hΨ,h,hQ,hF,hY (2*(p-w)) (by linarith only),Q.pay_for L hm hC,(hJ.add (hJ.add hb)) Q.rate hy] with
    x hx hk hK hΨ h hQ hF hY hA hv c f S T hS hF' R C' H I hI
  have hΓ:= H.laws.data
  have hh:= H.laws.intake
  have h' := hΓ.localP
  obtain ⟨V,y,hP,hW⟩:= h _ _ S T hΓ.funds hS hF' h' hΓ.access R hh I hI
  have hz:0 ≤ z x:= Real.rpow_nonneg (zero_le_one.trans hx) _
  have hΞ:=hH x c f S hΓ.funds.length_eq (by have h:= hΓ.room.sight; omega) (mul_nonneg hu' (mul_nonneg (zero_le_one.trans hK) hz))
  have hu : Sales (radiusB x) Q.relative Q.ε (footprints T R Q.halo (radiusB x)) (fun i=> weigh c f I (E x) (K x) i * rates V y (u'*z x) i) (Sum.elim
    (Raw.forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L x) := by
    apply (Sales.raise (γ:= J x+(J x+b x)))
    · convert (hP.first.together (hW.together hΞ)) using 1
      · rfl
      · funext j; rcases j with j|j|j
        · exact one_mul _
        · rfl
        change K x*(u'*z x)=u'*(K x*z x); ring
    exact (le_abs_self _).trans hv
  refine ⟨⟨V,y,u',hu',z x,hz,hF',hZ x,(by rw [hΓ.funds.length_eq]; exact hA R.beta (hΓ.funds.length_eq ▸ hh.window.1)),
      (Inherit.fee_shift hu (ones I hk hK)),?_,?_⟩,hu⟩
  · intro E _ _ _ F X A' v' w' z q ht hX hχ hZ' hM hp F' k p hv
    have ht' := h' F X ht hX hZ'
    obtain ⟨hL,hK⟩:= hP.stamina E F X A' v' w' z q ht hX hχ hZ' hM hp k
    rcases p with p|p
    · by_cases he: Packets.connected S Q.halo X.B p
      swap
      · apply Brush.zi (Eventually.of_forall (fun y:E=> if_neg he)) (by unfold stout Mixed.costs; simp only [Sum.elim,if_neg he]; exact le_rfl)
          (show 0≤Z x*1 from mul_nonneg (zero_le_one.trans (hZ x)) zero_le_one)
      have hh' : Healthy (Pressure.temp X.x) (p.dome (Q.halo*X.B)) X.V := by unfold Coat.B; rw [ht] at *; exact hv
      have hX:= hΨ c _ S T hS hΓ.funds hΓ.access hΓ.grant E z A' F X R v' q w' ht hχ hX ht' hM hh hp p Q.halo k Q.buys
        (Packets.shares_nonzero S _ _ he) hh'
      apply hX.shimmy (Eventually.of_forall (fun y=> if_pos he))|>.climb _ (show 1≤Z x*1 by rw [mul_one]; exact hZ _)
      unfold stout; simp only [Mixed.costs,Sum.elim,if_pos he,steamP,Target.costs,Buy.quote]; unfold Grant.credit Coat.t; rw [ht,hΓ.funds.length_eq]
    have ha : 0 ≤ twigs R T X.B Q.halo p := add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hv : B x*twigs R T X.B Q.halo p≤Z x*twigs R T X.B Q.halo p := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (htQ x)) ha
    rcases p with p|p|p
    · exact (hK p).climb le_rfl hv
    · exact (hL p).climb le_rfl hv
    unfold u'; rw [← hS]; refine (hQ c _ S T F X R ht hχ hΓ.funds.length_eq (show 0<W*X.t from mul_pos hw ht'.sails.room.fiery) _ q z A' v' w' hp hM p k _).climb le_rfl ?_
    apply le_trans _ (mul_le_mul_of_nonneg_right (show A x ≤ Z x from le_add_of_nonneg_left (zero_le_one.trans (hBP _))) ha)
    apply le_of_eq; unfold twigs lengths; simp
    exact Or.inl rfl -- disambiguation
  intro F X ht hK _ hp K
  have hV' : betaF G x L^(2*(p-w))=z x^2 := by
    unfold z; rw [mul_comm,Real.rpow_mul (zero_le_one.trans hx),Real.rpow_two]
  exact (hF.2 c f S T F X ht hΓ.funds.length_eq (h' F X ht hK hp).sails R (ht.symm ▸ hh) K).trans
    (pow_le_pow_left₀ hF.1 (((le_abs_self _).trans hY).trans_eq hV') _)

end YM.RG01Estimate.Reprice
