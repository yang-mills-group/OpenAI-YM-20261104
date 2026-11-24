import YM.RGLocalTaylor.Engine.Awning

/-!
# License rare fares relative to the SAME actual support purchases. Arbitrary
power enhancement of `Utopia.ship` before sharing, by returning to the
`alarm_bills` estimate. Adaptation of `Utopia.whittle`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open Silica.Clutch

structure RareShips (Ξ : Utopia H j v d r C' χ) (discount : ℝ) : Prop where
  alert : ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s → X.width=o.K → X.χ=χ → X.manifest → ∀ v,
    X.dice.real (X.catastrophe (o.ξ/2) R.beta v) ≤ ((discount*Ξ.rad)^2)^v.card

namespace RareShips
lemma whittle (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (U:ℕ) (D:Patch), D.Branches P.bind G → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0 < W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤v x) → Rate G L (-(1/2)) w → ∃ (C':ℝ) (r:ℝ→ℝ), 0≤C' ∧ Rate G L 0 r ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T → ∀ (R:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),
      ∃ Ξ : Utopia H i (v x) (w x) (r x) C' χ, RareShips Ξ (betaF G x L ^ (-(U:ℝ))) := by
  obtain ⟨t,hT,ht⟩:= exists_between Q.start
  obtain ⟨n,hn⟩:= Clutch.pay_busy P Q hT (ht.trans Q.stop)
  refine ⟨n,fun L hL U D hd i χ W hw μ hm o v w hv hwV hW=>?_⟩
  obtain ⟨C,hC,hΨ⟩:= Clutch.chimney P D L hd o.K o.γ W o.a χ i Q.table_exists hv hwV hW μ o.indexPay o.f o.large hw o.gamma
  obtain ⟨B,J,hB,hJ,hv',h⟩:= hn L hL D hd i χ W o v w hv hwV hW
  obtain ⟨A,hA,hy,hQ⟩:=Clutch.ash G L χ i hW hv W o.a Q.halo (by have h:=Q.buys; omega)
  obtain ⟨Y,hY,hF⟩:= Coat.alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (2*(t-U)-1) (half_pos o.rare)
  let g x:= betaF G x L ^ t; let Z x:= B x+A x; have hZ x:1≤Z x:= (hv' x).trans (le_add_of_nonneg_right (hy x))
  have hp:0≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  let u := Coat.topStorm D+1; have hu : 0 ≤ u := by unfold u; linarith [topStorm_one D]
  obtain ⟨b,hb,hH⟩:= exponent_fee G L Q.halo Q.relative Q.ε t u hp g Rate.power
  refine ⟨C,Z,hC,hB.add hA,?_⟩
  filter_upwards [hΨ,h,hQ,hF,hY (2*(t-U)) (by linarith),Q.pay_for L hm hC,(hJ.add (hJ.add hb)) Q.rate ht]
    with x hΨ h hQ he hV hA hv c f S T hS hF R C' H
  have hΓ:= H.laws.data; have hh:= H.laws.intake
  have hΘ: 0<betaF G x L:=by have he:=hh.height; rw [hΓ.funds.length_eq] at he; linarith
  have hg:0≤g x:= by unfold g; positivity
  have h' := (hΓ.localP)
  obtain ⟨V,y,H'⟩:= h _ _ S T hΓ.funds hS hF h' hΓ.access R hh
  have hΞ:=hH x c f S hΓ.funds.length_eq (by have h:= hΓ.room.sight; omega) (mul_nonneg hu hg)
  let cst:= betaF G x L ^ (-(U:ℝ))
  have htL : 1 ≤ betaF G x L:= by rw [←hΓ.funds.length_eq]; exact hh.height.le
  have hcst : cst ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos htL (by simp)
  have hp': (cst*g x)^2 = betaF G x L ^ (2*(t-U)) := by
    unfold cst g; rw [← Real.rpow_add hΘ, neg_add_eq_sub, mul_comm, Real.rpow_mul hΘ.le, Real.rpow_two]
  have hP (F:Forest S.ratio) (X:Coat T F) (ht:X.x=x) (hk:X.width=o.K) (hp:X.manifest) K :
      X.dice.real (X.catastrophe (o.ξ/2) R.beta K) ≤ ((cst*g x)^2)^K.card := by
    rw [hp']; exact (he.2 c f S T F X ht hΓ.funds.length_eq (h' F X ht hk hp).sails R (ht.symm ▸ hh) K).trans
      (pow_le_pow_left₀ he.1 ((le_abs_self _).trans hV) _)
  refine ⟨⟨V,y,u,hu,g x,hg,hF,hZ x,(by rw [hΓ.funds.length_eq]; exact hA R.beta (hΓ.funds.length_eq ▸ hh.window.1)),
    (ratesCombine H'.first H'.hair hΞ).raise ((le_abs_self _).trans hv),?_,?_⟩, ⟨fun F X ht hk _ hM K=> hP F X ht hk hM K⟩⟩
  · intro E _ _ _ F X A' v' w' z q ht hX hχ hZ' hM hp F' k p hv
    have ht' := h' F X ht hX hZ'

    obtain ⟨hL,hK⟩:=H'.stamina E F X A' v' w' z q ht hX hχ hZ' hM hp k
    rcases p with p|p
    · by_cases he: Packets.connected S Q.halo X.B p
      swap; · apply Brush.zi (Eventually.of_forall (fun y:E=> if_neg he)) (by unfold stout Mixed.costs; simp only [Sum.elim,if_neg he]; exact le_rfl)
                (show 0≤Z x*1 from mul_nonneg (zero_le_one.trans (hZ x)) zero_le_one)
      have hh' : Healthy (Pressure.temp X.x) (p.dome (Q.halo*X.B)) X.V := by unfold Coat.B; rw [ht] at *; exact hv
      have hX:= hΨ c f S T hS hΓ.funds hΓ.access hΓ.grant E z A' F X R v' q w' ht hχ hX ht' hM hh hp p Q.halo k Q.buys
        (Packets.shares_nonzero S _ _ he) hh'
      apply hX.shimmy (Eventually.of_forall (fun y=> if_pos he))|>.climb _ (show 1≤Z x*1 by rw [mul_one]; exact hZ _)
      unfold stout; simp only [Mixed.costs,Sum.elim,if_pos he,steamP,Target.costs,Buy.quote]; unfold Grant.credit Coat.t; rw [ht,hΓ.funds.length_eq]
    have ha : 0 ≤ twigs R T X.B Q.halo p := add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hv : B x*twigs R T X.B Q.halo p≤Z x*twigs R T X.B Q.halo p := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (hy x)) ha
    rcases p with p|p|p
    · exact (hK p).climb le_rfl hv
    · exact (hL p).climb le_rfl hv
    unfold u; rw [← hS]; refine (hQ c f S T F X R ht hχ hΓ.funds.length_eq
      (show 0<W*X.t from mul_pos hw ht'.sails.room.fiery) _ q z A' v' w' hp hM p k _).climb le_rfl ?_
    apply le_trans _ (mul_le_mul_of_nonneg_right (show A x ≤ Z x from le_add_of_nonneg_left (zero_le_one.trans (hv' _))) ha)
    apply le_of_eq; unfold twigs lengths; simp
    exact Or.inl rfl
  intro F X ht hK _ hp K
  exact (hP F X ht hK hp K).trans (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀
    (mul_nonneg (Real.rpow_nonneg hΘ.le _) hg) (mul_le_of_le_one_left hg hcst) 2) _)

end RareShips
end YM.RGLocalTaylor
