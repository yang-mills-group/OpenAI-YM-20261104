import YM.Gaps1020.Local.ThermalPower
/-!
# Earn an arbitrary power for the optional warning clusters

The arch narrows already discard all compulsory and forced input from the
list of Taylor leaves. But a nontrivial additional class of survivors can
still contain one or more *warnings* for a fine hot ball etc. Buy all these
leaves with the true joint angular derivative and Mask prices, even at virtual
grade chosen *after* L. Make one Utopia with additional strong Gaussian
discount and preserve its inflated individual warning Sales. Following and
extending the actual proof in AnalyticNext/CONNECTED_ACTIVITY_JETS_E6/Das.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {z : Air f G}

open Clutch
variable {H : Cash W s μ L Q o C T R}

def WarnBudget (Z:ℝ) (Ξ: Utopia H j v d r C' χ) :=
    Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s))
      (rates Ξ.goalsK Ξ.goalsL (Ξ.M*(Z*Ξ.rad)))
      (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L s)
-- Inflate only accounting of existing hard-event probability, on the same
-- angular union and chapter. Allows us to use the ordinary summability
-- estimates of a Utopia for all sectors after realignment here.
def pump {Ξ:Utopia H j v d r C' χ}{Z:ℝ}(h : WarnBudget Z Ξ) (hZ:1≤Z) : Utopia H j v d r C' χ where
  rad:= Z*Ξ.rad
  awake:= mul_nonneg (zero_le_one.trans hZ) Ξ.awake
  uses:=h
  ship F X ht he hp hv p := (Ξ.ship F X ht he hp hv p).trans (pow_le_pow_left₀ (sq_nonneg _) (pow_le_pow_left₀ Ξ.awake (le_mul_of_one_le_left Ξ.awake hZ) _) _)
  __:=Ξ
lemma pump_meant {Ξ:Utopia H j v d r C' χ}{Z:ℝ}(h : WarnBudget Z Ξ) (hZ:1≤Z) (M:Molecule S)(k:ℕ) :
    (pump h hZ).meant M k = Z^(blaze M).card*Ξ.meant M k:= by
  unfold Utopia.meant; split
  next he=> rw [Utopia.remixes (pump h hZ),Ξ.remixes]; change ( _ * ((Z*Ξ.rad)^_))*_ = _; rw [mul_pow]; unfold pump Utopia.tag; simp only; ring
  next _=> rw [mul_zero]

private lemma shrink {t T' : ℝ} {K:ℕ→ℝ}{y:LogIndex c f→ℝ}(ht:0 ≤ t)(hv : t ≤ T')
    (h:Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s))
      (rates K y T') (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L s)) :
    Sales (radiusB s) Q.relative Q.ε (footprints T R Q.halo (radiusB s))
      (rates K y t) (Sum.elim (forcedExtra R) (Sum.elim (exCharge T R) fun _=>0)) (Q.goal L s) := by
  apply (h.shift zero_le_one _ _).raise (one_mul _).le
  · rintro (k|j|j)
    · exact h.nonneg (Sum.inl k)
    · exact h.nonneg (Sum.inr (.inl j))
    exact ht
  rintro (k|j|j) <;> rw [one_mul] <;> first| exact hv| exact le_rfl
-- actual expansion buys Z=betaF^r0 after L, r0≥0 prescribed after clocks (may depend on finite request).
lemma arm (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) : ∃ n:ℕ, ∀ (L:Side), n≤L.val →
    ∀ (D:Patch), D.Branches P.bind G → ∀ (r0:ℝ), 0≤r0 → ∀ (i:ℕ) (χ:Chi) (W:ℝ), 0 < W → ∀ (μ:ℝ), 0<μ → ∀ (o:Target.Order G W) (v w : ℝ→ℝ),
    Rate G L (-(1/2)) v → (∀ᶠ x in atTop,0≤v x) → Rate G L (-(1/2)) w → ∃ (C':ℝ) (r:ℝ→ℝ), 0≤C' ∧ Rate G L 0 r ∧
    ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T: Tube G S), S.patch=D → Stamp T → ∀ (R:Rep G f) (C:ℝ) (H:Cash W x μ L Q o C T R),
      ∃ Ξ:Utopia H i (v x) (w x) (r x) C' χ, WarnBudget (betaF G x L^r0) Ξ := by
  obtain ⟨t,hT,ht⟩:= exists_between Q.start
  obtain ⟨n,hn⟩:= Clutch.pay_busy P Q hT (ht.trans Q.stop)
  refine ⟨n,fun L hL D hd r0 hr0 i χ W hw μ hm o v w hv hwV hW=>?_⟩
  obtain ⟨C,hC,hΨ⟩:= Clutch.chimney P D L hd o.K o.γ W o.a χ i Q.table_exists hv hwV hW μ o.indexPay o.f o.large hw o.gamma
  obtain ⟨B,J,hB,hJ,hv',h⟩:= hn L hL D hd i χ W o v w hv hwV hW
  obtain ⟨A,hA,hy,hQ⟩:=Clutch.ash G L χ i hW hv W o.a Q.halo (by have h:=Q.buys; omega)
  obtain ⟨Y,hY,hF⟩:= Coat.alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (2*(t-r0)-1) (half_pos o.rare)
  let g x:= betaF G x L ^ t; let Z x:= B x+A x; have hZ x:1≤Z x:= (hv' x).trans (le_add_of_nonneg_right (hy x))
  have hp:0≤ Q.relative := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
  let u := Coat.topStorm D+1; have hu : 0 ≤ u := by unfold u; linarith [topStorm_one D]
  obtain ⟨b,hb,hH⟩:= exponent_fee G L Q.halo Q.relative Q.ε t u hp g Rate.power
  refine ⟨C,Z,hC,hB.add hA,?_⟩
  filter_upwards [hΨ,h,hQ,hF,(YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1,hY (2*(t-r0)) (by linarith),Q.pay_for L hm hC,(hJ.add (hJ.add hb)) Q.rate ht]
    with x hΨ h hQ he hβ hV hA hv c f S T hS hF R C' H
  have hΓ:= H.laws.data; have hh:= H.laws.intake
  have hΘ: 0<betaF G x L:=by have he:=hh.height; rw [hΓ.funds.length_eq] at he; linarith
  have hg:0≤g x:= by unfold g; positivity
  have h' := (hΓ.localP)
  obtain ⟨V,y,H'⟩:= h _ _ S T hΓ.funds hS hF h' hΓ.access R hh
  have hΞ:=hH x c f S hΓ.funds.length_eq (by have h:= hΓ.room.sight; omega) (mul_nonneg hu hg)
  let a:=betaF G x L^(t-r0); let Λ:=betaF G x L^r0
  have ha:0≤a:=Real.rpow_nonneg hΘ.le _
  have hΛ:g x=Λ*a:=by unfold g Λ a; rw [← Real.rpow_add hΘ]; ring_nf
  have hm:= (ratesCombine H'.first H'.hair hΞ).raise ((le_abs_self _).trans hv)
  have hb : u*a ≤ u*g x:= mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hβ (by linarith only [hr0])) hu
  refine ⟨⟨V,y,u,hu,a,ha,hF,hZ x,(by rw [hΓ.funds.length_eq]; exact hA R.beta (hΓ.funds.length_eq ▸ hh.window.1)),
    shrink (mul_nonneg hu ha) hb hm,?_,?_⟩,?_⟩
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
  · intro F X ht hK _ hp K
    have hV' : betaF G x L^(2*(t-r0))=a^2 := by unfold a; rw [mul_comm, Real.rpow_mul hΘ.le, Real.rpow_two]
    exact (he.2 c f S T F X ht hΓ.funds.length_eq (h' F X ht hK hp).sails R (ht.symm ▸ hh) K).trans
      (pow_le_pow_left₀ he.1 (((le_abs_self _).trans hV).trans_eq hV') _)
  unfold WarnBudget; change Sales (radiusB x) Q.relative Q.ε (footprints T R Q.halo (radiusB x)) (rates V y (u*(Λ*a))) _ _
  rw [← hΛ]; exact hm
end YM.ConnectedActivityE6.Blaze.Thermal1020
