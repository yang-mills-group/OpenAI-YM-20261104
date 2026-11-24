import YM.OPE.Compatible.Basil.Door
/-!
# eventual parameters
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (Q: YM.ConnectedActivityE6.Target G P) (o : ConnectedActivityE6.Target.Order G W) (L : Side)
-- Offer required menus. Always L fixed.
structure Peals (Q:YM.ConnectedActivityE6.Target G P)(o:ConnectedActivityE6.Target.Order G W)(D:Patch)(L:Side)(μ x s C:ℝ) : Prop where
  scalar : 0 ≤ s
  visible : ∀ {c f: Side}{S:StepData c f}{R:Rep G f} {T:Tube G S}, ∀ H:Cash W x μ L Q o C T R,S.patch=D →
     R.p.B≤ 2*radiusB x ∧ (arcs Q L μ R.beta x C).Buy S.patch.L Q.halo (radiusB x)∧ (swing Q L μ R.beta x C).Buy S.patch.L Q.halo (radiusB x) ∧ (∀ M:Leaf S R,castCash H M s) ∧
       ∀ {F:Forest S.ratio}(X:Coat T F), X.x=x → X.manifest → X.width=o.K → ∀ A:Finset (WarningAt c f),X.dice.real (X.catastrophe o.ξ R.beta A)≤(s^2)^A.card
lemma summer (hh:foam Q L)(hμ:0<μ) (D:Patch) : ∀ C,∀ᶠ x in atTop,∃ s,Peals Q o D L μ x s C:=by
   let z:= Q.rate-2
   let g(x):=betaF G x L^z
   obtain ⟨v,hV,h⟩:= alarm_bills (η:=o.eta) (r:=o.gap) (Q:=o.ample) (Y:=o.indexPay) P L (2*z-1) o.rare
   have hz: Rate G L z g:= Rate.power
   have hP:0≤Q.relative:=by unfold ConnectedActivityE6.Target.relative; linarith [Q.usable,Q.bound,Q.pos]
   let y:=topStorm D
   obtain ⟨p,hp,H⟩:= exponent_fee G L Q.halo Q.relative Q.ε z y hP g hz
   intro C'
   filter_upwards [h,hV (z*2) (by linarith), hp _ (show z<Q.rate by unfold z; linarith),Delay.shift_pos G L,
    arcsV Q L hμ, sailsW Q L hμ,Fees.horizons G L Q.halo (a:=1) (σ:=3) (ε:=1) (by norm_num) zero_le_one (by norm_num)] with x h hx H₀ hG hS hT hB
   have hv:0≤g x:=by unfold g; positivity
   refine ⟨g x,hv,fun {c f S R T} A he => ?_⟩
   have hr:= A.laws.data; have hu:= A.laws.intake; have hm:= hr.funds.length_eq
   have hl: (swing Q L μ R.beta x C').Buy S.patch.L Q.halo (radiusB x):=hm.symm ▸ hT R.beta C' (hm ▸ A.laws.acquired)
   have hf:R.p.B≤ 2*radiusB x:=by rw [hu.sizes, hm]; exact hB.2.1
   have he' : Sales (radiusB x) Q.relative Q.ε (field_support S (radiusB x) Q.halo) (fun _=>g x*topStorm S.patch) (fun _=>0) (Q.goal L x):=by
     have hy : y= topStorm S.patch := by unfold y; rw [he]
     have hY:=(H x _ _ S hm hB.1 (mul_nonneg (zero_le_one.trans (Coat.topStorm_one D)) hv)).raise ((le_abs_self _).trans H₀) -- hy no
     simp_rw [mul_comm y,hy] at hY; exact hY
   refine ⟨hf,hm.symm ▸ hS _ _ (hm ▸ hl),hl,fun M=> M.withinCast A hh hf he',fun {F} X hs ha ht p=>?_⟩
   have hh := h.1; have hy:v x≤ (g x)^2:=by
      unfold g;apply ((le_abs_self _).trans hx).trans_eq; norm_cast; rw [Real.rpow_mul hG.le,Real.rpow_two] --
   exact (h.2 _ _ S T F X hs hm (hr.localP F X hs ht ha|>.sails) R (hs.symm ▸ hu) p).trans (pow_le_pow_left₀ hh hy _)
lemma stretchY (hμ:0<μ) (j:ℕ)(he : 0<Q.exp) : ∀ᶠ x:ℝ in atTop, ((radiusB x*2+1:ℕ):ℝ)^4*(Q.overture L μ x j*(1-(1/2:ℝ))⁻¹)≤ Q.exp:=by
   have hE:= Q.rate_none L hμ 0 j 0
   have hk : Rate G L Q.rate (fun x=> ((radiusB x*2+1:ℕ):ℝ)^4*(Q.overture L μ x j*(1-(1/2:ℝ))⁻¹)) := by
      simp_rw [Nat.cast_add,Nat.cast_mul]; push_cast; exact (by convert! (((Rate.radius_price (G:=G) (L:=L)|>.mul_right 2).add (Rate.const 1)|>.pow 4).mul (hE.mul_right ((1-(1/2:ℝ))⁻¹))) using 1; norm_num)
   exact (hk.below Q.stop Q.exp he).mono fun i hi=> (le_abs_self _).trans hi
end YM.PhysicalNext.Repeat.Aroma
