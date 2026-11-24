import YM.OPE.Compatible.Basil.Cream
/-!
# Additional alarm credit. Charge marker-less warning set under L² pairing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma.Leaf
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Itinerary Gas Ursell Trees Animals Corona Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (X:Coat T F) (H:Cash W x μ L Q o C T R) (M:Leaf S R)
def arcs (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(μ β x C : ℝ):Mixed.Costs:={ swing Q L μ β x C with
   optionalHit := (swing Q L μ β x C).optionalHit + Q.goal L x
   rootHit:= (swing Q L μ β x C).rootHit + Q.goal L x
   q:= 3/4 }
lemma arcsV (Q:YM.ConnectedActivityE6.Target G P)(L:Side)(h : 0<μ) : ∀ᶠ x in atTop,∀ β C,(swing Q L μ β x C).Buy L Q.halo (radiusB x)→ (arcs Q L μ β x C).Buy L Q.halo (radiusB x):=by
   let v x:=(arcs Q L μ 0 x 0).rootHit; have hv : Rate G L Q.rate v:= ((Q.rate_root (β:=0) (C:=0) L h).add (Rate.power.mul_right _)).add Rate.power
   have he:=Q.stop; let g(x:ℝ):= Trees.degreePrice (radiusB x) (v x) Q.δ
   have hp:Rate G L Q.rate g:=by
    unfold g Trees.degreePrice Trees.stretch; have hx:=width_rate G L 1 0; simp only [one_mul,add_zero] at hx
    simp_rw [div_eq_mul_inv]; simpa only [zero_add] using! (((hx.mul hv).mul_right _).mul_left _)
   filter_upwards [Delay.shift_pos G L,hp.below Q.stop _ (by norm_num:(0:ℝ)<3/4)] with x hx he β C hU
   have hu:0≤Q.goal L x:=by unfold ConnectedActivityE6.Target.goal; positivity
   refine {hU with
     γ:=hU.γ.trans_le (le_add_of_nonneg_right hu)
     combined:=le_trans (le_of_eq (add_assoc ..|>.symm)) (add_le_add_left hU.combined _)
     trees:=(le_abs_self (g x)).trans he
     grows:=by change 3/(4:ℝ)<1;norm_num }
local notation "Y" => H.birth
local notation "B₀" => (arcs Q L μ R.beta x C)
def clapper (s:ℝ): ConnectedActivityE6.Alphabet c f →ℝ := rates H.v H.w (s * topStorm S.patch)
local notation "μy" => steamP S (Q.costs L μ R.beta x C)
local notation "m₀" => radiusB x
def castCash (s:ℝ):= Accounts S Q.halo m₀ B₀ Y (colly (clapper H s) M.tin_ Q L x) (ConnectedActivityE6.lengths T R) μy
private lemma noneSales {B:ℕ}{D : Type}{z v:ℝ}(X:D→Support c)(W:D→ℕ):Sales B z v X (fun _=>0) W 0:=by
   refine ⟨fun _=> le_rfl,fun j=>?_⟩; simp [Reserves.tariff, SumBudget]
include H
lemma withinCast (hf:foam Q L)(hp:R.p.B≤2*m₀) (hs:Sales (radiusB x) Q.relative Q.ε (field_support S (radiusB x) Q.halo) (fun _=> a*topStorm S.patch) (fun _=>0) (Q.goal L x)):castCash H M a:=by
   have hE:= coco M.tin_ H hf hp H.opt _ _ H.armed
   let B:= radiusB x; let T':=clapper H a; let u:= colly T' M.tin_ Q L x; let v:=colly H.opt M.tin_ Q L x
   let w:=field_support S (radiusB x) Q.halo
   have hn i:0 ≤ u i:=by
     unfold u colly; split
     next h=> exact (dew M.tin_ H).1.le
     next h=> rcases i with i|i|i; exact H.earns (.inl i);exact H.earns (.inr (.inl i));exact hs.nonneg i
   refine ⟨hE.packetBound, hn,hE.extra,?_⟩
   intro p; have hx : Ac.Hit Y (radiusB x)
      (Reserves.tariff u (ConnectedActivityE6.lengths T R) (fun _=>0) (arcs Q L μ R.beta x C).reservePoly) (arcs Q L μ R.beta x C).head ((arcs Q L μ R.beta x C).optionalHit):= by
     let g:= rates (fun _=>0) (fun (_:LogIndex c f)=>0) (a*topStorm S.patch)
     let k:=ConnectedActivityE6.lengths T R; let ψ (u:ConnectedActivityE6.Alphabet c f→ℝ):=Reserves.tariff u k (fun _=>0) Q.ε
     have hQ:= ratesCombine (T:=T) (R:=R) (noneSales _ _) (noneSales _ _) hs; rw [zero_add,zero_add] at hQ
     intro y; refine budget_mono (budget_plus (hE.pays y) (hQ.hit y)) ?_ ?_
     · intro j; split; exact mul_nonneg (mul_nonneg (hn _) (Real.exp_pos _).le) (Real.exp_pos _).le; exact le_rfl
     intro i; unfold Costs.head; -- edit
     change (if y∈H.birth i then ψ u i*Real.exp _ else 0) ≤ (if y∈H.birth i then ψ v i*Real.exp _ else 0)+(if y∈H.birth i then ψ g i*Real.exp _ else 0)
     split_ifs with h; swap; · norm_num
     change ψ u i * Real.exp (Q.relative*(coverNumber B (H.birth i):ℝ)) ≤ ψ v i * Real.exp (Q.relative*(coverNumber B (H.birth i):ℝ)) + ψ g i * Real.exp (Q.relative*(coverNumber B (H.birth i):ℝ))
     rw [← add_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
     unfold ψ Reserves.tariff; rw [← add_mul]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
     by_cases h:i = sparkling c f M.tin_.turn
     · unfold u v colly; rw [if_pos h,if_pos h]; exact le_add_of_nonneg_right (hQ.nonneg _)
     unfold u v colly; rw [if_neg h,if_neg h]; rcases i with i|i|i
     · change H.v i ≤ _+0; rw [add_zero];exact le_rfl
     · change H.w i ≤ _+0; rw [add_zero];exact le_rfl
     change g (Sum.inr (Sum.inr i)) ≤ _+g (Sum.inr (Sum.inr i)); exact le_add_of_nonneg_left (H.earns _)
   exact hx p
end YM.PhysicalNext.Repeat.Aroma.Leaf
