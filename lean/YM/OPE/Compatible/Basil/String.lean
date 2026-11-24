import YM.OPE.Compatible.Basil.Sloop
/-!
# L² mark Q kernel
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
def hCost (a:ℝ):Head S→ℝ := Mixed.costs S Q.halo (radiusB x) (steamP S (Q.costs L μ R.beta x C)) (clapper H a)
-- generalized Weaving
lemma soundP {s : ℝ}(p : Molecule S) : (∏ i∈p,hCost H s i) = s^(blaze p).card*(∏ i∈p,H.fair i) := by
  rw [cumulate p (hCost H s), cumulate p H.fair]
  let X := p.toRight; let Y := X.toRight
  have hx : (∏ i∈X,hCost H s (.inr i)) = s^(blaze p).card*(∏ i∈X,H.fair (.inr i)) := by
    rw [cumulate X,cumulate X]
    let f (i) := hCost H s (Sum.inr (Sum.inr i)); let g i := H.fair (Sum.inr (Sum.inr i))
    have he : (∏ i∈Y,f i) = s^(blaze p).card*(∏ i∈Y,g i) := by
      rw [cumulate Y,cumulate Y, ← Finset.prod_const]
      change _ = (∏ _i∈Y.toRight, _)*((∏ i ∈ Y.toLeft, H.w i)* ∏ i∈Y.toRight, _)
      change (∏ i∈Y.toLeft, H.w i)* (∏ _i∈ Y.toRight, s * topStorm S.patch) =
        (∏ _i∈Y.toRight, s)* ((∏ i∈Y.toLeft, H.w i)*∏ _i∈Y.toRight,topStorm S.patch)
      rw [Finset.prod_mul_distrib]; ring
    change (∏ i∈X.toLeft,H.v i)*(∏ i∈Y,f i)=_* ((∏ i∈X.toLeft,H.v i)*∏ i∈Y,g i)
    rw [he]; ring
  rw [hx]; rw [mul_left_comm]; rfl
lemma ring_cast {s : ℝ}{n:ℕ}
 (hp:(arcs Q L μ R.beta x C).Buy S.patch.L Q.halo (radiusB x))
 (b : Molecule S→ℝ) (hv:0≤ b)(c':ℝ)(hc:0≤c') (H' : castCash H M s)
 (h : ∀ p,b p≠0→H.ticketsP 0 n 0 p ∧ M.turn.badge S∈p∧ b p ≤ c'* (M.weight*∏ i∈p.erase (M.turn.badge S), hCost H s i))
 (y : Site c)(hy:∀ p,b p≠0→ y∈H.unionP p) : SumBudget (fun p:H.ThinP=> b p.val * Real.exp (Q.exp * coverNumber (radiusB x) (H.unionP p.val))) (c'*(jewelDebt M.tin_ Q L x)*(arcs Q L μ R.beta x C).ceiling 0 0 n 0):=by
   let m:=radiusB x; let a:= M.turn.badge S
   let D:= M.tin_; let v:=clapper H s; let u:= colly v M.tin_ Q L x; let r:=jewelDebt M.tin_ Q L x
   have hd := (dew M.tin_ H).2
   have hh:=Mixed.mixed_hit S Q.halo m (arcs Q L μ R.beta x C) H.birth u (ConnectedActivityE6.lengths T R) (steamP S (Q.costs L μ R.beta x C)) hp H' 0 0 n 0 y
   have hc' :=budget_scale (mul_nonneg hc hd.1) (budget_pull (fun p:H.ThinP=>p.val) Subtype.val_injective hh)
   refine budget_mono hc' (fun i=>mul_nonneg (hv _) (Real.exp_pos _).le) fun i=> ?_
   by_cases hz:b i.val=0
   · rw [hz,zero_mul]; exact hc'.1 i
   obtain ⟨hV,hA,hℓ⟩:= h i.val hz
   change _ ≤ (c'*r)*(if y∈H.unionP i.val then _ else 0)
   rw [if_pos (hy _ hz),Mixed.selected, if_pos (show Mixed.Allowed S Q.halo m (arcs Q L μ R.beta x C) _ _ _ _ _ i.val from hV),Mixed.Price,pow_zero,mul_one, ← mul_prod_erase _ _ hA,← mul_assoc _ _ (Real.exp _)]
   let v₀:= hCost H s; refine (mul_le_mul_of_nonneg_right hℓ (Real.exp_pos _).le).trans_eq (congr_arg (fun x:ℝ=> x*Real.exp _) ?_); have ht : M.weight=r * jewel M.tin_ Q L x:=hd.2
   change c'*(M.weight * ∏ j∈i.val.erase a, v₀ j)=_*(needle M.tin_ H C v a*∏j∈i.val.erase a,needle M.tin_ H C v j); rw [ht,show needle _ H C v a=_ from (show needle M.tin_ H C v a=jewel M.tin_ Q L x by unfold a; rw [← M.colorCue.2,nose])]
   have hE : (∏ j∈i.val.erase a, needle M.tin_ H C v j)=∏ j∈i.val.erase a, v₀ j:=prod_congr rfl fun j hj=> sleeve M.tin_ H _ _ _ (M.colorCue.2.symm ▸ (show j≠a from ne_of_mem_erase hj))
   rw [hE]; ring
end YM.PhysicalNext.Repeat.Aroma.Leaf
