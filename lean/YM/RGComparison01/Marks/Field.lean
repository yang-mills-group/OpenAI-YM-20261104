import YM.RGComparison01.Marks.Flask
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ Λ μ s κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Bloch Laurent Progress.StationaryScenes Green Census Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
open YM.RGComparison01
namespace Team
variable (M : Team R) (X : Coat T F) {U : Cash W s μ L Q o C T R}
variable {E:Type} {d C' D A B Y v :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia U j v d r C' χ}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {x:E} {z:Air f G} {V:E → Config G c} {V':E→Directions G f} {D':ℝ} {b:Head S → ℝ}
    {g:E→Air f G}
lemma no_panic (N:Molecule S) (i:WarningAt c f) (h:i∈ blaze N) : Sum.inr (.inr (.inr i))∈ N\M.signs S := by
  refine Finset.mem_sdiff.mpr ⟨mem_toRight.mp (mem_toRight.mp (mem_toRight.mp h)),fun h=>?_⟩
  obtain ⟨j,hj,H⟩:=mem_image.mp h; cases h : j.turn <;> simp [h,Wing.badge] at H
lemma footprint_post (N:Molecule S) (h:troupe T R Q.halo (radiusB s) N) (ha:M.signs S ⊆ N) (hf:X.x=s) (Z:ℝ) (hZ:0≤Z):
    (∑ i∈M.own,Z*spanW T R X.B Q.halo (i.turn.badge S))+(∑ i∈ N\M.signs S,Z*spanW T R X.B Q.halo i)≤ Z*(2*U.shapeW N) := by
  let F i:= Z*spanW T R X.B Q.halo i
  have hh: (∑ i∈ M.signs S,F i)= ∑ i∈M.own,Z*spanW T R X.B Q.halo (i.turn.badge S):= by
    refine sum_image (f:=F) ?_; intro a ha b hb h; exact M.alone ha hb (badged S h)
  rw [← hh]; change (∑ i∈M.signs S,F i)+(∑ i∈ N\M.signs S,F i) ≤ _
  rw [add_comm (∑ i∈ M.signs S,F i), Finset.sum_sdiff ha]; unfold F; rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ hZ; rw [show X.B=radiusB s from congr_arg radiusB hf]; exact Utopia.worthy N h

lemma felt {g:E→Air f G} (he : troupe T R Q.halo (radiusB s) p) (hA:M.signs S ⊆ p) (k:Finset ℕ) (hX:X.x=s)(ht:X.width=o.K)(hv:X.manifest)(hY:Healthy (Pressure.temp X.x) (U.unionP p) X.V)(hV : Mode V x j v) (hr:Clutch X z o.a R.beta d x j V V' g)
    (hB : Cloak Ω D' D' b X z V V' g x) (hh:0≤D') : Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun _=> M.weight*∏ i∈p\M.signs S,b i) z) (D'*(2*U.shapeW p))
      (fun t=> M.floral (vary X (V t)) p W o.a Q.table k Q.halo (g t)) x:= by
  let Z (t:E):=vary X (V t); let a (i:Leaf R) t := i.fond (Z t) o.a (V' t) (X.input (worldZ X R.beta z))
  let u i (t:E):= Polar.ember (Z t) o.a R W Q.table (V' t) (X.input (worldZ X R.beta z)) (g t) k Q.halo i
  let f t:= (∏ i∈M.own,a i t)*∏ i∈p\M.signs S,u i t
  have hF : (fun t=> M.floral (vary X (V t)) p W o.a Q.table k Q.halo (g t))=ᶠ[𝓝 x] f:= by
    filter_upwards [hr.patch] with y h; unfold Team.floral; rw [if_pos hA]; unfold f u a Polar.floating Team.paidU Leaf.paidU; simp_rw [hr.moving y]; have hv':= plastic h hr.pulse
    exact congr_arg₂ (·*·) (Finset.prod_congr rfl fun j _=> j.canv (Z y) _ _ _ hv') (Finset.prod_congr rfl fun i hi=> hv'.reeled (show Room P S _ (Z y).x from hX.symm ▸ U.laws.data.room) W _ _ _ (show Intake P _ (Z y).x R from hX.symm ▸ U.laws.intake) i (g y))
  apply Brush.shimmy _ hF
  let K:= X.catastrophe (o.ξ/2) R.beta (blaze p)
  by_cases hy:z∈ K
  · rw [Set.indicator_of_mem hy]; exact ((Brush.all_prod M.own a _ _ fun i _=>hB.pip i).paints (Brush.all_prod _ u _ _ fun i hi=> hB.posts k i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem U.supportP (Finset.mem_sdiff.mp hi|>.1)) hY))).climb le_rfl (M.footprint_post X _ he hA hX D' hh)
  rw [Set.indicator_of_notMem hy]; refine Brush.zi ?_ le_rfl (mul_nonneg hh (mul_nonneg zero_le_two (U.positive_volume p)))
  unfold K catastrophe Poll.Crash at hy; change ¬ (∀ i∈_,∃ j, _≤_ ∧ _≤_) at hy; push Not at hy
  obtain ⟨i,hi,hp'⟩:=hy
  have hc : Cash W X.x μ L Q o C T R:= hX.symm ▸ U; have hx:=hr.sleek hc hV Ω.clock hv ht i (fun i hi =>(hp' i hi).le) k
  filter_upwards [hx] with v hZ
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (M.no_panic p i hi) hZ)

lemma trail_budget (he : troupe T R Q.halo (radiusB s) p)(hp : M.signs S⊆p)(hX:X.x=s)(ht:X.width=o.K)(hv:X.manifest)(hP:Healthy (Pressure.temp X.x) (U.unionP p) X.V)(hV : Mode V x j v)(hr: Clutch X z o.a R.beta d x j V V' (fun i=>course X A R.beta z (V i)))
    (hC : Cloak Ω D' D' b X z V V' (fun i=>course X A R.beta z (V i)) x) (hB : 1≤D')
    {I:Finset (Bond f)} (hT:Brush j 1 (B*facescale I z^k) (fun i=> scalp I X (V i) R.beta A z) x) (hh:0≤B) (h : ∀ i,0≤ b i) :
    let K':=M.weight*∏ i∈p\M.signs S,b i
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun z=> K'*(1+B+2*D')^j*(1+U.shapeW p)^j*facescale I z^(k*j)) z) 1
      (fun i=> M.roof X p I (V i) A Q.table W o.a Q.halo z) x := by
  intro P'; have hD := (hT.paints (M.felt X he hp (Matter.own p) hX ht hv hP hV hr hC (zero_le_one.trans hB))).trim
  refine hD.climb ?_ le_rfl; by_cases hx:z∈X.catastrophe (o.ξ/2) R.beta (blaze p)
  swap; · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,mul_zero,zero_mul]
  rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,one_mul]; change P'* _ ≤ _
  let f:=facescale I z; let D:=1+U.shapeW p; have ht':1≤D':=hB; have hF:1≤f:= (Flux.expenses ..).1; have hv':1≤D:=le_add_of_nonneg_right (U.positive_volume p)
  have h₁:1≤ f^k:= one_le_pow₀ hF; have h₂ : 1+(B*f^k+D'*(2*U.shapeW p))≤(1+B+2*D')*D*f^k:=by
    have hc : f^k ≤ D*f^k:= le_mul_of_one_le_left (zero_le_one.trans h₁) hv'
    have hS:U.shapeW p ≤ D*f^k:= (show U.shapeW p ≤ D from le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (zero_le_one.trans hv') h₁)
    nlinarith only [mul_le_mul_of_nonneg_left hc hh, mul_le_mul_of_nonneg_left hS (zero_le_one.trans ht'), h₁.trans hc]
  have he : 0 ≤ 1+(B*f^k+D'*(2*U.shapeW p)):=add_nonneg zero_le_one (add_nonneg hT.pos (mul_nonneg (zero_le_one.trans ht') (mul_nonneg zero_le_two (U.positive_volume p))))
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he h₂ j) (show 0≤P' from mul_nonneg M.profit (prod_nonneg fun i _=>h _))).trans_eq ?_
  rw [mul_pow,mul_pow,pow_mul]; unfold f D; ring
end Team
end YM.PhysicalNext.Repeat.Lotus
