import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Gnomon
import YM.LocalLTE.Marked.Booth

/-! Premiums use body score on every hold. No unmasked Taylor assumes on masks. -/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Daisy
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R)(X:Coat T F)(H:Cash W x μ L Q o C T R) (a' : ℝ) (u:ConnectedActivityE6.Alphabet c f→ℝ)
    {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)

-- Unmasked full stencil angular cost, even on ZERO normative
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V : E→ Config G c} {y:E} {f':E→ Directions G f} {z':Air f G} {g:E→Air f G}
lemma portfolioQ (he : troupe T R Q.halo (radiusB x) p)(hA : M.signs S ⊆ p)(k:Finset ℕ) (hX:X.x=x)(ht:X.width=o.K)(hF:X.χ=χ)(hu:X.manifest)(hv:Healthy (Pressure.temp X.x) (H.unionP p) X.V)(hV : Mode V y j v)(hr: Clutch X z' o.a R.beta d y j V f' g) (hB : 0≤B)
    (hC : ∀ x : Leaf R, x∈M.own→Brush j x.weight (B*spanW T R X.B Q.halo (x.turn.badge S)) (fun t=> x.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z'))) y) :
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun _=>M.weight*∏ i∈p\M.signs S, Ξ.tag i) z') ((r+B)*(2*H.shapeW p))
      (fun t=> M.qlocal4a_floret (vary X (V t)) p W o.a Q.table k Q.halo (g t)) y:=by
  let u i (t:E):=Polar.ember (vary X (V t)) o.a R W Q.table (f' t) (X.input (worldZ X R.beta z')) (g t) k Q.halo i
  let a (M:Leaf R) t:=M.fond (vary X (V t)) o.a (f' t) (X.input (worldZ X R.beta z')); let s:=p\M.signs S
  let F t:= (∏ j∈M.own,a j t)* ∏ i∈s,u i t
  have hU : (fun t=>M.qlocal4a_floret (vary X (V t)) p W o.a Q.table k Q.halo (g t))=ᶠ[𝓝 y] F:=by
    filter_upwards [hr.patch] with z hv
    unfold Team.qlocal4a_floret; rw [if_pos hA]; unfold F u a Polar.floating Team.paidU Leaf.paidU; simp_rw [hr.moving z]
    let Z:= vary X (V z); have hv' := plastic hv hr.pulse
    exact congr_arg₂ (·*·) (Finset.prod_congr rfl (fun i _=>i.canv Z _ _ _ hv')) (Finset.prod_congr rfl fun i hi=> hv'.reeled (show Room P S _ Z.x from hX.symm ▸ H.laws.data.room) W _ _ _ (show Intake P _ Z.x R from hX.symm ▸ H.laws.intake) i (g z)) -- invalid p name
  apply Brush.shimmy _ hU
  let S' := X.catastrophe (o.ξ/2) R.beta (blaze p)
  have hΞ := Ξ.stream E _ X V f' g y z' hX ht hF hu hV hr; have ht' : r≥0:= zero_le_one.trans Ξ.active
  by_cases hy:z' ∈ S'
  · rw [Set.indicator_of_mem hy]
    have hh i(hi : i∈s) : Brush j (Ξ.tag i) (r*spanW T R X.B Q.halo i) (u i) y := by
      have hx:=hΞ k i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP (Finset.mem_sdiff.mp hi).1) hv)
      unfold Utopia.tag; rw [← show X.B=radiusB x from congr_arg radiusB hX]; exact hx
    apply ((Brush.all_prod M.own a _ _ hC).paints (Brush.all_prod _ u _ _ hh)).climb le_rfl
    let W i:=(r+B)*spanW T R X.B Q.halo i
    refine le_trans (add_le_add (Finset.sum_le_sum (g:=fun (i:Leaf R)=> W (i.turn.badge S)) ?_) (Finset.sum_le_sum (g:=W) (fun i hi=> mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) ?_))) ?_
    · intro i hi; apply mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ht')
      unfold spanW; cases i.turn <;> exact add_nonneg zero_le_one (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    · exact nonneg_of_mul_nonneg_right (hh i hi).pos (zero_lt_one.trans_le Ξ.active)
    have hM: (∑ i∈M.own,W (i.turn.badge S))+∑ i∈s,W i=∑ i∈p,W i:=by
       have he: (∑ i∈ M.signs S,W i)=∑ i∈ M.own,W (i.turn.badge S):= Finset.sum_image (fun i hi j hj hz=> M.alone hi hj (Team.badged S hz))
       rw [← he, add_comm, Finset.sum_sdiff hA]
    rw [hM, show (∑ i∈p,W i)=(r+B)*∑ i∈p,spanW T R X.B Q.halo i from (Finset.mul_sum ..).symm, show X.B=radiusB x from congr_arg radiusB hX]
    exact mul_le_mul_of_nonneg_left (Utopia.worthy p he) (add_nonneg ht' hB)
  rw [Set.indicator_of_notMem hy]; refine Brush.zi ?_ le_rfl (mul_nonneg (add_nonneg ht' hB) (mul_nonneg zero_le_two (H.positive_volume p)))
  unfold S' catastrophe Poll.Crash at hy; change ¬ (∀ i∈_,∃ j, _≤_ ∧ _≤_) at hy; push Not at hy
  obtain ⟨i,hi,hp'⟩:=hy
  have hc : Cash W X.x μ L Q o C T R:= hX.symm ▸ H; have hx:=hr.sleek hc hV Ξ.clock hu ht i (fun i hi =>(hp' i hi).le) k
  filter_upwards [hx] with v hZ
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi)),?_⟩) hZ)
  intro hp; obtain ⟨v,hu,hv⟩:= Finset.mem_image.mp (show Sum.inr (.inr (.inr i))∈ M.signs S from hp); cases he:v.turn <;> simp [he,Wing.badge] at hv -- `cases` generalization
end YM.PhysicalNext.Repeat.Daisy
