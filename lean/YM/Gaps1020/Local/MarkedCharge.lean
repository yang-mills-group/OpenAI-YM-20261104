import YM.Gaps1020.Local.MarkedGerm
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Charm
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
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
open PhysicalNext.Repeat.Lotus PhysicalNext.Repeat.Daisy
section credit
-- Generalize Gnomon.acreage & Charm. Each marked angular appointment
-- has an unconditional paid factor along the path; Healthy applies at
-- the combined halo. A Crash failure for ANY non-substituted warning
-- head (there are no substituted warnings) pays zero; otherwise charge
-- span once per mark address and once per untouched head, no arity cost.
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {U:E→Config G c} {x:E} {w:E→Directions G f} {g:E→Air f G}
variable {H : Cash W s μ L Q o C T R} (Ξ:Utopia H j v d r q χ)
lemma remainBlaze (p:Molecule S)(M:Team R): blaze (others M p) = blaze p := by
  ext i; simp only [blaze, mem_toRight, others]; refine ⟨fun h=> sdiff_subset h, fun h=> Finset.mem_sdiff.mpr ⟨h,?_⟩⟩; intro h; obtain ⟨i',hi',hb'⟩:=mem_image.mp h; cases hD:i'.turn <;> rw [hD, Wing.badge] at hb' <;> simp at hb'
lemma teamOpens (p:Molecule S)(M:Team R)
    (hc:M.signs S⊆p) (ht:troupe T R Q.halo (radiusB s) p)(hx:X.x=s)(hk:X.width=o.K)(hF:X.χ=χ)(hm:X.manifest)(hv:Healthy (Pressure.temp X.x) (H.unionP p) X.V)
    (hU: Mode U x j v)(hr: Clutch X z o.a R.beta d x j U w g) (hB:0≤B)(hT:∀ i∈M.own, Brush j (i:Leaf R).weight (B*spanW T R X.B Q.halo (i.turn.badge S)) (fun a=> i.fond (vary X (U a)) o.a (w a) (X.input (worldZ X R.beta z))) x):
    let K':=M.weight*∏ i∈others M p,Ξ.tag i
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun _=>K') z) ((r+B)*(2*H.shapeW p)) (fun u=> seats p R M Q.table W o.a Q.halo (vary X (U u)) (g u)) x:=by
  intro K'
  let S':= others M p; let I:= X.catastrophe (o.ξ/2) R.beta (blaze p); let Z a:= vary X (U a)
  let V':= X.input (worldZ X R.beta z)
  let f (i:Leaf R) a:= i.fond (Z a) o.a (w a) V'
  let t i a:= Polar.ember (Z a) o.a R W Q.table (w a) V' (g a) (own p) Q.halo i
  have h : (fun u=> seats p R M Q.table W o.a Q.halo (Z u) (g u))=ᶠ[𝓝 x] fun a=> (∏ i∈M.own,f i a)*∏ i∈S',t i a:=by
    filter_upwards [hr.patch] with u h; unfold seats floating; rw [if_pos hc, hr.moving u]; let hU:=plastic h hr.pulse
    exact congr_arg₂ (·*·) (prod_congr rfl (fun i _=> i.canv (Z u) _ _ _ hU)) (prod_congr rfl fun i _=> hU.reeled (show Room P S _ (Z u).x from hx.symm ▸ H.laws.data.room) W _ _ _ (show Intake P _ (Z u).x R from hx.symm ▸ H.laws.intake) i (g u))
  apply Brush.shimmy _ h
  have hA:0<r:=zero_lt_one.trans_le Ξ.active
  have hF'(i:Head S)(hi:i∈ p): Brush j (Ξ.tag i) (r*spanW T R X.B Q.halo i) (t i) x:=by
    have h:= Ξ.stream E _ X U w g x z hx hk hF hm hU hr (own p) i (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hi) hv)
    unfold Utopia.tag; rw [← show X.B=radiusB s from congr_arg radiusB hx]; exact h
  have hz(i:Head S)(hi:i∈p):0 ≤ spanW T R X.B Q.halo i:= nonneg_of_mul_nonneg_right (hF' i hi).pos hA
  let l(i:Head S):=(r+B)*spanW T R X.B Q.halo i
  by_cases hy : z∈I
  · rw [Set.indicator_of_mem hy]
    have hZ' (i:Leaf R) (hi:i∈M.own): Brush j i.weight (l (i.turn.badge S)) (f i) x:= (hT i hi).climb le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (hz _ (hc (mem_image_of_mem _ hi))))
    have hY (i:Head S)(hi:i∈S'): Brush j (Ξ.tag i) (l i) (t i) x:= (hF' i (sdiff_subset hi)).climb le_rfl (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (hz _ (sdiff_subset hi)))
    apply ((Brush.all_prod M.own f _ _ hZ').paints (Brush.all_prod S' t _ _ hY)).climb le_rfl
    rw [← sum_image (f:=l) (fun i hi j hj h=> M.alone hi hj (Team.badged S h)),show (M.own.image (fun i=> i.turn.badge S))= M.signs S from rfl, add_comm,
      Finset.sum_sdiff hc]; unfold l; rw [← Finset.mul_sum, show X.B=radiusB s from congr_arg _ hx]; exact mul_le_mul_of_nonneg_left (Utopia.worthy p ht) (add_nonneg hA.le hB)
  rw [Set.indicator_of_notMem hy]; refine Brush.zi ?_ le_rfl (mul_nonneg (add_nonneg hA.le hB) (mul_nonneg zero_le_two (H.positive_volume p)))
  unfold I catastrophe Poll.Crash at hy; change ¬ (∀ i∈_,∃ j, _≤_ ∧ _≤_) at hy; push Not at hy
  obtain ⟨i,hi,hp'⟩:=hy; rw [← remainBlaze p M] at hi
  have hh:=hr.sleek (show Cash W X.x μ L Q o C T R from hx.symm ▸ H) hU Ξ.clock hm hk i (fun i hi =>(hp' i hi).le) (own p)
  filter_upwards [hh] with v hZ
  exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (mem_toRight.mp (mem_toRight.mp (mem_toRight.mp hi))) hZ)

variable {B':ℝ}{I : Finset (Bond f)}
lemma teamAccent (p:Molecule S)(M:Team R) (hc:M.signs S⊆p)(ht:troupe T R Q.halo (radiusB s) p)(hx:X.x=s)(hk:X.width=o.K)(hF:X.χ=χ)(hm:X.manifest)(hv:Healthy (Pressure.temp X.x) (H.unionP p) X.V)
    (hU: Mode U x j v)(hr: Clutch X z o.a R.beta d x j U w (fun i=> course X A R.beta z (U i))) (hB:0≤B)(hT:∀ i∈M.own, Brush j (i:Leaf R).weight (B*spanW T R X.B Q.halo (i.turn.badge S)) (fun a=> i.fond (vary X (U a)) o.a (w a) (X.input (worldZ X R.beta z))) x)
    (hS: Brush j 1 (B'*facescale I z^k) (fun i=> scalp I X (U i) R.beta A z) x)(h':0≤B') :
    let K':=M.weight*∏ i∈others M p,Ξ.tag i
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun z=> K'*(1+B'+2*(r+B))^j*(1+H.shapeW p)^j*facescale I z^(k*j)) z) 1
      (fun i=> teamWeightRecoil I X (U i) A Q.table p R M (emptyTeamData M p) W o.a Q.halo z) x := by
  intro P'; have hD:=(hS.paints (teamOpens Ξ p M hc ht hx hk hF hm hv hU hr hB hT)).trim
  unfold teamWeightRecoil; simp_rw [lit]; refine hD.climb ?_ le_rfl; by_cases h':z∈X.catastrophe (o.ξ/2) R.beta (blaze p)
  swap; · rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h',mul_zero,zero_mul]
  rw [Set.indicator_of_mem h', Set.indicator_of_mem h',one_mul]; change P'* _ ≤ _
  let f:=facescale I z; let g := r+B; let D:=1+H.shapeW p; have ht':1≤g:=Ξ.active.trans (le_add_of_nonneg_right hB); have hF:1≤f:= (Flux.expenses ..).1; have hv':1≤D:=le_add_of_nonneg_right (H.positive_volume p)
  have h₁:1≤ f^k:= one_le_pow₀ hF; have h₂ : 1+(B'*f^k+g*(2*H.shapeW p))≤(1+B'+2*g)*D*f^k:=by
    have hc : f^k ≤ D*f^k:= le_mul_of_one_le_left (zero_le_one.trans h₁) hv'
    have hS:H.shapeW p ≤ D*f^k:= (show H.shapeW p ≤ D from le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (zero_le_one.trans hv') h₁)
    have ha:1≤ D*f^k:= h₁.trans hc
    -- nlinarith
    nlinarith only [mul_le_mul_of_nonneg_left hc ‹0≤B'›, mul_le_mul_of_nonneg_left hS (zero_le_one.trans ht'),ha]
  have he : 0 ≤ 1+(B'*f^k+g*(2*H.shapeW p)):=add_nonneg zero_le_one (add_nonneg hS.pos (mul_nonneg (zero_le_one.trans ht') (mul_nonneg zero_le_two (H.positive_volume p))))
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he h₂ j) (show 0≤P' from mul_nonneg M.profit (prod_nonneg fun _ _=>Ξ.tagged _))).trans_eq ?_
  rw [mul_pow,mul_pow,pow_mul]; unfold f g D; ring
end credit
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
