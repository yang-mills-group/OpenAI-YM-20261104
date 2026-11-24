import YM.RGComparison01.Marks.DayStar
/-!
# Prices of the free coordinates, all stretches

 Upgrade Olive of E6 to polynomial witnesses
 required in the marked real payment. Invocation tools unchanged down to
 projections in that payment. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Gate

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge} {c f: Side} {S : StepData c f} {T:Tube G S} {P:Teller G}
open Metric 
private lemma all_whiteF (S : PathData G) (p : Clip) (R M) (a : Twin c) : plotted S p R M (1: Config G c) a=0 := by
  have he (n : ℕ) : shortenTerm S R M (1:Config G c) a.1 n=0 := by
    unfold shortenTerm; split
    next hv => simp [PathData.ellTerms, Work.F03.atSite_path,faceValue, SliceRows.trivial]
    exact rfl
  unfold plotted; split
  next => simp only [shorten,he,tsum_zero]
  simp [shoot,faceValue, SliceRows.trivial]
private lemma base_nil (h : P.Funds S T) (k : S.Choices) (i : Rod c f) (s : ℝ) : Scroll.freely T s 1 k i=0 := by
  unfold Scroll.freely baseStroke entryCost visual; rw [replica_one]
  have he (u : Twin c) : T.Xn (till s) (1 : Config G c) u=0 := all_whiteF ..
  rw [show S.prediction 1 k=(1:Config G c) from funext fun i=> Push.settled S (funds_branch h) i k]
  rcases i with i|i
  · simp only [Sum.elim,Tube.Xf,all_whiteF,canopyF,zip,he,map_zero,sum_const_zero,sub_zero]
  simp only [Sum.elim,canopyI,zip,Tube.Z,he,Pi.one_apply,inv_one,mul_one,G.curvature_unit,smul_zero,map_zero,sum_const_zero,sub_zero]

lemma promises (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) :
    ∃ (R:ℝ), 0<R ∧ ∃ (A : ℝ→ℝ), R≤1 ∧ RGComparison01.Geo G L A ∧ ∀ᶠ s : ℝ in atTop,
      ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T→ ∀ (k : S.Choices) (p : Rod c f),
      let g (v : ZipP G c f) := Scroll.freely T s (increment 1 v.1) k p
      ∀ x, ‖x‖≤R → Brush j (A s) 1 g x := by
  obtain ⟨r,v,hr,h1,hv,h⟩:= dressed P D hD j
  let f x:= shadowL P+maxima P L (till x); let g x:= hikeZ G v (till x) (dimLift P (till x) v)
  have ht := Geo.tilling (G:=G) (L:=L)
  have hf: Geo G L f:= (Geo.fixed _).joins (((Geo.balling ht).times (Geo.fixed _)).times (Geo.fixed _))
  let r' (x:ℝ):= (4:ℝ)+2*(till x:ℝ)
  have hr': Geo G L r':= (Geo.fixed _).joins ((Geo.fixed _).times ht)
  have hh: Geo G L (fun x => dimLift P (till x) v):= (((hr'.times (Geo.fixed _)).joins (Geo.fixed _)).joins (Geo.fixed _))
  let A x:= f x*(1+g x)^j
  refine ⟨r,hr,A,h1, hf.times (((Geo.fixed 1).joins (((((Geo.fixed 2).times ht).times (Geo.fixed _)).times (Geo.fixed _)).joins hh)).power j),
    Eventually.of_forall fun x c f S T hs ht k p x' hX=>?_⟩
  obtain ⟨h₁,-,-,-,h₂⟩:= h _ _ S T ht.funds hs x' hX k
  exact (grove ht.funds ht.length_eq h₁ k h₂ p _).trim

lemma prospect (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) {v : ℝ→ℝ}
    (h : RGComparison01.Fine G L v) (hp : ∀ᶠ x in atTop, 0≤v x) : ∃ F : ℝ→ℝ, RGComparison01.Fine G L F ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D→ Works P L x S T→ ∀ (k:S.Choices) (p:Rod c f)
    (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ Config G c) (z:E), Mode U z j (v x)→
      Clean (U z) x (focus S p) (radiusB x) → Brush j (F x) 1 (fun t=> Scroll.freely T x (U t) k p) z := by
  obtain ⟨R,hr,hV,hR,hv,hP⟩:= promises P L D hD (j+3)
  obtain ⟨F,hF,hG⟩:= dayStar P L j h hp; let B x:= F x+F x
  have hB:= hF.plus hF
  refine ⟨fun x=>(hV x+j.factorial*hV x)*B x,Fine.grind_left (hv.joins ((Geo.fixed _).times hv)) hB,?_⟩
  filter_upwards [hG,hP,hB.dividend.below (by norm_num) R hr,room G P L] with
    x H H' hx hf c f S T hs hh k p E _ _ U z hU hE
  have hp:=hf c f S T hh; have hX:=hp.sight
  let W (x' : Config G c) := Scroll.freely T x x' k p
  let g (v:ZipP G c f):= W (increment 1 v.1)
  obtain ⟨d,b,hθ,hA⟩:= H.2 c f S T hh _ U z (radiusB x/4) _ hU (by omega) (hE.shrink (by rw [separation_self]; omega))
  let V' i := (b i,(0:Directions G f)); let A:= hV x
  have hY : Brush j (B x) 1 V' z := Brush.pair hθ ((Brush.certified zero_le_one _).climb (show ‖(0:Directions G f)‖≤F x by rw [norm_zero]; exact H.1) le_rfl)
  have hx' := (le_abs_self _).trans hx
  have h1(i:ZipP G c f)(hi:i∈closedBall 0 R): Brush (j+3) A 1 g i:= H' c _ S T hs hh k p i (mem_closedBall_zero_iff.mp hi)
  have hh': V' z ∈ closedBall 0 R:= mem_closedBall_zero_iff.mpr (hY.bound.trans hx')
  have ha:=(h1 (V' z) hh').smaller (show j≤j+3 by omega); have hZ:=ha.nonneg
  have hz(i:ZipP G c f)(hi:i∈closedBall 0 R):DifferentiableAt ℝ g i:= by
      have h4 : (1:WithTop ℕ∞) ≤ (j+3:ℕ) := by exact_mod_cast (show 1≤j+3 by omega)
      exact (h1 i hi).smooth.differentiableAt (ne_of_gt (lt_of_lt_of_le zero_lt_one h4))
  have he(i:ZipP G c f)(hi:i∈closedBall 0 R): ‖fderiv ℝ g i‖ ≤ A:= by
      rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.1 (h1 i hi)).2 1 (by omega)
  have hg0 : g 0=0:= by unfold g W; dsimp only [Prod.fst_zero]; simp only [Work.G07.at_zero_increment,base_nil hh.funds]
  have hg' := Convex.norm_image_sub_le_of_norm_fderiv_le hz he (convex_closedBall _ _) (Metric.mem_closedBall_self hr.le) hh'
  simp only [hg0,sub_zero] at hg'
  let F' := (G.adjoint (d (focus S p))⁻¹).toContinuousLinearMap
  have hg := (Brush.even hY ha (hx'.trans hR) hZ (hg'.trans (mul_le_mul_of_nonneg_left hY.bound hZ))).report F' (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by
     rw [one_mul]; exact (G.norm_adjoint _ _).le)); rw [one_mul] at hg
  apply hg.shimmy
  filter_upwards [hA] with i hi
  have hv : W (gauge d (U i))=g (V' i) := by unfold W g W freely baseStroke; dsimp only [V']; rw [entry_stencil hp _ _ _ _ k p (replica_near hi) hi, shoreVisa hp p hi]
  change W _=G.adjoint _ (g (V' i)); rw [← hv]; unfold W
  rw [peony d hh.funds,← G.adjoint_mul, inv_mul_cancel, G.adjoint_one]
end YM.ConnectedActivityE6.Blaze.Gate
