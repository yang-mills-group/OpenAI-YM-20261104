import YM.Comparison.Density.Transport.Stencils
import YM.Comparison.Density.Mirrors.Masked
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Weld
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Clover
/-!
# Applying the ordinary jet bound to the complete reflected patches

The bound is in the actual left derivatives.
Choice of local axial gauge is POINTWISE and fixed for a germ computation:
no smooth dependence of gauge on fields required. The domain is closed-healthy
and we carry an actual smooth unmasked extension through boundary points. All
boxes are within the physical lifted periods indicated. After this bridge
no periodic-producer result on any auxiliary volume is needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Mirrors
open Function Lattice RG Wilson Filter WardBin.Lies AnalyticBridge.SectorAffine.Offset
open PhysicalNext.Repeat Transport
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} (B : BudgetPoint) (L : LinkTube G)

/-- Small-field geometry, independent of the field demand. Pinned
mask B.threshold. Room at least one extra layer for axial proof. -/
def axialCost (B : BudgetPoint) (d : ℕ) := 16*(2*(d:ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)*B.threshold
lemma axial_nonneg (d : ℕ) : 0≤ axialCost B d := by unfold axialCost; have hp:=B.threshold_pos; positivity

structure Room (B : BudgetPoint) (n : Side) (L : LinkTube G) (d : ℕ) (w : ℝ) : Prop where
  side : 2*d<n.val
  core : axialCost B d < L.radius
  logs : L.constant * axialCost B d ≤ w
  budget : B.threshold≤w
  small : w ≤ 1

lemma axial_to (o : Site n) (D d : ℕ) (U : Config G n) (hs : d < D) (hb : 2*D<n.val)
    (hU : Healthy B.threshold (neighborhood D o) U) :
    ∃ z : Site n → G.El, ∀ i : Edge (Site n), separation o i.1≤ d → G.chord (gauge z U i) ≤ axialCost B D := by
  refine Work.E08.axial_patch o U d D hs hb B.threshold B.threshold_pos.le ?_
  intro y hy A
  exact AnalyticBridge.CouplingShape.local_chord hU (y,A) ((neighborhood_iff ..).2 hy)

theorem inspection (U : Config G n) (k : Side) (o : Site n) {D : ℕ} {w : ℝ} (h : Room B n L D w) (hd : k.val<D)
    (hU : Healthy B.threshold (neighborhood D o) U) : ∃ z : Site (quad k) → G.El,
        let V:= gauge z (tiled k o U)
        (∀ i, G.chord (V i)<L.radius) ∧ ‖logField V‖ ≤ w := by
  obtain ⟨t,ht⟩:= axial_to B o D k.val U hd h.side hU
  let S:=track k
  let Q:=Slide.sites S o
  let V:= gauge (t ∘ Q) (tiled k o U)
  have he (i) : G.chord (V i) ≤ axialCost B D:= by
    unfold V; rw [tiled_track,← Slide.shape_gauge S o]
    unfold Slide.shape; split
    · exact ht _ (track_sites ..)
    split
    next _=> rw [G.chord_inv]; exact ht _ (track_sites ..)
    simpa using axial_nonneg B D
  have h' i := lt_of_le_of_lt (he i) h.core
  exact ⟨_,h',(pi_norm_le_iff_of_nonneg (B.threshold_pos.le.trans h.budget)).2 fun i=>
    (L.log_size _ (h' i)).trans ((mul_le_mul_of_nonneg_left (he i) L.scale.le).trans h.logs)⟩

-- regular requests
variable (f : Links ℤ G.El → ℝ) (r : Side)

lemma entry_gauge (fg : GaugeInvariant f) (o : Site n) : GaugeInvariant (f ∘ expandAt o) := by
  intro z U; rw [Function.comp_apply,Function.comp_apply,expandAt_gauge,fg]
lemma total_gauge (fg : GaugeInvariant f) : GaugeInvariant (total f n) :=
  fun z U=> Finset.sum_congr rfl fun x _=> entry_gauge f fg x z U
lemma germ_pull_gauge {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (z : Site n→G.El)
    (F : Config G n→E) (U : Config G n) {p : ℕ} (h : GaugeInvariant F)
    (he : WardBin.Lies.Germ p F (gauge z U)) : WardBin.Lies.Germ p F U := by
  unfold WardBin.Lies.Germ
  rw [show (fun y => F (increment U y))=(fun y=>F (gauge z (increment U y))) from funext (fun v=> (h z (increment U v)).symm)]
  apply he.curves (Z:=fun v=> gauge z (increment U v))
  · rw [Work.G07.at_zero_increment]
  intro i; unfold Lattice.gauge; simp only [G.mat_mul]
  have hv:= grins (U:=fun _:Directions G n=>U) (l:=p) (A:=id) (fun i=> contDiffAt_const) (x:=(0:Directions G n)) contDiffAt_id i
  exact ContDiffAt.mul (contDiffAt_const.mul hv) contDiffAt_const

lemma weight_regular (k : Side) (o : Site n) (D : ℕ) {w d : ℝ} {m : ℕ} (h : Room B n L D w) (hd : k.val<D) (hk : B.order ≤ m)
    (hP : Measurable f) (hL : LocalOn (Lattice.box r.val) f) (hF : GaugeInvariant f)
    (hf : ∀ y : Arms r G, ‖y‖ ≤ w → Through m (Transport.chart r f) y d) :
    B.Regular (neighborhood D o) (weightAt f k o) := by
  have hh (U) (hU : Healthy B.threshold (neighborhood D o) U) : Push.Local.Chart B.order (weightAt f k o) U := by
    obtain ⟨z,ht,hV⟩:= inspection B L U k o h hd hU
    have hv:= germ_smooth (total f _) L _ ht B.order (through_le (total_entry f (quad k) r hL hV hf) hk).smooth
    have hd : weightAt f k o = total f _ ∘ Slide.shape (track k) o:= by
      funext V; rw [Function.comp_apply, ← tiled_track]; rfl
    rw [hd]; refine Slide.cloth (B:=B) (track k) o _ ?_
    rw [← tiled_track]; exact germ_pull_gauge z _ (tiled k o U) (total_gauge f hF) hv
  exact ⟨fun U V h'=> weight_local f k o U V (agrees_mono h' (Finset.coe_subset.mpr (neighborhood_mono hd.le))),
    weight_borel f _ _ hP,weight_gauge f hF k o,hh,fun U hU A l hl=> Next.Foundations.left_has A hl (hh _ hU)⟩

def tileBudget (k : Side) (s : ℕ) (w d e : ℝ) := 2^B.order*((1+(k.val:ℝ))^(B.power*B.order))*(groupPrice L B.order*
    (s*((Fintype.card (Edge (Site (quad k))):ℝ)*e)+((Fintype.card (Site (quad k)):ℝ)*d)*w^s))

theorem weight_sup (k : Side) (o : Site n) (D : ℕ) {w d e : ℝ} {m s : ℕ} (hR : Room B n L D w) (hB : k.val<D)
    (hm : B.order ≤ m) (hs : s ≤ m) (hk : r.val<k.val)
    (hN : 4*r.val < n.val) (hd : 0≤d) (he : 0≤e) (hL : LocalOn (Lattice.box r.val) f) (hg : GaugeInvariant f)
    (h : Ordinary f n s e) (hf : ∀ y:Arms r G, ‖y‖≤w → Through m (Transport.chart r f) y d) :
    B.supBounds o (neighborhood D o) (weightAt f k o) (tileBudget B L k s w d e) := by
  let p:=quad k
  let F:=total f p
  let A:ℝ:= (Fintype.card (Site p):ℝ)*d
  let E:ℝ:= (Fintype.card (Edge (Site p)):ℝ)*e
  have ha:0≤A:=by unfold A; positivity
  have he':0≤E:=by unfold E; positivity
  let C:=groupPrice L B.order*(s*E + A*w^s)
  have hw:= B.threshold_pos.trans_le hR.budget
  have hC : 0≤ C:= by unfold C; have ht:= price_nonneg L B.order; positivity
  refine ⟨show 0≤ 2^B.order*((1+ (k.val:ℝ)) ^ (B.power*B.order))*C from by positivity,fun U hU l hl hD=>?_⟩
  obtain ⟨z,hz,hV⟩:= inspection B L U k o hR hB hU
  let V:=tiled k o U
  have hv:=germ_smooth F L (gauge z V) hz B.order (through_le (total_entry f p r hL hV hf) hm).smooth
  have hsX : Ordinary f p s e := local_transport f r p n (by change 4*r.val<4*k.val; omega) hN hL he
    (through_le (hf (0:Arms r G) (by rw [norm_zero]; exact hw.le)) hs).smooth h
  have ht i (hi:i<s): ‖iteratedFDeriv ℝ i (F ∘ increment 1) 0‖≤E := ordinary_norm f hsX he _ hi
  have hx (l : List (Directions G p)) (hl : l.length≤B.order) (ht : ∀ i∈l,‖i‖ ≤ B.threshold) :
      ‖leftDerivs F l V‖ ≤ C := by
    refine Slide.bills z (total_gauge f hg) (fun l' h1 h2=> ?_) _ hl ht
    exact transport F L w (gauge z V) hz hw hR.small hV m B.order s A E hs hm ha he' (fun Y h=> total_entry f p r hL h hf) (by assumption) _ h1 (fun i hi=> (h2 i hi).trans hR.budget)
  have hE : total f p ∘ tiled k o= weightAt f k o:= rfl
  rw [←hE,tiled_track]; apply Slide.stalled (track k) o F (track_sites k o) l U hl hD
  · rw [← tiled_track]; exact germ_pull_gauge z F V (total_gauge f hg) hv
  simpa only [V,tiled_track] using hx
end YM.Comparison.Density.Mirrors
