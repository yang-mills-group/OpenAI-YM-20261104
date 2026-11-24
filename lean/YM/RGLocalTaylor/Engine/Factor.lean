import YM.RGLocalTaylor.Engine.Awning

/-!
# Factor licensing with cumulative warning events

Individual Factors compose into product price preserving the joint
`catastrophe` event. Don't factor that event's probability. Include
non-HEAD-power and repeated analytic estimates before this composition
and carry the costs in Sales.
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


def stampFactor (_H : Cash W s μ L Q o C T R) (i : Head S) (V : ℝ) :=
  V * spanW T R (radiusB s) Q.halo i

lemma stamp_nonneg {i : Head S} (ha:0≤A) : 0 ≤ stampFactor H i A := by
  unfold stampFactor
  apply mul_nonneg ha
  rcases i with i|i
  · exact zero_le_one
  change (0:ℝ)≤1+(↑(coverNumber _ _) + ↑(_ : ℕ))
  positivity

lemma crash_summed (p : Molecule S) (z : Air f G) (A β : ℝ) :
    z∈ X.catastrophe A β (blaze p) ↔ ∀ i∈p,z∈ X.catastrophe A β (blaze ({i}:Molecule S)) := by
  have hh i (q:Molecule S) : i∈blaze q ↔ Sum.inr (Sum.inr (Sum.inr i))∈q:=by simp [blaze]
  change (∀ i∈ _,_) ↔ ∀ i∈p, ∀ j∈ _, _
  simp_rw [hh]; refine ⟨fun h i hi j hj=>h j ((mem_singleton.mp hj).symm ▸ hi),fun h i hi=> h _ hi i (mem_singleton_self _)⟩

/-- Pointwise factor orientation BEFORE grouping estimates at a V-Brush
(pass ζ-analytic factor/weighted moments here). -/
def EstFactor (_Ξ : Utopia H j v d r C' χ) (i : Head S) (f' : Insert T) (A weight speed : ℝ) : Prop :=
  ∀ (F : Forest S.ratio) (X : Coat T F) (z : Air f G), X.x=s → X.width=o.K → X.χ=χ → X.manifest →
    Healthy (Pressure.temp s) (H.supportP i) X.V → ∀ (E : Type)
    [_hE : NormedAddCommGroup E] [_hER : NormedSpace ℝ E] [_fE : FiniteDimensional ℝ E]
      (U : E → Config G c) (y : E), Mode U y j v → U y=X.V →
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze ({i}:Molecule S))).indicator (fun _ => weight) z)
      (stampFactor H i speed) (fun i=> f'.value (vary X (U i)) (course X A R.beta z (U i))) y

namespace EstFactor
variable {Ξ : Utopia H j v d r C' χ} {i : Head S} {f' : Insert T} {weight speed : ℝ}

lemma weaken (h : EstFactor Ξ i f' A weight speed) {weight' speed' : ℝ} (hp : weight ≤ weight')
    (hv : speed ≤ speed') : EstFactor Ξ i f' A weight' speed' := by
  intro F X z hX hK hχ hM hh E _ _ _ U x hy hU
  apply (h F X z hX hK hχ hM hh E U x hy hU).climb
  · by_cases he : z ∈ X.catastrophe (o.ξ/2) R.beta (blaze ({i} : Molecule S))
    · simpa only [Set.indicator_of_mem he]
    rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he]
  exact mul_le_mul_of_nonneg_right hv (show 0≤ spanW .. from by simpa only [stampFactor,one_mul] using stamp_nonneg (H:=H) (i:=i) zero_le_one)

lemma product {p : Molecule S} {f' : Head S → Insert T} {w' : Head S → ℝ} (hv:0≤speed)
    (ht : troupe T R Q.halo (radiusB s) p) (hp : ∀ i∈p, EstFactor Ξ i (f' i) A (w' i) speed) :
    CoveredAt Ξ (Insert.joined p f') p A (∏ i∈p, w' i) speed := by
  intro F X z hX hK hχ hM hh E _ _ _ U x hy hU
  let f i y := (f' i).value (vary X (U y)) (course X A R.beta z (U y)); let w i:= stampFactor H i speed
  let k (p:Molecule S) := X.catastrophe (o.ξ/2) R.beta (blaze p)
  let a i:= (k {i}).indicator (fun _=> w' i) z
  have h : ∑ i∈p,w i ≤ speed*(2*H.shapeW p):=by
    unfold w stampFactor; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (Utopia.worthy p ht) hv
  have hg i (hi:i∈p): Brush j (a i) (w i) (f i) x := hp i hi F X z hX hK hχ hM
    (Finset.disjoint_of_subset_left (subset_biUnion_of_mem H.supportP hi) hh) E U x hy hU
  apply (Brush.all_prod p f _ _ hg).climb _ h
  by_cases he:z∈ k p
  · rw [Set.indicator_of_mem he]; apply Finset.prod_le_prod (fun i hi=> (hg i hi).nonneg) (fun i hi=> ?_); rw [show a i=w' i from Set.indicator_of_mem ((crash_summed ..).1 he i hi) _]
  rw [Set.indicator_of_notMem he]; unfold k at he; rw [crash_summed] at he; push Not at he
  obtain ⟨i,hi,hv⟩:= he; rw [prod_eq_zero hi (show a i=0 from Set.indicator_of_notMem hv _)]

end EstFactor

namespace Awning
variable {Ξ : Utopia H j v d r C' χ}
    {e uJ vJ discount : ℝ} (h : Awning H Ξ A b discount e uJ vJ k l)
include h

lemma estimates_leg (y₀ : Finset ℕ) (i : Head S) : EstFactor Ξ i (leg H y₀ i) A (Ξ.tag i) r := by
  intro F X z hX hK hχ hM hh E _ _ _ V x hy hv
  let f' t := steer X A (worldZ X R.beta z) (V t); let w' t:= course X A R.beta z (V t)
  let f i (t:E):= Polar.ember (vary X (V t)) o.a R W Q.table (f' t) (X.input (worldZ X R.beta z)) (w' t) y₀ Q.halo i
  have hr : Clutch X z o.a R.beta d x j V f' w' := (h.course_prices F X z hX hK hχ hM E V x hy hv).1
  have hU i : (fun t=> (leg H y₀ i).value (vary X (V t)) (w' t))=ᶠ[𝓝 x] f i := by
    filter_upwards [hr.patch] with t ht
    have hh := (plastic ht hr.pulse).reeled
      (show Room P S T _ from hX.symm ▸ H.laws.data.room) W Q.table y₀ Q.halo
      (show Intake P T _ _ from hX.symm ▸ H.laws.intake) i (w' t)
    change ember (vary X (V t)) .. = _
    rw [hr.moving t]; exact hh
  apply Brush.shimmy _ (hU i)
  by_cases he : z∈ X.catastrophe (o.ξ/2) R.beta (blaze ({i}:Molecule S))
  · rw [Set.indicator_of_mem he]
    have hx := Ξ.stream E F X V f' w' x z hX hK hχ hM hy hr y₀ i (hX.symm ▸ hh)
    rw [show X.B=radiusB s from congr_arg _ hX] at hx; exact hx
  rw [Set.indicator_of_notMem he]
  unfold catastrophe Poll.Crash at he; change ¬ (∀ i∈_,∃ j,_≤_ ∧ _ ≤ _) at he; push Not at he
  obtain ⟨w,hw,hv⟩:= he
  rw [blaze,mem_toRight,mem_toRight,mem_toRight,mem_singleton] at hw
  apply Brush.zi _ le_rfl (stamp_nonneg (zero_le_one.trans Ξ.active))
  rw [← hw]; exact hr.sleek (show Cash W X.x μ L Q o C T R from hX.symm ▸ H) hy Ξ.clock hM hK w (fun i hi=> (hv i hi).le) y₀
end Awning
end YM.RGLocalTaylor
