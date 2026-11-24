import YM.RGComparison01.Marks.Rate
/-!
# Angular costs via Eider compact joint estimates

 Upgrade Pommel, Eskim, Aria of E6 to polynomial witnesses
 required in the marked real payment. Invocation tools unchanged down to
 projections in that payment. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Eider

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge} {d A : ℝ} (p : Canary G d A) (χ : Chi)
include p
lemma sharper (j : ℕ) (L : Side) {V : ℝ→ℝ} (h : RGComparison01.Fine G L V) : ∃ S Z : ℝ→ℝ, RGComparison01.Fine G L S ∧ RGComparison01.Geo G L Z ∧
    ∀ᶠ s in atTop, ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (M:E→G.Mat) (x:E), M x=1 → Brush j (royalty G) (V s) M x →
    ∀ y:G.Color, Brush j (S s) 1 (fun i=> plume G χ d (M i) y) x ∧ Brush j 1 (Z s) (fun i=> palm G χ d (M i) y) x := by
  obtain ⟨u,z,hU,hZ,hp⟩:= thorax p χ j; let D s:=(1+royalty G)*V s
  let B:=1+(j.factorial:ℝ)*z
  have hb : 1≤ B := le_add_of_nonneg_right (by positivity)
  refine ⟨fun s=>(j.factorial:ℝ)*u*D s,fun s=> B*D s,RGComparison01.Fine.grind_left (Geo.fixed _) (RGComparison01.Fine.grind_left (Geo.fixed _) h), (RGComparison01.Fine.grind_left (Geo.fixed _) (RGComparison01.Fine.grind_left (Geo.fixed _) h)).slow,?_⟩
  filter_upwards [(h.dividend.mul_left (1+royalty G)).below (by norm_num) 1 zero_lt_one] with s hS E _ _ M x hm hM y
  obtain ⟨hv,hh⟩:=hp y; rw [← hm] at hv hh
  have hp : 0≤ D s := by unfold D; have he:= royalty_ge G; have := hM.pos; positivity
  constructor
  · have hf := hM.pine hv
    refine Brush.offer.mpr ⟨hf.smooth,fun i hi=>?_⟩
    match i with
    | 0 => unfold normJ; rw [norm_iteratedFDeriv_zero,hm,nothing p χ,norm_zero]; positivity
    | i+1 =>
      apply (hf.order _ hi).trans; exact mul_le_mul_of_nonneg_left ((pow_le_pow_of_le_one hp ((le_abs_self _).trans hS) (by omega : 1 ≤ i+1)).trans_eq (pow_one _)) (by positivity)
  have hx:= hM.pine hh
  refine ⟨hx.smooth,mul_nonneg (zero_le_one.trans hb) hp,fun i hi=>?_⟩; match i with
  | 0=> unfold normJ; rw [norm_iteratedFDeriv_zero,hm, leaves p,norm_one,pow_zero,mul_one]
  | i+1=> apply (hx.order _ hi).trans; rw [one_mul,mul_pow B]; exact mul_le_mul_of_nonneg_right
            ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ (n:=i+1) hb (by omega))) (pow_nonneg hp _)
end YM.ConnectedActivityE6.Blaze.Eider
namespace YM.ConnectedActivityE6.Blaze.Silica

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge} {d A : ℝ} (p : Canary G d A)
include p
lemma franks (P : Teller G) (L : Side) (j : ℕ) (χ : Chi) {V : ℝ→ℝ} (h : RGComparison01.Fine G L V) :
    ∃ B D, RGComparison01.Fine G L B ∧ RGComparison01.Geo G L D ∧ ∀ᶠ x in atTop,
      ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio) (X : Coat T F), X.x=x → Works P L x S T → X.χ=χ → ∀ β>0,
      ∀ z : Air f G, ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ Config G c) (y:E), U y=X.V → Mode U y j (V x) →
        let u:=worldZ X β z
        (∀ i,Brush j 1 (D x) (fun v=>steerJ X d u (U v) i) y) ∧ (∀ a : ℝ, 0<a*X.t → 8*a*X.t ≤ d/2 →
          Clutch X z a β (|B x|) y j U (fun v=> steer X d u (U v)) (fun v=>course X d β z (U v))) := by
  obtain ⟨A,b,H,hb,hX⟩:= sharper p χ j L h
  refine ⟨A,b,H,hb,hX.mono ?_⟩
  intro x h c f S T F X hk hr hχ β hβ z E _ _ U y ht hv u
  subst χ
  have hp (i:Bond f) := h E (fun v=>G.mat (action X (U v) i)) y (by rw [ht]; simp [action]) (chargeMode X (V x) hv i) (u i)
  refine ⟨fun i=> (hp i).2,fun a ha hF=> ⟨ht,hβ,?_,ha,fun v=> proceeds _ _ hβ _ _,abs_nonneg _,?_,?_⟩⟩
  · rw [ht,home X p z hβ]
  · intro i; unfold steer fleece; change Brush _ _ _ (fun v=> u i+_ -u i) _; simp_rw [add_sub_cancel_left]; exact
      (hp i).1.climb (le_abs_self _) le_rfl
  filter_upwards [nearby X p ht hv] with y hh; exact conquered X p (U y) u hh ha hF

end YM.ConnectedActivityE6.Blaze.Silica
namespace YM.ConnectedActivityE6.Blaze.Silica.Clutch

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
lemma enamel (G : Gauge) (L : Side) (χ : Chi) {V : ℝ→ℝ} (h : RGComparison01.Fine G L V) (j : ℕ) (b : ℝ) :
    ∃ X : ℝ→ℝ, RGComparison01.Geo G L X ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S : StepData c f) (T : Tube G S) (F : Forest S.ratio)
    (Q : Coat T F), Q.x=x → S.patch.L=L → Q.χ=χ → 0<b*Q.t → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Air f G) (a β : ℝ) (y:E) (U : E → Config G c) (f':E → Directions G f) (W:E → Air f G),
    Clutch Q z a β (V x) y j U f' W → ∀ i, Brush j 1 (|X x|) (fun y=> Q.cone b (f' y) i) y := by
  obtain ⟨w,hp,hX⟩ := Brush.compact (k:=j) (f:=χ.read) (s:=Set.Icc 0 4) isCompact_Icc (fun _ _=>
    (χ.smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)))
  let t:= (Pressure.fiery G · L); let K x:= (b*t x)⁻¹*(V x +2*b*t x)
  have hk: RGComparison01.Geo G L K:= RGComparison01.Fine.inversed b (h.plus (RGComparison01.Fine.grind_left (Geo.fixed _) RGComparison01.Fine.flame))
  refine ⟨fun x=>(1+(j.factorial:ℝ)*w)*((1+K x*K x)*(1+1)),(Geo.fixed _).times (((Geo.fixed 1).joins (hk.times hk)).times (Geo.fixed _)),?_⟩
  refine Eventually.of_forall fun x c f S T F Q hQ he hχ hw E _ _ z a β y U f' W H i=> ?_
  by_cases hp:(fun y=> Q.cone b (f' y) i)=ᶠ[𝓝 y] fun _=>0
  · exact Brush.zi hp zero_le_one (abs_nonneg _)
  obtain ⟨hd,hA⟩:= H.fostered i hw hp
  unfold cone; rw [hχ]
  apply (plateauChi χ hA hX hw (by rw [← mul_assoc]; exact hd)).climb le_rfl
  change _ ≤ |(1+j.factorial*w)*((1+K x*K x)*(1+1))|
  simp_rw [Coat.t,hQ,he]; exact le_abs_self _


lemma coronet (G : Gauge) (L : Side) (χ : Chi) (j : ℕ) {V : ℝ→ℝ} (h : RGComparison01.Fine G L V) (b : ℝ) :
    ∃ B, RGComparison01.Geo G L B ∧ (∀ x,0≤B x) ∧ ∀ᶠ x in atTop, ∀ (c f:Side) (S:StepData c f) (T: Tube G S) (F : Forest S.ratio)
      (X : Coat T F), X.x=x → X.χ=χ → S.patch.L=L → 0 < b*X.t → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (z : Air f G) (a β : ℝ) (y:E) (U : E→ Config G c) (f':E → Directions G f) (w:E → Air f G), Clutch X z a β (V x) y j U f' w →
        ∀ Y (M:Support c),Y⊆ M → Brush j 1 (B x*coverNumber X.B M) (fun y=> X.enforce b (f' y) (X.plaza Y)) y := by
  obtain ⟨C,hC,hp⟩:= enamel G L χ h j b
  let B x:= (ballCost (radiusB x):ℝ)*ballCost 1*Itinerary.density L*|C x|
  refine ⟨B,(((Geo.balling Geo.radii).times (Geo.fixed _)).times (Geo.fixed _)).times hC.mean,
    fun x=> by unfold B; positivity,hp.mono ?_⟩
  intro x hx c f S T F X he hχ hL ht E _ _ z a β y U f' w H Y M hm; apply (Blaze.canopy (a:=b) (X:=X) f' M (|C x|) (M:=X.plaza Y)
    (fun i _=> hx _ _ S T F X he hL hχ ht E z a β y U f' w H i) (worn X hm) (abs_nonneg _)).climb le_rfl
  apply le_of_eq; unfold B; rw [← he,hL]; change _= (ballCost X.B:ℝ)* _ * _ * _ * _
  ring

end YM.ConnectedActivityE6.Blaze.Silica.Clutch
