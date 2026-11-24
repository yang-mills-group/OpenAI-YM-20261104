import YM.RGComparison01.Marks.Enamel
/-!
# Signal costs in threshold units

 Upgrade Hallmark/Cincture of E6 to polynomial witnesses
 required in the marked real payment. Invocation tools unchanged down to
 projections in that payment. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
attribute [local instance] Gauge.frobInner
lemma drawn (G : Gauge) (L : Side) (χ : Chi) {K : ℝ} (γ : ℝ) (j : ℕ) {v : ℝ→ℝ}
    (h : RGComparison01.Fine G L v) : ∃ B : ℝ→ℝ, RGComparison01.Fine G L B ∧ ∀ᶠ x in atTop,
    ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ G.El) (z:E), Brush j (royalty G) (v x) (G.mat ∘ U) z →
      let Z:=K*Pressure.fiery G x L
      Reliable G Z γ → Brush j (|B x|) 1 (fun i=>cutLog χ Z (U i)) z := by
  obtain ⟨J,d,he⟩:= cleanly G j 1 zero_lt_one
  have hu : ContDiff ℝ (↑j) χ.read := χ.smooth.of_le (show (↑(↑j:ℕ∞):WithTop ℕ∞)≤(↑(⊤:ℕ∞)) from WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C,hC,hΘ⟩ := Brush.compact (s:=Set.Icc 0 4) isCompact_Icc (fun _ _=> hu.contDiffAt)
  let m:= royalty G; let f x:= K*Pressure.fiery G x L; let D x:= (1+m)*v x
  let H x:= γ*(2*f x)+(j.factorial*J)*D x; let Y x:= (m*f x)⁻¹*((2*f x)*m+(m+m)*v x); let B x:=
    (j.factorial*C * H x)*(1+((1+Y x*Y x)*(1+1)+1))^j
  have hp : 0 < m := zero_lt_one.trans_le (royalty_ge _)
  have hf : RGComparison01.Fine G L f := RGComparison01.Fine.grind_left (Geo.fixed _) RGComparison01.Fine.flame
  have hd:= RGComparison01.Fine.grind_left (Geo.fixed (1+m)) h
  refine ⟨B,?_,?_⟩
  · have hr:Fine G L H:= (Fine.grind_left (Geo.fixed _) (Fine.grind_left (Geo.fixed _) hf)).plus (Fine.grind_left (Geo.fixed _) hd)
    have hx := Fine.inversed (m*K) (Fine.plus (Fine.grind_right (Fine.grind_left (Geo.fixed (2:ℝ)) hf) (Geo.fixed m)) (Fine.grind_left (Geo.fixed (m+m)) h))
    have hY: Geo G L Y:= by apply hx.compact; filter_upwards with x; unfold Y f; rw [mul_assoc m K]
    let u:=Geo.fixed (G:=G) (L:=L) (1:ℝ)
    exact (Fine.grind_left (Geo.fixed (j.factorial*C:ℝ)) hr).grind_right ((u.joins ((((u.joins (hY.times hY)).times (Geo.fixed (1+1))).joins u))).power j)
  filter_upwards [((hf.dividend.mul_left 2).mul_right m).below (by norm_num) _ he.pos,
    h.dividend.below (by norm_num) 1 zero_lt_one, hd.dividend.below (by norm_num) 1 zero_lt_one] with x hX hx ht E _ _ U z h Z hr
  have hp' : 0 < Z := hr.down
  have h₂ : v x ≤ 1 := (le_abs_self _).trans hx
  by_cases hi : G.chord (U z) ≤ 2*Z
  · let V i:= χ.innerShare Z (G.chord (U i))
    let P i := G.plog (G.mat (U i)); let c':= (j.factorial:ℝ)*C
    have hh : ‖G.mat (U z)-1‖ ≤ (2*f x)*m := (div_le_iff₀ hp).1 hi
    have hV : Brush j c' ((1+Y x*Y x)*(1+1)) V z := by
      let D (i:E) := (m*Z)⁻¹ • (G.mat (U i)-1); let f (x:E) := ‖D x‖^2
      have hp'' (i : E) : ‖D i‖ = G.chord (U i)/Z := by unfold D Gauge.chord; rw [norm_smul, Real.norm_of_nonneg (by positivity)]; unfold m royalty; ring
      have heq (i:E) : V i=χ.read (f i) := by unfold V f Chi.innerShare; rw [hp'']
      have hw : ‖D z‖≤ 2 := by rw [hp'',div_le_iff₀ hp']; exact hi
      rw [show V=(fun i=>χ.read (f i)) from funext heq]
      have hz : Brush j (Y x) 1 D z := by
        have ha:= (shrinker (h.separating (a_oneB G 1 h.pos)) hh h₂).smul ((m*Z)⁻¹); simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (m*Z)⁻¹)] using! ha
      have hh : f z ∈ Set.Icc 0 4 := ⟨sq_nonneg _,by unfold f; nlinarith [norm_nonneg (D z)]⟩
      exact (squared hz).pine (hΘ _ hh)
    have hX' : Brush j (H x) 1 P z := shrinker (h.pine (he.sound _ (hh.trans ((le_abs_self _).trans hX))))
      ((hr.cap _ hi).trans (mul_le_mul_of_nonneg_left hi hr.price.le)) ((le_abs_self _).trans ht)
    exact ((snaps hV hX').trim).climb (le_abs_self _) le_rfl
  apply Brush.shimmy (g:=fun y=> cutLog χ Z (U y)) (f:=fun _ : E=> (0:G.Color))
    ((Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl)
  have hz : ContinuousAt (fun y=> G.chord (U y)) z := ((h.smooth.continuousAt.sub_const _).norm.div_const _)
  filter_upwards [hz (lt_mem_nhds (lt_of_not_ge hi))] with y hy
  have hu : χ.innerShare Z (G.chord (U y))=0 := by
    by_contra hp; exact (χ.chosen_lt _ _ hr.down hp).not_ge (show _<_ from hy).le
  rw [cutLog,hu,zero_smul]
end YM.ConnectedActivityE6.Blaze
namespace YM.ConnectedActivityE6.Blaze.Vine

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
lemma signal (G : Gauge) (L : Side) (W γ K : ℝ) (j : ℕ) (χ : Chi) {v : ℝ→ℝ} (h : RGComparison01.Fine G L v) :
    ∃ C, RGComparison01.Fine G L C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → ShellAccess S G x W K γ →
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Forest S.ratio) (X : Coat T F) (U:E → Config G c) (y : E),
      X.χ=χ → X.x=x → X.width=K → Mode U y j (v x) → ∀ i : Bond f, Brush j (|C x|) 1 (fun z=> (vary X (U z)).saved i) y := by
  obtain ⟨C,hC,hp⟩:= drawn G L χ (K:=K) γ j h
  refine ⟨C,hC,hp.mono ?_⟩
  intro x hx c f S T hS hL E _ _ F X U y hX ht hw hY i
  let Z := K*Pressure.fiery G x L
  have hv : ((vary X (U y)).t)=Pressure.fiery G x L := by change X.t= _; unfold Coat.t; rw [ht,hS]
  have hk : Reliable G Z γ := by unfold Z; rw [← hS]; exact hL.log
  by_cases he:i ∈ F.trunks ∨ X.Hot i
  · rw [show (fun z=> (vary X (U z)).saved i)=(fun z:E=> (0:G.Color)) from funext fun z=> (if_pos he)]
    exact (Brush.certified zero_le_one _).climb (by rw [norm_zero]; exact abs_nonneg _) le_rfl
  let V z := F.drape X.Y i*(replica S.ratio (U z) i)⁻¹
  have hb: Brush j (royalty G) (v x) (G.mat ∘ V) y := by
    have hh := offsetB (Blaze.reverse (f:=fun t=> replica S.ratio (U t) i) (Blaze.recopy S hY.atLink i)) (F.drape X.Y i) 1
    simpa only [mul_one] using! hh
  have heq i' : (vary X (U i')).saved i=cutLog χ Z (V i') := by
    unfold Coat.saved; rw [if_neg (show ¬(i∈F.trunks ∨ (vary X (U i')).Hot i) from he)]; change cutLog X.χ (X.width*X.t) _=_
    rw [hX, hw, show X.t=_ from hv]; rfl
  simp_rw [heq]; exact hx _ V _ hb hk
end YM.ConnectedActivityE6.Blaze.Vine
