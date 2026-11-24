import YM.RGComparison01.Marks.Rate
/-!
# Polynomial costs on short flat frozen array

 Upgrade SmallLog, Rasura of E6 to polynomial witnesses
 required in the marked real payment. Invocation tools unchanged down to
 projections in that payment. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge}
lemma patch_flat (P : Teller G) (L : Side) : ∃ H : ℝ → ℝ, RGComparison01.Fine G L H ∧
    ∀ᶠ x : ℝ in atTop, 0 ≤ H x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S), S.patch.L=L → Room P S T x →
    ∀ V : Config G c, ∀ (o : Site c) (d : ℕ), d ≤ 32 * radiusB x → Clean V x o (d+1) →
    ∃ (z : Site c → G.El) (b : LogField G c), AgreeNear id o d (gauge z V) (represent b) ∧ ‖b‖ ≤ H x := by
  obtain ⟨C,r,hC,hr,hk⟩ := extend_interior G
  let F x := 32*radiusB x+1
  let u x := 16*(2*(F x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  have hh : Geo G L fun x=> (F x:ℝ):= by unfold F; push_cast; exact ((Geo.fixed _).times Geo.radii).joins (Geo.fixed _)
  have he : RGComparison01.Fine G L u := RGComparison01.Fine.grind_left (((Geo.fixed 16).times ((((Geo.fixed 2).times hh).joins (Geo.fixed 1)).power 5)).times (Geo.fixed _)) (RGComparison01.Fine.grind_left (Geo.fixed (2:ℝ)) RGComparison01.Fine.flame)
  refine ⟨fun x=>C*u x, RGComparison01.Fine.grind_left (Geo.fixed C) he, ?_⟩
  filter_upwards [he.dividend.below (by norm_num) _ hr, Delay.shift_pos G L] with x hx hy
  have h0 : 0 ≤ u x := by have hs : 0 < Pressure.fiery G x L := Work.E09.temp_pos hy; unfold u; positivity
  refine ⟨mul_nonneg hC.le h0,?_⟩
  intro c f S T hL hR V o d hd h
  have hv : 0 ≤ Pressure.temp x := by unfold Pressure.temp; positivity
  obtain ⟨z,hz⟩ := Work.E08.axial_patch o V d (d+1) le_rfl (by have hh := hR.buys; omega) _ hv
    (fun i hi j => h.toll (b := (i,j)) hi)
  have hb : ∀ i : Bond c, separation o i.1 ≤ d → G.chord (gauge z V i)≤u x := by
    intro i hi; apply (hz i hi).trans
    unfold u; gcongr
    · unfold F; omega
    · simpa only [hL] using! hR.temperatures
  obtain ⟨b,hy,hx⟩ := hk id o d (gauge z V) _ h0 ((le_abs_self _).trans hx) hb
  exact ⟨z,b,hx,hy⟩
end YM.ConnectedActivityE6.SliceRows
namespace YM.ConnectedActivityE6.Blaze.Frond

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open PhysicalNext PhysicalNext.Repeat Packets Art Silica Poll Pond Shield Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

open YM.RGComparison01
variable {G : Gauge}
lemma dayStar (P : Teller G) (L : Side) (j : ℕ) {V : ℝ→ℝ} (h : RGComparison01.Fine G L V) (hv : ∀ᶠ x in atTop,0≤V x) :
    ∃ Q : ℝ→ℝ, RGComparison01.Fine G L Q ∧ ∀ᶠ s in atTop, 0≤Q s ∧
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), Works P L s S T →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : E → Config G c) (x:E) (p : ℕ) (o : Site c),
    Mode U x j (V s) → p ≤ 32*radiusB s→ Clean (U x) s o (p+1) →
      ∃ (z : Site c→ G.El) (L : E→ Directions G c), Brush j (Q s) 1 L x ∧
        ∀ᶠ i in 𝓝 x, AgreeNear id o p (gauge z (U i)) (increment 1 (L i)) := by
  obtain ⟨C,hC,hP⟩:= patch_flat P L
  obtain ⟨J,d,hJ⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨e,he,hy⟩ := Metric.nhds_basis_closedBall.mem_iff.mp G.plog_left
  obtain ⟨f,r,hf,hr,h⟩:= chord_chart_cost G
  let D x:= (1+royalty G)*V x
  let K : ℝ := j.factorial*J
  have hx := hJ.value; have hk : 0≤K := by unfold K; positivity
  have hD : RGComparison01.Fine G L D := RGComparison01.Fine.grind_left (Geo.fixed _) ‹Fine G L V›
  refine ⟨fun x=> C x+K* D x,hC.plus (RGComparison01.Fine.grind_left (Geo.fixed _) hD),?_⟩
  filter_upwards [hP,hv,hD.dividend.below (by norm_num) 1 zero_lt_one,hC.dividend.below (by norm_num) (min r e) (lt_min hr he),
    ((hC.dividend.mul_left f).mul_right (royalty G)).below (by norm_num) d hJ.pos, room G P L] with x hp hv hz he hx hr
  have ht : 0≤ D x := by unfold D; have hh:=royalty_ge G; positivity
  have ht' := add_nonneg hp.1 (mul_nonneg hk ht)
  refine ⟨ht',?_⟩
  intro c f' S T hS E _ _ U X p o hU hf' hw
  obtain ⟨z,b,hb,hB⟩:= hp.2 _ _ S T hS.length_eq (hr _ _ S T hS) (U X) o p hf' hw
  let g x:= gauge z (U x); let L' (x:E) (j : Bond c) := if separation o j.1 ≤ p then G.plog (G.mat (g x j)) else 0
  obtain ⟨hR,hE⟩ := le_min_iff.mp ((le_abs_self _).trans he)
  have he (i : Bond c) (hi : separation o i.1 ≤ p) : ‖L' X i‖ ≤ C x ∧ ‖G.mat (g X i)-1‖ ≤ d := by
    let y := b (pole i); have hb' : ‖y‖ ≤ C x := (norm_le_pi_norm _ _).trans hB
    have hg : g X i=G.lieExp y := by rw [show g X i=_ from hb i hi]; unfold represent increment; rw [Pi.one_apply,mul_one]; rfl
    refine ⟨?_,?_⟩
    · unfold L'; rw [if_pos hi,hg,show G.plog (G.mat (G.lieExp y))=y from hy (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hb'.trans hE))]; exact hb'
    have he := (h y (hb'.trans hR)).trans (mul_le_mul_of_nonneg_left hb' hf.le)
    rw [hg]; change _ / royalty G≤ _ at he
    apply le_trans ((div_le_iff₀ (lt_of_lt_of_le zero_lt_one (royalty_ge G))).mp he); exact (le_abs_self _).trans hx
  have hh := soak hU z
  have hy i : Brush j (C x+K*D x) 1 (fun y=> L' y i) X := by
    unfold L'; split_ifs
    next ht =>
      have hu : Brush j K (D x) (fun y=> G.plog (G.mat (g y i))) X := (hh.atLink i).pine (hJ.sound _ (he i ht).2)
      apply Brush.offer.mpr; refine ⟨hu.smooth,fun k hi=>?_⟩
      rcases k with _|k
      · unfold normJ; rw [norm_iteratedFDeriv_zero]; have hq:= (he i ht).1; unfold L' at hq; rw [if_pos ht] at hq
        exact hq.trans (le_add_of_nonneg_right (mul_nonneg hk ‹0 ≤ D x›))
      apply (hu.order _ hi).trans
      exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one ‹0≤ D x› ((le_abs_self _).trans hz)
        (by omega : 1 ≤ k+1)) hk).trans (by rw [pow_one]; exact le_add_of_nonneg_left hp.1)
    exact (certified (show (0:ℝ)≤1 by norm_num) (0:G.Color)).climb (by rw [norm_zero]; exact ht') le_rfl
  have hv i (hi : i∈univ.filter fun j : Bond c=> separation o j.1 ≤ p) : ∀ᶠ y in 𝓝 X,g y i=increment 1 (L' y) i := by
    have hi := (mem_filter.mp hi).2
    have hz : ‖G.mat (g X i)-1‖ < 2*d := lt_of_le_of_lt (he i hi).2 (by have h:=hJ.pos; linarith)
    have he : ContinuousAt (fun y : E=> ‖G.mat (g y i)-1‖) X := ((hh.atLink i).smooth.continuousAt.sub_const (1:G.Mat)).norm
    filter_upwards [he (gt_mem_nhds hz)] with y hy; unfold increment L'; rw [if_pos hi,hJ.inverse _ hy,Pi.one_apply,mul_one]
  refine ⟨z,L',Brush.fold zero_le_one ht' hy,?_⟩
  filter_upwards [(Finset.eventually_all _).2 hv] with y hz i hi; exact hz i (mem_filter.mpr ⟨mem_univ _, hi⟩)

end YM.ConnectedActivityE6.Blaze.Frond
