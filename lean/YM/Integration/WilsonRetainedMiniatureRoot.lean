import YM.Integration.WilsonRetainedMiniatureTaylor

/-! The summed rooted price of the actual short interaction errors, on the same marked Cash. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonRetainedMiniatureRoot

open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Canvas LocalTaylorR2.Port RGLocalTaylor
open WilsonRetainedMiniatureTaylor
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {W : ℝ} (P : Teller G) (Q : ConnectedActivityE6.Target G P)
  (o : Target.Order G W) (L : Side) (D : Patch) (hD : D.Branches P.bind G)

include hD in
theorem original (χ : Chi) (p j : ℕ) (η : ℝ) (hη : 0<η) (v d : ℝ → ℝ)
    (hv : Rate G L (-(1/2)) v) (hd : Rate G L (-(1/2)) d) (hn : ∀ᶠ s in atTop, 0≤v s) :
    ∀ᶠ s in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R), S.patch=D →
      ∃ w : Miniature c f → ℝ,
      Sales (radiusB s) Q.relative Q.ε (sleeve S (radiusB s) Q.halo) w (fun _ => 0)
        (betaF G s L ^ (-((p:ℝ)+1-η)/2)) ∧
      (∀ k, Sees H j (v s) (d s) χ (Mesh.error (Pavilion.mosaics H p) H (letter k)) (w k) 1) ∧
      ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s → X.width=o.K → X.manifest → X.χ=χ →
        ∀ (z : Air f G) (k : Miniature c f),
        Healthy (Pressure.temp X.x) (sleeve S X.B Q.halo k) X.V →
        |Mayer.exponent H X z (identityLog (letter k))| ≤ H.w (letter k) ∧
        |Mayer.exponent H X z (identityLog (letter k)) - Pavilion.mosaics H p (letter k) F X z| ≤ w k := by
  let a : ℝ := -((p:ℝ)+1-η/2)/2
  obtain ⟨b,hb,hN,hPass⟩ := Pavilion.titular v d L o P Q p j 0 hv hd hn D hD χ
  let ticket s := b s + betaF G s L ^ a
  have hTicket : Rate G L a ticket := (hb.weaken (by dsimp [a]; linarith)).add Rate.power
  let m := Fintype.card Signed*Census.spots L+(Itinerary.density L+Itinerary.density L)
  let fee s := ((Animals.ballCost ((Q.halo+1)*radiusB s):ℝ)*m)*
    (ticket s*Real.exp (Q.relative*Animals.ballCost (Q.halo+1)))
  have width := Census.width_rate G L (Q.halo+1) 0
  have hFee : Rate G L a fee := by
    simpa only [Nat.add_zero,zero_add] using!
      (width.mul_right (m:ℝ)).mul (hTicket.mul_right (Real.exp (Q.relative*Animals.ballCost (Q.halo+1))))
  have point := purchased P Q o L D hD χ p (η/2) (half_pos hη)
  filter_upwards [hPass,point,hFee (-((p:ℝ)+1-η)/2) (by dsimp [a]; linarith),
      (Work.E09.betaF_growth G L).eventually_gt_atTop 0] with s hs hp priced hβ
  intro c f S T R μ C H patch
  have pos : 0≤betaF G s L ^ a := Real.rpow_nonneg hβ.le _
  have hr : 0<radiusB s := lt_of_lt_of_le (by norm_num) H.laws.data.room.sight.1
  have seen := hs c f S T R μ C H patch
  have census := ConnectedActivityE6.fixed (ε:=Q.ε) (C:=ticket s)
    (smallCensus S L H.laws.data.funds.length_eq) hr _ (packed S (l:=Q.halo) hr)
    (show 0≤Q.relative by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos])
    (add_nonneg (hN s) pos)
  refine ⟨fun _ => ticket s, census.raise ((le_abs_self (fee s)).trans priced), ?_, ?_⟩
  · intro k
    exact (seen.round k).climb H (le_add_of_nonneg_right pos) le_rfl
  · intro F X hx hw hm hχ z k healthy
    exact ⟨((H.quotes F X hx hw hm).2.1 (letter k) z).1,
      (hp c f S T R μ C H patch F X hx hw hm hχ z k healthy).trans (le_add_of_nonneg_left (hN s))⟩

end YM.Integration.WilsonRetainedMiniatureRoot
end
