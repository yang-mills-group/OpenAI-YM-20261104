import YM.Integration.FVA1Physical.Sources.Round2.PortalFieldTaylor

/-! Uniform fixed-order bounds for the mixed physical insertion under the full
conditional portal on a measured RG season. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bakery MSbar.Bakery.Film
open MSbar.Cacao MSbar.Whisk Push.Uniform Next.SectorChange YM.Integration.FVA1Physical.Wilson
open MSbar.Mosaic MSbar.Kelvin
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

private theorem field_clock_price (p : Palisade) (V : Voice G) (n : ℕ) (C δ η : ℝ)
    (hδ : 0<δ) (hη : 0<η) (hηn : η<(n:ℝ)+1) :
    ∀ᶠ y:ℝ in atTop, ∀ g:ℝ, lensT y g → 3*shade G*rot p y≤δ ∧
      C*(3*shade G*rot p y)^(n+1)≤g^((n:ℝ)+1-η) := by
  have rise : Tendsto (fun y:ℝ=>y) atTop atTop:=tendsto_id
  let α:ℝ:=(n:ℝ)+1-η
  have hα : 0<α:=sub_pos.mpr hηn
  have rotator:=(Mosaic.height rise p V).2.2.2.1.mulK rise (3*shade G)
  have cash:=((rotator.raise rise (n+1)).mulK rise C).mulK rise ((2:ℝ)^α)
  have ok : -(1/2:ℝ)*((n+1:ℕ):ℝ) < -(1/2)*α:= by dsimp [α];push_cast;linarith
  filter_upwards [cash _ ok,(rotator.bouquet rise (by norm_num)).eventually (ge_mem_nhds hδ),
    eventually_gt_atTop (0:ℝ)] with y bound small hy
  intro g band
  have β : 0 < cue y:=inv_pos.mpr (Real.sqrt_pos.mpr hy)
  have hg : 0<g:=(half_pos β).trans_le band.1
  have scale : cue y=y^(-(1/2:ℝ)):=by rw [Real.rpow_neg hy.le,←Real.sqrt_eq_rpow];rfl
  have room : cue y ≤ 2*g:=by linarith only [band.1]
  refine ⟨small,?_⟩
  apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) α)).mp
  calc
    (2:ℝ)^α * (C*(3*shade G*rot p y)^(n+1)) ≤ y^(-(1/2:ℝ)*α) :=
      (le_abs_self _).trans bound
    _ = (cue y)^α := by rw [scale,Real.rpow_mul hy.le]
    _ ≤ (2*g)^α := Real.rpow_le_rpow β.le room hα.le
    _ = (2:ℝ)^α*g^α := Real.mul_rpow (by norm_num) hg.le

/-- In each admitted torus and at any scale buying this stage, integrating the
fixed mixed field's first n canonical Taylor rows under the unchanged interacting
conditional law costs at most g^(n+1−η). No tail or denominator hypothesis. -/
theorem purchased_field_taylor (V : Voice G) (clear : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' : RG.Stage) (P : Patch)
    (K : KernelChoices) (branch : P.Branches K G) (part : Bool) (n : ℕ)
    {D η : ℝ} (hD : 0≤D) (hη : 0<η) (hηn : η<(n:ℝ)+1) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x;let X:=boxX y b;let Y:=boxY y b;let idx:=includeX (G:=G) A.F X
      let O:=represent (tint G (Exterior.Body 1 A.c) z);let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      let HM:=mold A.pre A.F A.v;let area:=hotel A.F X Y V O ν (pillow y) (room y)
      ∀ (o : ι→Site A.f) (near : ∀ l : Slice J, 2*separation b (legs J o l).1≤ spotN y)
      (U : Config G A.f) (B : Positions (Primary A.f G)→ℝ),
      let m:=him V A.F Y O ν HM X (linCash A.F z) U ∘ idx
      let E:=interiorEnergy A.S O A.v (chambers A.F Y V O ν) A.pre.beta A.fClock B
      |schurOrbit A V χ y z b B (fun Z=>look part (tally J o Z)) U -
       tiltedTaylor J A.S A.F o X (wires_inside J A.S A.F o y b near) Y area χ m
       (pinch idx HM)⁻¹ A.fClock E U part n| ≤ A.fClock^((n:ℝ)+1-η) := by
  obtain ⟨δ,C,hδ,hC,fields⟩:=held_field_taylor J part n
  obtain ⟨p,buy⟩:=purchased_chart_chance V clear simple H H' P K branch hD 0
  obtain ⟨_,_,ready⟩:=waiting p H H' V χ hχ clear P 3 0
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [buy,ready,rise.eventually (field_clock_price p V n C δ η hδ hη hηn),
    rise.eventually_gt_atTop 0] with x offered seats charged high
  intro A z b patch kernel season hz y X Y idx O ν HM area o near U B m E
  obtain ⟨give,cal,_,_⟩:= offered A patch kernel season z b hz
  obtain ⟨_,suite⟩ := seats.enter _ _ patch season X Y A.F z A.v give (by rw [patch]; exact cal.first)
  rw [patch] at suite
  have pc := season.case_
  rw [patch] at pc
  have hg : 0<A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos high).trans_le pc.beta))
  obtain ⟨room,price⟩:=charged A.fClock (Mosaic.ever high pc.beta pc.upper)
  exact (fields A.S A.F o X Y (wires_inside J A.S A.F o y b near) V clear O U ν χ hχ
    (linCash A.F z) suite.seat cal.first.extendsX m _ E hg room).trans price

end YM.Integration.FVA1Physical.Round2.Curvature
