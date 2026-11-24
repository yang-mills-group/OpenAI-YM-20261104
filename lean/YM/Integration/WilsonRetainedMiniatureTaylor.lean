import YM.Integration.WilsonCoherentMayerTariff
import YM.LocalTaylorR2.Pavilion.Sheets

/-! The three original short logarithmic factors on the actual marked Gaussian draw. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonRetainedMiniatureTaylor

open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open LocalTaylorR2 LocalTaylorR2.Canvas LocalTaylorR2.Port RGLocalTaylor
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
  {F : Forest S.ratio} {P : Teller G} {Q : ConnectedActivityE6.Target G P}
  {W s μ C : ℝ} {o : Target.Order G W} {R : Rep G f} {H : Cash W s μ L Q o C T R}

abbrev letter (k : Miniature c f) : LogIndex c f := .inr (.inl k)

theorem sameDraw (H : Cash W s μ L Q o C T R) (X : Coat T F)
    (hx : X.x=s) (hm : X.manifest) (w : Air f G) (k : Miniature c f)
    (clear : Healthy (Pressure.temp X.x) (sleeve S X.B Q.halo k) X.V) :
    Mayer.exponent H X w (identityLog (letter k)) = weightLog H (letter k) F X w := by
  have room : Room P S T X.x := hx.symm ▸ H.laws.data.room
  have e := Polar.leisure X o.a R Q.table room hm Q.buys w (worldZ X R.beta w)
    (Vine.shine X room hm R.beta w) (letter k) clear
  exact Real.exp_injective (sub_left_inj.mp e)

private theorem sample {p j : ℕ} {ζ b : ℝ} {χ : Chi} (pass : Pass H p j (Pavilion.mosaics H p) ζ 0 0 1 b χ)
    (X : Coat T F) (hx : X.x=s) (hw : X.width=o.K) (hm : X.manifest) (hχ : X.χ=χ)
    (w : Air f G) (k : Miniature c f)
    (clear : Healthy (Pressure.temp X.x) (sleeve S X.B Q.halo k) X.V) :
    |Mayer.exponent H X w (identityLog (letter k)) - Pavilion.mosaics H p (letter k) F X w| ≤ b := by
  let V : ℝ → Config G c := fun _ => X.V
  let u : ℝ → Directions G f := fun _ => worldZ X R.beta w
  let z : ℝ → Air f G := fun _ => w
  have ht : 0<X.t := R.p.threshold_pos.trans_eq (hx.symm ▸ H.laws.intake : Intake P T X.x R).received.temp
  have pulse := mul_pos o.large ht
  have move : Mode V (0:ℝ) j 0 := ⟨le_rfl, fun i => a_oneB G (X.V i) le_rfl⟩
  have cl : Clutch X w o.a R.beta 0 (0:ℝ) j V u z := by
    refine ⟨rfl,H.laws.intake.positive,rfl,pulse,fun _ => rfl,le_rfl,?_,?_⟩
    · intro i
      simpa [u] using (Brush.certified (E:=ℝ) (x:=0) (k:=j) (d:=1) zero_le_one (0:G.Color))
    · exact Eventually.of_forall fun y => ⟨fun _ _ => rfl, by change 0 < (2*o.a)*X.t; exact mul_pos (mul_pos (by norm_num) o.large) ht⟩
  have bill := (pass.round k ℝ F X V u z 0 w hx hw hm hχ move cl).bound
  rw [sameDraw H X hx hm w k clear]
  exact bill

variable (P : Teller G) (Q : ConnectedActivityE6.Target G P) (o : Target.Order G W)

theorem purchased (L : Side) (D : Patch) (hD : D.Branches P.bind G)
    (χ : Chi) (p : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ s : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f)
      (μ C : ℝ) (H : Cash W s μ L Q o C T R), S.patch=D →
      ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s → X.width=o.K → X.manifest → X.χ=χ →
      ∀ (w : Air f G) (k : Miniature c f),
      Healthy (Pressure.temp X.x) (sleeve S X.B Q.halo k) X.V →
      |Mayer.exponent H X w (identityLog (letter k)) - Pavilion.mosaics H p (letter k) F X w|
        ≤ betaF G s L ^ (-((p:ℝ)+1-η)/2) := by
  have zero : Rate G L (-(1/2)) (fun _ => 0) := by
    intro a _
    filter_upwards [(Work.E09.betaF_growth G L).eventually_gt_atTop 0] with s hs
    simpa using Real.rpow_nonneg hs.le a
  obtain ⟨b,hb,_,paid⟩ := Pavilion.titular (fun _=>0) (fun _=>0) L o P Q p 0 0 zero zero
    (Eventually.of_forall fun _ => le_rfl) D hD χ
  filter_upwards [paid,hb (-((p:ℝ)+1-η)/2) (by linarith)] with s hs hr
  intro c f S T R μ C H hS F X hx hw hm hχ w k clear
  exact (sample (hs c f S T R μ C H hS) X hx hw hm hχ w k clear).trans ((le_abs_self _).trans hr)

end YM.Integration.WilsonRetainedMiniatureTaylor
end
