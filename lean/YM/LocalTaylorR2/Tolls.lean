import YM.LocalTaylorR2.Market
/-!
# L² toll on ONE Gaussian. Adaptation of March.launch.

Analytic leaf calculations will get the same `period-independent` toll
prior to moving from the physical H/T controls.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open Channel Gas Ursell Trees Animals Census Itinerary Port Reserves
variable {j k n : ℕ} {v r d A D x C' : ℝ} {H : Cash W s μ L Q o C T R} {χ : Chi}
-- Support-weight R and d/v used around this very price. Moments depend
-- on the full correlated Gaussian X.dice before multiplying.
structure StoresR2 (H : Cash W s μ L Q o C T R) (j : ℕ) (v d A D : ℝ) (k : ℕ) (x:ℝ) (n:ℕ) (χ:Chi) : Prop where
  sure : 1 ≤ x
  fuel : 0 ≤ D
  flight : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=s → X.χ=χ → X.width=o.K → X.manifest →
    ∀ (z:Air f G) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (V:E → Config G c) (y:E), V y=X.V → Mode V y j v →
    Clutch X z o.a R.beta d y j V (fun i=> steer X A (worldZ X R.beta z) (V i)) (fun i=> course X A R.beta z (V i)) ∧
    ∀ p:Molecule S, let I:=edgesM S (H.unionP p) (radiusB s)
    Brush j 1 (D*facescale I z^k) (fun i=> scalp I X (V i) R.beta A z) y
  moment : ∀ (F:Forest S.ratio) (X:Coat T F), X.x=s → X.χ=χ → X.width=o.K → X.manifest →∀ p:Molecule S, let I:=edgesM S (H.unionP p) (radiusB s)
    (∫ z,facescale I z^(k*j*2) ∂X.dice) ≤ (x*(1+H.shapeW p)^n)^2

namespace StoresR2
variable (M: StoresR2 H j v d A D k x n χ) (Ξ:Utopia H j v d r C' χ)
include M
lemma curtain (p:Molecule S) (F:Forest S.ratio) (X:Coat T F) (ht:X.x=s) (hζ:X.χ=χ) (hK:X.width=o.K) (hM:X.manifest) (a:ℝ) (ha:0≤a) (v:ℝ) (hv:0≤v) (J:Set (Air f G)) (hQ:MeasurableSet J) (hz:X.dice.real J ≤ v^2):
    let m:=(F.order G).prod X.dice; let Y z:= J.indicator (fun z=>facescale (edgesM S (H.unionP p) (radiusB s)) z^(k*j)) z
    Integrable (fun z:F.Slice G × Air f G=> a * Y z.2) m ∧
      (∫ z:F.Slice G × Air f G,a * Y z.2 ∂m) ≤ a*((x*(1+H.shapeW p)^n)*v) := by
  intro m f'
  let I:= edgesM S (H.unionP p) (radiusB s); let X' (z:Air f G):=facescale I z^(k*j)
  have hR:= H.laws.data.localP F X ht hK hM
  have hP':1≤1+H.shapeW p:= le_add_of_nonneg_right (H.positive_volume p)
  have he : 1 ≤ x:= M.sure
  have hm:=globes I hR.sails (k*j*2)
  have hV := (globes I hR.sails (k*j)).1
  have hTax : Integrable f' X.dice := hV.indicator hQ
  have hE: (∫ x,f' x ∂X.dice) ≤ (x*(1+H.shapeW p)^n)*v := by
    refine divideC _ X' hV _ (by positivity) _ hQ hz hv ?_ ?_
    · unfold X'; simp_rw [← pow_mul]; exact hm.1
    unfold X'; simp_rw [← pow_mul]; exact M.moment F X ht hζ hK hM p
  have hhP: Integrable (fun z:F.Slice G × Air _ G=> a*f' z.snd) m := (hTax.const_mul a).comp_snd _
  refine ⟨hhP,?_⟩
  rw [integral_prod _ hhP]
  dsimp only; simp_rw [integral_const_mul]; rw [ integral_const]; simp only [probReal_univ,one_smul]; exact mul_le_mul_of_nonneg_left hE ha

lemma earnings : FlareW H Ξ A (x*(1+D+2*r)^j) (n+j) := by
  refine ⟨?_⟩
  intro E _ _ _ F X Y y p hζ hM ht hK hr hu he hf hy m
  let I:= edgesM S (H.unionP p) (radiusB s); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p)
  let f(z : Air f G):= facescale I z^(k*j); let S':=1+H.shapeW p; let X' z:= J.indicator f z
  let a:=(∏ i∈p, Ξ.tag i)*(1+D+2*r)^j*S'^j
  have hx':(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p)
  have hD : 0≤D:= M.fuel
  have ha:a≥0 := mul_nonneg (mul_nonneg (prod_nonneg fun _ _=> Ξ.tagged _) (pow_nonneg (by have hq:= Ξ.active; positivity) _)) (pow_nonneg (zero_le_one.trans hx') _)
  obtain ⟨hV,hA⟩:= M.curtain p F X ht hζ hK hM a ha (Ξ.rad^(blaze p).card) (pow_nonneg Ξ.awake _) J (Poll.sounded ..)
    (by rw [← pow_mul, Nat.mul_comm, pow_mul]; exact Ξ.ship _ X ht hK hζ hM (blaze p))
  refine ⟨fun z=> a*X' z.2,hV,?_,?_⟩
  · rw [Utopia.meant,if_pos ((H.attends _).2 he),Ξ.remixes]
    exact hA.trans_eq (by unfold a S'; ring)
  intro ⟨v',z⟩; let X'' := X.wrapY v'
  obtain ⟨hp,hq⟩:=M.flight F X'' ht hζ hK hM z E Y y hy hf
  apply (accent Ξ X'' hf _ hu hM hr ht hζ hK hp (hq p) hD).climb _ le_rfl
  by_cases h:z∈J
  · change J.indicator _ z≤ a * X' z; unfold a X'; rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem h,Set.indicator_of_notMem h,mul_zero]
end StoresR2
end YM.LocalTaylorR2
