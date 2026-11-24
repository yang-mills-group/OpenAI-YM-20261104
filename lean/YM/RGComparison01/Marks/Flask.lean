import YM.RGComparison01.Marks.Scalp
import YM.RGComparison01.Marks.Meristem
import YM.RGComparison01.Marks.Aperture
import YM.RGComparison01.Premium

/-!
# Simultaneous Angular guarantee for Teams

 Keep the *unmarked Utopia* booster (on a polynomial currency) for
 stencil legs; for recurring marks replace by Root-Wing. For older e
 use angular scale replacement before resonance. No proliferation of
 unpriced analytic/source rays. No flag differentiation.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ Λ μ s κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Bloch Laurent Progress.StationaryScenes Green Census Itinerary Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
open YM.RGComparison01
namespace Team
variable (M : Team R) (X : Coat T F) {U : Cash W s μ L Q o C T R}
variable {E:Type} {d C' D A B Y v :ℝ} {j k ℓ:ℕ} {χ:Chi} {Ω : Utopia U j v d r C' χ}
structure Cloak (Ω:Utopia U j v d r C' χ) (w j' : ℝ) (u:Head S→ℝ) (X : Coat T F) (z:Air f G) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P:E → Config G c) (V:E→ Directions G f) (W' : E→Air f G) (x:E) : Prop where
  posts : ∀ k : Finset ℕ,∀ i, Healthy (Pressure.temp X.x) (U.supportP i) X.V→
    Brush j (u i) (w*spanW T R X.B Q.halo i) (fun t=> Polar.ember (vary X (P t)) o.a R W Q.table (V t) (X.input (worldZ X R.beta z)) (W' t) k Q.halo i) x
  pip : ∀ M:Leaf R,Brush j M.weight (j'*spanW T R X.B Q.halo (M.turn.badge S)) (fun t=> M.fond (vary X (P t)) o.a (V t) (X.input (worldZ X R.beta z))) x

-- cost for a head consumed literally at a log-marker input of this calculation.
-- For unassigned E require ticket b. wlog designate M subset from e.
variable (B' : ℝ) (u : Head S→ℝ) {b:ℕ→ℝ} {D':ℝ} (Ψ : ℕ→Prop)
def maskRaise (Ω:Utopia U j v d r C' χ) (Ψ : ℕ→Prop) (b : ℕ→ℝ) (e : ℝ) : Head S → ℝ:= fun i=> match i with
 | Sum.inr (.inr (.inl (.inl (.inl k)))) => if Ψ k then e*b k else Ω.tag i*r^j
 | _ => Ω.tag i*r^j
abbrev silent (Ω:Utopia U j v d r C' χ) := maskRaise Ω (fun _=>False) (fun _=>0) 0
lemma raises {e:ℝ} (he : 0≤e) (hu:∀ i,Ψ i → 0 ≤ b i) (i:Head S): 0≤ maskRaise Ω Ψ b e i:= by
  unfold maskRaise; split
  next k =>
    split
    next h=> exact mul_nonneg he (hu k h)
    next => exact mul_nonneg (Ω.tagged _) (pow_nonneg (zero_le_one.trans Ω.active) _)
  next => exact mul_nonneg (Ω.tagged _) (pow_nonneg (zero_le_one.trans Ω.active) _)
lemma span_floor (U:Coat T F) (M:Head S) (l:ℕ): 1≤ spanW T R U.B l M:= by
  rcases M with i|i
  · exact le_rfl
  exact le_add_of_nonneg_right (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {x:E} {z:Air f G} {V:E → Config G c} {V':E→Directions G f}
    {g:E→Air f G}
lemma extra_cloth (Ω:Utopia U j v d r C' χ) (he : X.x=s) (ht:X.width=o.K) (hv:X.χ=χ) (hM:X.manifest)
  (hV: Mode V x j v) (hx:Clutch X z o.a R.beta d x j V V' g) (hd: 1≤ D')
  (h: ∀ Y (M:Support c), Y⊆ M → Brush j 1 (D'*coverNumber X.B M) (fun y=> X.enforce (2*o.a) (V' y) (X.plaza Y)) x)
  {e:ℝ} (hE : ∀ (K: E→ℝ) (t q:ℝ), Brush j t q K x → t≤1 → Brush j (e*t) q (fun i=> Real.exp (K i)-1) x)
  (hq:∀ i,Ψ i→ ∀ U, |R.activities.regularOccurrence R.p i U| ≤ b i)
  (hH : ∀ i, Ψ i → b i ≤ 1) : Cloak Ω D' D' (maskRaise Ω Ψ b e) X z V V' g x := by
  let Θ t k i:= Polar.ember (vary X (V t)) o.a R W Q.table (V' t) (X.input (worldZ X R.beta z)) (g t) k Q.halo i
  have hw i k (hp:Healthy (Pressure.temp X.x) (U.supportP i) X.V): Brush j (Ω.tag i*r^j) (D'* spanW T R X.B Q.halo i) (fun t=> Θ t k i) x:= by
    have hz:=Ω.stream E F X V V' g x z he ht hv hM hV hx k i hp
    change Brush _ (stout _ _ _ _ _ _ _ _) _ _ _ at hz
    have ht : Brush j (Ω.tag i) (r*spanW T R X.B Q.halo i) (fun t=> Θ t k i) x:= by
      unfold Utopia.tag; rw [← show X.B=radiusB s from congr_arg radiusB he]; exact hz
    let s:= spanW T R X.B Q.halo i; have hv:0 ≤ s:= zero_le_one.trans (span_floor X i Q.halo)
    have hs:s≤D'*s:= le_mul_of_one_le_left hv hd
    refine ⟨ht.smooth,hv.trans hs,fun n hn=>?_⟩
    apply (ht.order _ hn).trans; rw [mul_pow, ← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ Ω.active hn) ht.nonneg) (pow_le_pow_left₀ hv hs n) (pow_nonneg hv _) (mul_nonneg ht.nonneg (pow_nonneg (zero_le_one.trans Ω.active) _))
  have hb (U : Support f) : Footprint.enlargement S.ratio 0 X.B (RG.inspected U)⊆ Footprint.enlargement S.ratio Q.halo X.B (RG.inspected U):= Corona.halo_mono (by omega) (Subset.refl _)
  have hi (M: Wing) : Brush j 1 (D'*spanW T R X.B Q.halo (M.badge S)) (fun y=> X.enforce (2*o.a) (V' y) (X.plaza (Matter.areas R T 0 X.B (M.badge S)))) x:= by
    apply (h (Matter.areas R T 0 X.B (M.badge S)) (Matter.areas R T Q.halo X.B (M.badge S)) (by simp_rw [M.badge_area]; apply hb)).climb le_rfl
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hd)
    cases M <;> exact le_trans (le_add_of_nonneg_right (Nat.cast_nonneg _)) (le_add_of_nonneg_left zero_le_one)
  constructor
  · intro k i hl; unfold maskRaise; split
    next n =>
      split
      next hp=>
        have hv := (Brush.certified (k:=j) (x:=x) (le_refl (0:ℝ)) (-(R.activities.regularOccurrence R.p n (X.input (worldZ X R.beta z))))).climb (v:=b n) (by rw [norm_neg]; exact hq n hp _) le_rfl
        apply hE (fun i=> frost (vary X (V i)) o.a R (V' i) (X.input (worldZ X R.beta z)) (.inl n)) _ _ _ (hH _ hp)
        exact (hv.paints (hi (.logKey n))).climb (mul_one _).le (zero_add _).le
      next=> exact hw _ _ hl
    next=> exact hw _ _ hl
  intro i; exact (((Brush.certified (k:=j) (x:=x) (le_refl (0:ℝ)) (i.ingredient (X.input (worldZ X R.beta z)))).climb (i.earn _) le_rfl).paints (hi i.turn)).climb (mul_one _).le (zero_add _).le
end Team
end YM.PhysicalNext.Repeat.Lotus
