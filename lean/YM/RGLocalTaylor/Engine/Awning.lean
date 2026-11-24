import YM.RGLocalTaylor.Engine.Ember
import YM.RGLocalTaylor.Engine.Slice
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Captains

/-!
# A quantitatively strengthened shared integral estimate

Inscribe an additional power-saving reserve **relative to** the actual joint
warning budget, before assembly. Price the same `Utopia` integrals also with
new probes prepared at fixed marked order. `Awning` register is used to apply
the estimates to all these integrals, including products with extra analytic
vertices or marked factors. `discount` will be a coupling power with exponent
as large as desired. Registration is proved on the actual construction in later
files, not a hypothesis on `Gauge`/the physical choices.

Proofs adapted/generalized from CONNECTED_ACTIVITY_JETS_E6/{Das,March,Splay}.
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


/-- All the motion used to settle one estimated probe. The insertion method
works including for nonanalytic input functions of the held argument. -/
structure Awning (H : Cash W s μ L Q o C T R) (Ξ : Utopia H j v d r C' χ)
    (A b : ℝ) (discount e uJ vJ : ℝ) (jMoment kMoment : ℕ) : Prop where
  chart : Canary G A b
  sc : 8*o.a*Pressure.fiery G s L ≤ A/2
  nonneg : 0 ≤ discount
  small : discount ≤ 1
  earn : 0 ≤ e
  bSc : 0 ≤ uJ
  cSc : 0 ≤ vJ
  /-- Includes uniform derivative estimates on even reread/transformed terms. -/
  course_prices (F : Forest S.ratio) (X : Coat T F) (z : Air f G) (hX:X.x=s) (hk:X.width=o.K)
    (hv:X.χ=χ) (he:X.manifest) : ∀ (E : Type) [_hE : NormedAddCommGroup E]
    [_hER : NormedSpace ℝ E] (V : E → Config G c) (x : E), Mode V x j v → V x=X.V →
      let w i:= steer X A (worldZ X R.beta z) (V i)
      Clutch X z o.a R.beta d x j V w (fun i=>course X A R.beta z (V i)) ∧
      (∀ I : Finset (Bond f), Brush j 1 (uJ * facescale I z ^ jMoment) (fun t=> scalp I X (V t) R.beta A z) x) ∧
      ∀ K (M: Support c), K ⊆ M → Brush j 1 (vJ * coverNumber X.B M)
        (fun y=> X.enforce (2*o.a) (w y) (X.plaza K)) x
  shocks (F : Forest S.ratio) (X : Coat T F) (p : Molecule S) (hX:X.x=s) (hk:X.width=o.K)
    (hv:X.χ=χ) (he:X.manifest) : let I:= edgesM S (H.unionP p) (radiusB s); let J:= X.catastrophe (o.ξ/2) R.beta (blaze p)
      (∫ x,J.indicator (fun z => facescale I z^(jMoment*j)) x ∂X.dice) ≤
        e * (1+H.shapeW p)^kMoment * (discount*Ξ.rad)^(blaze p).card

/-- Pointwise bill on all Clutched fields. Discount comes later, via one
joint moment estimate after any number of warning events. -/
def CoveredAt (_Ξ : Utopia H j v d r C' χ) (f' : Insert T) (p : Molecule S) (A : ℝ)
    (weight speed : ℝ) : Prop :=
  ∀ (F : Forest S.ratio) (X : Coat T F) (z : Air f G), X.x=s → X.width=o.K → X.χ=χ → X.manifest →
    Healthy (Pressure.temp s) (H.unionP p) X.V → ∀ (E : Type)
    [_hE : NormedAddCommGroup E] [_hER : NormedSpace ℝ E] [_fE : FiniteDimensional ℝ E]
      (U : E → Config G c) (y : E), Mode U y j v → U y=X.V →
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator (fun _ => weight) z)
      (speed*(2*H.shapeW p)) (fun i=> f'.value (vary X (U i)) (course X A R.beta z (U i))) y

variable {Ξ : Utopia H j v d r C' χ} {weight uJ vJ e discount α : ℝ} {p : Molecule S}
  {f' : Insert T}

def speedBill (e uJ speed : ℝ) (j : ℕ) := e * (1+uJ+2*speed)^j

namespace Awning

variable (h : Awning H Ξ A b discount e uJ vJ k l)
include h

lemma covered_native (hp : troupe T R Q.halo (radiusB s) p) :
    CoveredAt Ξ (native H p) p A (∏ i∈p, Ξ.tag i) r := by
  intro F X z hx hK hχ hM hz E _ _ _ V x hV hω
  exact Ξ.acreage p (own p) hp hx hχ hM hK (hx.symm ▸ hz) hV
    (h.course_prices F X z hx hK hχ hM E V x hV hω).1

-- factor `scalp` supplies support/edge power of the derivative. Don't
-- repay the motion weight on each input hit. z is ONE Air vector.
lemma accent (hF : CoveredAt Ξ f' p A weight α) (hz:0≤weight) (ha:1≤α)
    {F : Forest S.ratio} {X : Coat T F} {z : Air f G} (hx:X.x=s) (hK:X.width=o.K)
    (hχ:X.χ=χ) (hM:X.manifest) (hy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : E → Config G c} {x:E} (hp : Mode V x j v) (hV : V x=X.V) {I : Finset (Bond f)} :
    Brush j ((X.catastrophe (o.ξ/2) R.beta (blaze p)).indicator
      (fun z=> weight*(1+uJ+2*α)^j*(1+H.shapeW p)^j*facescale I z^(k*j)) z) 1
      (fun i=> f'.onCourse I A R.beta X (V i) z) x := by
  have hT := (h.course_prices F X z hx hK hχ hM E V x hp hV).2.1 I
  have hp' := hF F X z hx hK hχ hM hy E V x hp hV
  refine (hT.paints hp').trim.climb ?_ le_rfl
  by_cases hh:z∈X.catastrophe (o.ξ/2) R.beta (blaze p)
  swap; · rw [Set.indicator_of_notMem hh,Set.indicator_of_notMem hh, mul_zero,zero_mul]
  rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh,one_mul]
  let f:= facescale I z; let W':= (1+H.shapeW p)
  change weight*_ ≤ _
  have hω:1≤f:= (Flux.expenses ..).1; have ht:1≤ W':= le_add_of_nonneg_right (H.positive_volume p)
  have hw:=h.bSc
  have h₁:1≤f^k:= one_le_pow₀ hω
  have hhX:0≤ 1+(uJ*f^k+α*(2*H.shapeW p)):= add_nonneg zero_le_one (add_nonneg hT.pos hp'.pos)
  have hh : 1+(uJ*f^k+α*(2*H.shapeW p)) ≤ (1+uJ+2*α)*W'*f^k := by
    have hc : f^k ≤ W'*f^k:= le_mul_of_one_le_left (zero_le_one.trans h₁) ht
    have hS:H.shapeW p ≤ W'*f^k:= (show H.shapeW p ≤ W' from le_add_of_nonneg_left zero_le_one).trans (le_mul_of_one_le_right (zero_le_one.trans ht) h₁)
    have hu:1≤ W'*f^k:= h₁.trans hc
    nlinarith only [mul_le_mul_of_nonneg_left hc hw,mul_le_mul_of_nonneg_left hS (zero_le_one.trans ha),hu]
  apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hhX hh j) hz).trans_eq
  rw [mul_pow,mul_pow,pow_mul]; unfold W' f; ring

lemma enhanced (hF : CoveredAt Ξ f' p A weight α) (hz:0≤weight) (ha:1≤α)
    {F : Forest S.ratio} {X : Coat T F} (hx:X.x=s) (hK:X.width=o.K)
    (hχ:X.χ=χ) (hM:X.manifest) (hy:Healthy (Pressure.temp s) (H.unionP p) X.V)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : E → Config G c} {x:E} (hf : Mode V x j v) (hV : V x=X.V) :
    let m:=(F.order G).prod X.dice; let I:=edgesM S (H.unionP p) (radiusB s)
    ∃ f, Integrable f m ∧
      (∫ x,f x ∂m) ≤ speedBill e uJ α j * weight * (1+H.shapeW p)^(l+j) * (discount*Ξ.rad)^(blaze p).card ∧
      ∀ z, Brush j (f z) 1 (fun t=> f'.rhythmic I A R.beta X (V t) z) x := by
  intro m I; let J:= X.catastrophe (o.ξ/2) R.beta (blaze p)
  let f(z : Air f G):= facescale I z^(k*j); let S':=1+H.shapeW p; let X' z:= J.indicator f z
  let a:= weight*(1+uJ+2*α)^j*S'^j
  have hu:= h.bSc
  have hS:(1:ℝ)≤S':= le_add_of_nonneg_right (H.positive_volume p)
  have ha' : 0 ≤ a:= mul_nonneg (mul_nonneg hz (by positivity)) (pow_nonneg (zero_le_one.trans hS) _)
  have hTax : Integrable (X': Air _ G → ℝ) X.dice :=
    (globes I (H.laws.data.localP F X hx hK hM).sails (k*j)).1.indicator (Poll.sounded ..)
  have hhP: Integrable (fun z:F.Slice G × Air _ G => a*X' z.snd) m := (hTax.const_mul a).comp_snd _
  refine ⟨fun z=> a*X' z.2,hhP,?_,?_⟩
  · rw [integral_prod _ hhP]
    dsimp only; simp_rw [integral_const_mul]; rw [integral_const]; simp only [probReal_univ,one_smul]
    apply (mul_le_mul_of_nonneg_left (h.shocks F X p hx hK hχ hM) ha').trans_eq
    unfold a S' speedBill; rw [pow_add]; ring
  rintro ⟨y,z⟩
  apply (h.accent hF hz ha (X:=X.wrapY y) (z:=z) hx hK hχ hM hy hf hV (I:=I)).climb _ le_rfl
  by_cases hv:z∈J
  · change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_mem hv,Set.indicator_of_mem hv]
  change J.indicator _ z≤a * X' z; unfold X'; rw [Set.indicator_of_notMem hv,Set.indicator_of_notMem hv,mul_zero]

lemma flareW : FlareW H Ξ A (speedBill e uJ r j) (l+j) := by
  constructor
  intro E _ _ _ F X V y p hχ hM hX hK hx ht he hp hV m
  have hu : CoveredAt Ξ (native H p) p A (∏ i∈p, Ξ.tag i) r := h.covered_native (p:=p) ht
  have hz : Healthy (Pressure.temp s) (H.unionP p) X.V := by
    -- rewrite directly (not dependent row of context)
    rw [hX] at hx; exact hx
  obtain ⟨f,hf,h₁,h₂⟩:= Awning.enhanced h (F:=F) (p:=p) (X:=X) (V:=V) (x:=y) hu
    (Finset.prod_nonneg (s:=p) (f:=Ξ.tag) fun i _ => Ξ.tagged i) Ξ.active hX hK hχ hM hz hp hV
  refine ⟨f,hf,h₁.trans ?_,fun i=> h₂ i⟩
  rw [Utopia.meant,if_pos ((H.attends p).2 he),Ξ.remixes]
  have hp0:= Ξ.awake; have hF:= h.nonneg; have hu:= h.bSc
  let B:= speedBill e uJ r j; have hb : 0≤B:= mul_nonneg h.earn (by have ht:=Ξ.active; positivity)
  apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hF hp0) (mul_le_of_le_one_left hp0 h.small) (blaze p).card) (mul_nonneg (mul_nonneg hb (Finset.prod_nonneg (s:=p) (fun _ _=>Ξ.tagged _))) (pow_nonneg (add_nonneg zero_le_one (H.positive_volume p)) (l+j))))
  unfold B; apply le_of_eq; ring
end Awning
end YM.RGLocalTaylor
