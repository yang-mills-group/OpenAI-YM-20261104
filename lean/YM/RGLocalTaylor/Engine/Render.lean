import YM.RGLocalTaylor.Engine.SliceGauge
import YM.RGLocalTaylor.Engine.Interest
import YM.RGLocalTaylor.Engine.Ember
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cadre.Tassel

/-!
# Inserted pre-gauge render with native E6 masks

`onLog` keeps the exact molecule labels and permit predicates in the
base Cash output. No tests depend on how many powers of an inserted
probe are Taylor expanded. These kernels are for all-arity and all-order real
cost estimates. Proofs adapted/generalized from `Pattern`, `Sterad`, `Gio`
and `Cadre.Tassel`.
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

open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt

/-- Authorizes exactly the same preliminary terms before Taylor extraction. -/
def authorized (H : Cash W s μ L Q o C T R) (p : Molecule S) :=
  Ac.Spark H.supportP p ∧ troupe T R Q.halo (radiusB s) p

namespace Insert

def inTags (r : Insert T) (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F) : ℝ :=
  if authorized H p then
    likely fun i => r.onSlice (podium S G (H.unionP p) (radiusB s)) ((preps X (roster p)).taggedL i)
  else 0

def preGauge (r : Insert T) (H : Cash W s μ L Q o C T R) (p : Molecule S) (X : Coat T F) :=
  ∫ z, r.inTags H p (X.rinse z) ∂(Measure.pi fun _:Site c=>G.probHaar)

def onLog (r : Insert T) (H : Cash W s μ L Q o C T R) (χ : Chi) (p : Molecule S) (V : Config G c) :=
  likely fun i : Greenbelt.Reserve S => r.preGauge H p (prism T s χ o.K V (Greenbelt.allot i))

lemma onLog_of_forbidden {p : Molecule S} (h : ¬authorized H p) (r : Insert T) (V : Config G c) : r.onLog H χ p V = 0 := by
  unfold onLog preGauge inTags likely; simp only [if_neg h, integral_zero,sum_const_zero,mul_zero]

lemma preGauge_invariant (r : Insert T) (p) : GaugeInvariant (fun V => r.preGauge H p (vary X V)) := by
  intro z V
  let f:= MeasurableEquiv.piCongrRight (fun i=> MeasurableEquiv.mulRight (z i))
  let U:=(Measure.pi fun _:Site c=>G.probHaar)
  have hp : MeasurePreserving f U U := measurePreserving_pi _ _ (fun i : Site c=> measurePreserving_mul_right G.probHaar (z i))
  let Y:= vary X V
  dsimp only [preGauge]
  rw [← hp.integral_comp' (fun z => r.inTags H p (Y.rinse z))]
  apply integral_congr_ae; filter_upwards with u; have ht : gauge u (gauge z V) = gauge (f u) V := by
    funext i; unfold Lattice.gauge; change _= (u _*z _)* V _* (u _*z _)⁻¹; group
  unfold vary rinse; simp_rw [ht]; rfl

lemma onLog_invariant (r : Insert T) (p) : GaugeInvariant (r.onLog H χ p) :=
  let X i := prism T s χ o.K 1 (Greenbelt.allot (S:=S) i)
  fun z V => congr_arg likely (funext fun i => r.preGauge_invariant (X:=X i) p z V)

lemma nativeTag (H : Cash W s μ L Q o C T R) (hX : X.x=s) (p : Molecule S) :
    (native H p).inTags H p X=shelter X W o.a p R Q.table Q.halo := by
  unfold inTags shelter
  rw [show X.B=radiusB s from congr_arg _ hX]
  congr! 1

lemma nativeRender (H : Cash W s μ L Q o C T R) (p : H.ThinP) (V : Config G c) :
    (native H p.val).onLog H χ p.val V=leaflet H χ V p := by
  unfold onLog leaflet
  apply congr_arg likely; funext i
  exact integral_congr_ae (Eventually.of_forall fun z => nativeTag H (X:=(prism T s χ o.K V (Greenbelt.allot i)).rinse z) rfl p.val)
end Insert

namespace Fits
variable {p : Molecule S} {r : Insert T} (h : Fits H r (H.unionP p) j) (hX : X.x=s) (hK : X.width=o.K)
include h hX hK

lemma preGauge_seam : LocalOn (H.unionP p) (fun y:Config G c=> r.preGauge H p (vary X y)) ∧
    Measurable fun y:Config G c=> r.preGauge H p (vary X y) := by
  have hv : X.B=radiusB s:= congr_arg _ hX
  constructor
  · intro U V hu
    unfold Insert.preGauge Insert.inTags; split
    next =>
      apply integral_congr_ae; filter_upwards with z
      apply congr_arg likely; funext q
      rw [← hv]
      apply h.slice_local (X:=(preps (vary X U|>.rinse z) (roster p)).taggedL q) hX hK (Finset.Subset.refl _)
      -- rw hazard since podium uses X.B
      exact ⟨rfl,rfl,rfl,fun _ _=>Iff.rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,
        fun i hi hj => by unfold rinse; change gauge z U i=gauge z V i; unfold Lattice.gauge; rw [hu i hi hj]⟩
    rfl
  · let Y:= Measure.pi fun _: Site c=> G.probHaar
    have htag : Measurable fun y=> r.inTags H p (vary X y) := by
      unfold Insert.inTags; split_ifs
      next => refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> ?_); exact h.sliceBorel (X:=(preps X (roster p)).taggedL i) hX hK
      exact measurable_const
    have hp : Measurable fun (a:Config G c × (Site c → G.El))=> gauge a.2 a.1 := by
      refine measurable_pi_lambda _ fun i=> ?_; dsimp only [Lattice.gauge]; fun_prop
    exact (((htag.comp hp).stronglyMeasurable.integral_prod_right' (ν:=Y))).measurable

omit hX hK in
lemma log_seam : LocalOn (H.unionP p) (r.onLog H χ p) ∧ Measurable (r.onLog H χ p) := by
  let X i := prism T s χ o.K 1 (Greenbelt.allot (S:=S) i); let f i V:=r.preGauge H p (vary (X i) V)
  have he i := h.preGauge_seam (X:=X i) rfl rfl
  change LocalOn _ (fun V=> likely (fun i=> f i V)) ∧ Measurable (fun V=> likely (fun i=> f i V))
  exact ⟨fun U V h=>congr_arg likely (funext fun i=> (he i).1 U V h),measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => (he i).2)⟩

variable (he : (roster p).flags=∅) (hy : Healthy (Pressure.temp s) (H.unionP p) X.V)
include he hy

-- use planted flags with same gauge/spare
lemma realign (V : Config G c) (k : S.Choices) :
    r.onSlice (podium S G (H.unionP p) (radiusB s)) (vary ((planted X p).taggedL k) V) =
      r.onSlice (podium S G (H.unionP p) (radiusB s)) ((preps (vary X V) (roster p)).taggedL k) := by
  let Z := vary ((planted X p).taggedL k) V; let Z' := (preps (vary X V) (roster p)).taggedL k
  rw [← show Z.B=radiusB s from congr_arg radiusB hX]
  refine h.slice_local (X:=Z) (X':=Z') hX hK (Finset.Subset.refl _) ?_
  refine ⟨rfl,rfl,rfl,?_,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=> rfl⟩
  intro i hi; have he':i∉ RG.flags (Pressure.temp X.x) X.V:= by rw [hX]; exact Finset.disjoint_left.mp hy hi
  unfold Z Z' vary taggedL planted preps place; simp [he,he']

/-- Anchor AFTER putting in the actual sectors. All same-data cluster queries
work simultaneously at the germ (not necessarily at another calendar). -/
lemma atTags (hp : authorized H p) (V : Config G c) :
    r.inTags H p (vary X V) = likely fun k => r.onSlice (podium S G (H.unionP p) X.B) (vary ((planted X p).taggedL k) V) := by
  unfold Insert.inTags; rw [if_pos hp, show X.B=radiusB s from congr_arg _ hX]; exact congr_arg likely (funext fun k=> (h.realign hX hK he hy V k).symm)

variable {Ξ : Captain H j C' d v Y A b q B η k χ} (hχ : X.χ=χ)
include Ξ hχ
set_option quotPrecheck false
lemma legitimate {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {x:E} {V : E → Config G c} (hV : Mode V x j v) (hz : V x=X.V) :
    (fun y=> r.preGauge H p (vary X (V y))) =ᶠ[𝓝 x] fun y=>r.inTags H p (vary X (V y)) := by
  let K:= (planted X p); let Y' t y:= vary (K.taggedL t) (V y); have ht:= H.laws.data
  have hf t: ∀ᶠ y in 𝓝 x, Hue (Y' t y) :=
    eventual_hue (Ξ.oboe.flow F (K.taggedL t) hX hχ hK (planted_valid X p) E V x hz hV)
      (ht.localP F (K.taggedL t) hX hK (planted_valid X p)).sails
  filter_upwards [eventually_all.mpr hf] with y hh
  have hg z : r.inTags H p ((vary X (V y)).rinse z)=r.inTags H p (vary X (V y)) := by
    change r.inTags H p (vary X (gauge z (V y)))= _
    by_cases hp : authorized H p
    swap; · exact (if_neg hp).trans (if_neg hp).symm
    rw [h.atTags hX hK he hy hp, h.atTags hX hK he hy hp]
    rw [←chargedU]; exact congr_arg likely (funext fun t=> h.sliceGauge (X:=Y' t y) hX hK _ z (hh t))
  unfold Insert.preGauge; simp_rw [hg]; simp

section linear
variable {ι : Type} {w : Finset ι} {f' : ι → Insert T} (hf : ∀ i∈w,Fits H (f' i) (H.unionP p) j)
omit h
include hf
private lemma pre_add {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {x:E} {V : E → Config G c} (hV : Mode V x j v) (hz : V x=X.V) :
    (fun y => (Insert.together w f').preGauge H p (vary X (V y))) =ᶠ[𝓝 x] fun y=>∑ i∈w,(f' i).preGauge H p (vary X (V y)) := by
  let r:=Insert.together w f'; have hr:= Fits.together hf
  let K:= planted X p
  let P' := podium S G (H.unionP p) X.B
  let Y' (u : Insert T) i y:= u.onSlice P' (vary (K.taggedL i) (V y))
  have hF (t:S.Choices) : ∀ᶠ y in 𝓝 x,Y' r t y = ∑ i∈ w, Y' (f' i) t y := by
    have hg := Ξ.oboe.flow F (K.taggedL t) hX hχ hK (planted_valid X p) E V x hz hV
    exact Fits.add_near (X:=K.taggedL t) hX (planted_valid X p) hK hg Ξ.oboe.conduit Ξ.oboe.mode hf
  filter_upwards [Eventually.and (eventually_all.mpr hF) (hr.legitimate hX hK he hy hχ hV hz (Ξ:=Ξ)),(eventually_all_finset w).mpr (fun i hi=> (hf i hi).legitimate hX hK he hy hχ hV hz (Ξ:=Ξ))] with y ⟨hf',hl⟩ hh
  change r.preGauge _ _ _ = _ at hl
  rw [hl,sum_congr rfl (fun i hi=> hh i hi)]
  by_cases hp : authorized H p
  · rw [hr.atTags hX hK he hy hp,sum_congr rfl (fun i hi=> (hf i hi).atTags hX hK he hy hp _)]
    change likely (fun t=> Y' r t y)=∑ i∈w, likely fun t=> Y' (f' i) t y
    unfold likely; simp_rw [hf']; rw [sum_comm, Finset.mul_sum]
  simp only [Insert.inTags, if_neg hp,sum_const_zero]

omit hX hK hy hχ
lemma sum_onLog {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {x:E} {V : E → Config G c} (hV : Mode V x j v) (hy : Healthy (Pressure.temp s) (H.unionP p) (V x)) :
    (fun y => (Insert.together w f').onLog H χ p (V y)) =ᶠ[𝓝 x] fun y=>∑ i∈w,(f' i).onLog H χ p (V y) := by
  let X i := prism T s χ o.K (V x) (Greenbelt.allot (S:=S) i)
  let f (q : Insert T) i y := q.preGauge H p (vary (X i) (V y)); let g:=Insert.together w f'
  filter_upwards [eventually_all.mpr (fun i:Greenbelt.Reserve S=> Fits.pre_add (Ξ:=Ξ) (X:=X i) rfl rfl he hy rfl hf hV rfl)] with y hy
  change likely (fun i=> f g i y)=∑ i∈w, likely fun j=> f (f' i) j y
  have he(i):f g i y= ∑ j∈w,f (f' j) i y:= hy i
  unfold likely; simp_rw [he]; rw [sum_comm, Finset.mul_sum]
end linear
end Fits
end YM.RGLocalTaylor
