import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Captains
import YM.Gaps1020.Local.ExpShares
/-!
# Thermal log powers — physical integration on one common component

The multipliers act **inside** the simultaneous tag/field/Gaussian integration.
Bounds below will therefore include nonlinear powers of an exponent of the
low-head list as actual joint moments, not repeated products of separately
integrated heads. Support and gauge extension as in AnalyticNext. We follow
the change-of-variables and domination proofs there, generalizing from
products of vertices to weighted products (`ψ` will be given by ExpShares).
Taken alone this file is not a comparison of represented RG data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {z : Air f G}

-- Use subtype multiplier so later convolution needs no Decidable lookup
abbrev MulData (p : Molecule S) := (i:↑p)→ℝ→ℝ

def row (p:Molecule S)(R:Rep G f)(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ)(X:Coat T F)(z:Air f G)(i:Head S):ℝ:=
    Polar.ember X a R W Ñ (worldZ X R.beta z) (X.input (worldZ X R.beta z)) z (own p) l i

def weighted (p:Molecule S)(w:MulData p)(R:Rep G f)(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ)(X:Coat T F)(z:Air f G):ℝ:=
    (Polar.floating X a R W Ñ z (own p) l p)*∏ i:↑p, w i (row p R Ñ W a l X z i)

def weightedBars (p:Molecule S) (w:MulData p) (I:Finset (Tubular f G)) (X:Coat T F) (R:Rep G f) (Ñ:ChartRatio G) (W a:ℝ)(l:ℕ) :=
    ∫ Y, (∫ z, lens₀ (Pond.circuit I X.relating) z * weighted p w R Ñ W a l (X.wrapY Y) (Pond.spill I z)) ∂F.order G

-- copy locations, including support union and the manifest branch.
def weightedSeat (H:Support c)(B:ℕ)(X:Coat T F)(p:Molecule S)(w:MulData p)(R:Rep G f)(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ) :=
    let Z:= preps X (roster p)
    likely fun i=> weightedBars p w (podium S G H B) (Z.taggedL i) R Ñ W a l

def weightedShelter (X:Coat T F)(p:Molecule S)(w:MulData p)(R:Rep G f)(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ) :=
    if Ac.Spark (areas R T l X.B) p ∧ troupe T R l X.B p then weightedSeat (ground R T l X.B p) X.B X p w R Ñ W a l else 0

def weightedFringe (X:Coat T F)(p:Molecule S)(w:MulData p)(R:Rep G f)(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ):=
    ∫ z, weightedShelter (X.rinse z) p w R Ñ W a l ∂(Measure.pi fun _:Site c=>G.probHaar)

def weightedRecoil (B:Finset (Bond f)) (X:Coat T F)(C:Config G c)(d:ℝ)(Ñ:ChartRatio G)(p:Molecule S)(w:MulData p)(R:Rep G f)
    (W a:ℝ) (l:ℕ) (y:Air f G):=
    scalp B X C R.beta d y * weighted p w R Ñ W a l (vary X C) (course X d R.beta y C)

def weightedRhythm (B:Finset (Bond f)) (X:Coat T F)(C:Config G c)(d:ℝ)(Ñ:ChartRatio G)(p:Molecule S)(w:MulData p)(R:Rep G f)
    (W a:ℝ)(l:ℕ)(t:F.Slice G × Air f G) := weightedRecoil B (X.wrapY t.1) C d Ñ p w R W a l t.2
lemma absorb (B:Finset (Bond f)) (X:Coat T F)(C:Config G c)(d:ℝ)(Ñ:ChartRatio G)(p:Molecule S)(w:MulData p)(R:Rep G f)
    (W a:ℝ)(l:ℕ)(t:F.Slice G × Air f G) : weightedRhythm B X C d Ñ p w R W a l t= rhythm B X C d Ñ p R W a l t *
      ∏ i:↑p, w i (row p R Ñ W a l (vary (X.wrapY t.1) C) (course (X.wrapY t.1) d R.beta t.2 C) i):= by
  unfold weightedRhythm rhythm recoil weightedRecoil weighted; rw [mul_assoc]

section meas
variable (X : Coat T F) (hΞ : ShellAccess S G X.x W X.width γ) (h : Intake P T X.x R) (hP : LocalRatio Ñ)
variable (p:Molecule S) (w:MulData p) (hw : ∀ i, Measurable (w i))
include hP hΞ h hw
lemma collected {E:Type*}[MeasurableSpace E]{V:E→Config G c}{Y:E→F.Slice G}{u:E→Air f G}
    (hv : Measurable V)(hY:Measurable Y)(hu:Measurable u): Measurable (fun t=> weighted p w R Ñ W a l (drive X (V t) (Y t)) (u t)):=
  (collectionB X hΞ h hP hv hY hu (own p) a l p).mul (Finset.measurable_fun_prod _ fun i _=> (hw i).comp (bornB X hΞ h hP hv hY hu a l (own p) i))

lemma barsMeasured (I : Finset (Tubular f G)) (a : ℝ) (l:ℕ) : Measurable fun y=> weightedBars p w I (vary X y) R Ñ W a l := by
  let E' := (Config G c × F.Slice G) × Body (↥ I)
  let V (t:E'):= t.1.1; let Y (t:E'):= t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2* weighted p w R Ñ W a l (drive X (V i) (Y i)) (Pond.spill I i.2)
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have hh := c_measured X.shutter (A:=fun i=> (vary X (V i)).plate) (fun i j=> (Art.borel_plate X h.ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j=> hh.1 i.val j.val : Borel fun i=> Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (collected X hΞ h hP p w hw hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd))
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=volume)).integral_prod_right' (ν:=F.order G)).measurable
lemma shelterMeasured (a:ℝ)(l:ℕ): Measurable fun y=> weightedShelter (vary X y) p w R Ñ W a l:= by
  change Measurable fun y=> if Ac.Spark (areas R T l X.B) p ∧ troupe T R l X.B p then weightedSeat (ground R T l X.B p) X.B (vary X y) _ _ _ _ _ _ _ else 0
  split_ifs
  · refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> ?_)
    let Z := (preps X (roster p)).taggedL i
    exact barsMeasured Z hΞ (show Intake P T Z.x R from h) hP p w hw (podium S G _ X.B) a l
  exact measurable_const
end meas

section locality
-- Following Flotsam, Tropolis, Sterad. No evaluation off period chart moved.
variable {X' : Coat T F} (p:Molecule S) (w:MulData p)
variable {Z : Support c} {u v:Air f G} (hb : Borough X X' Z u v (own p) (own p) R) (hr : Room P S T X.x)
    (hl : 500≤l) (h : Intake P T X.x R)
include hb hr hl h
lemma weightedSync (hp : ground R T l X.B p ⊆ Z) : weighted p w R Ñ W a l X u=weighted p w R Ñ W a l X' v := by
  unfold weighted; rw [hb.flops hr hl h a W Ñ hp]
  apply congrArg; apply Finset.prod_congr rfl; intro i hi
  have he:= (hb.rooms hr R.beta).preserve hr hl h a W Ñ (i:=i.val) hb (Subset.trans (subset_biUnion_of_mem (areas R T l X.B) i.2) hp)
  dsimp only at he; rw [X.oldysis h.positive, X'.oldysis h.positive] at he
  exact congr_arg (w i) he
omit hb
lemma barsSync (hp : ground R T l X.B p ⊆ Z) (hV : Village X X' Z) :
    weightedBars p w (podium S G Z X.B) X R Ñ W a l=weightedBars p w (podium S G Z X.B) X' R Ñ W a l := by
  let I:=podium S G Z X.B
  have he : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hV.same_cov hr j.val j.property i.val
  unfold weightedBars; rw [he]; apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  apply congr_arg₂ (·*·) rfl; let v:=Pond.spill I y
  exact weightedSync p w (show Borough (X.wrapY q) (X'.wrapY q) Z v v (own p) (own p) R from
    ⟨hV.wrap q q (fun _ _=> rfl),fun _ _=> rfl,fun _ _=>Iff.rfl⟩) hr hl h hp

lemma shelterLocal : LocalOn (ground R T l X.B p) (fun V:Config G c=> weightedShelter (vary X V) p w R Ñ W a l) := by
  intro V U he
  let s := ground R T l X.B p
  unfold weightedShelter; simp_rw [show ∀ V,(vary X V).B=X.B from fun _=>rfl]
  split
  next => apply congr_arg likely; funext k; apply barsSync (X:=(preps (vary X V) (roster p)).taggedL k) p w hr hl (show Intake P T _ R from h) (show ground R T l X.B p⊆s from Subset.refl _)
          exact ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=> rfl,fun _ _=>rfl,he⟩
  next => rfl
end locality
end YM.ConnectedActivityE6.Blaze.Thermal1020
