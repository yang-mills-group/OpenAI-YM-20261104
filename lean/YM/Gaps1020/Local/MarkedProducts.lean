import YM.Gaps1020.Local.Products
import YM.MergeProof.TeamParts
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Class
/-!
# Shared marked thermal germ

In the same RG step, jointly control a whole separated-wing Team on one
component. Multiple Leaf signs can enter with different carrier sites;
no assumption of disjoint *supports*. Build full angular variation and
covariance transport (following the same one-Leaf controls of Lotus/Daisy,
Team and Checkpoint A vacuum) BEFORE expansion into marker modes; in
particular the fine source ingredient(s) can be merely measurable. Includes
gas-origin marks and no reduction to scalar test kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
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

open PhysicalNext.Repeat.Lotus
-- CARE: symbol-own set of forced vertices from the *whole* p persists.
-- thermal multipliers/indexing applied only to non-sign components later.
abbrev others (M : Team R)(p : Molecule S) := p \ M.signs S

def seats (p:Molecule S)(R:Rep G f)(M:Team R)(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ)(X:Coat T F)(z:Air f G):= if M.signs S ⊆ p then M.paidU X a (worldZ X R.beta z)* Polar.floating X a R W Ñ z (own p) l (others M p) else 0

def teamWeight (p:Molecule S)(R:Rep G f)(M:Team R)(w:MulData (others M p))(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ)(X:Coat T F)(z:Air f G):ℝ:=
    seats p R M Ñ W a l X z *∏ i:↑(others M p), w i (row p R Ñ W a l X z i)

def teamWeightBars (p:Molecule S) (I:Finset (Tubular f G)) (X:Coat T F) (R:Rep G f)(M:Team R)(w:MulData (others M p)) (Ñ:ChartRatio G) (W a:ℝ)(l:ℕ) :=
    ∫ Y, (∫ z, lens₀ (Pond.circuit I X.relating) z * teamWeight p R M w Ñ W a l (X.wrapY Y) (Pond.spill I z)) ∂F.order G

-- copy locations, including support union and the manifest branch.
def teamWeightSeat (H:Support c)(B:ℕ)(X:Coat T F)(p:Molecule S)(R:Rep G f)(M:Team R)(w:MulData (others M p))(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ) :=
    let Z:= preps X (roster p)
    likely fun i=> teamWeightBars p (podium S G H B) (Z.taggedL i) R M w Ñ W a l

def teamWeightShelter (X:Coat T F)(p:Molecule S)(R:Rep G f)(M:Team R)(w:MulData (others M p))(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ) :=
    if Ac.Spark (areas R T l X.B) p ∧ troupe T R l X.B p then teamWeightSeat (ground R T l X.B p) X.B X p R M w Ñ W a l else 0

def teamWeightFringe (X:Coat T F)(p:Molecule S)(R:Rep G f)(M:Team R)(w:MulData (others M p))(Ñ:ChartRatio G)(W a:ℝ)(l:ℕ):=
    ∫ z, teamWeightShelter (X.rinse z) p R M w Ñ W a l ∂(Measure.pi fun _:Site c=>G.probHaar)

def teamWeightRecoil (B:Finset (Bond f)) (X:Coat T F)(C:Config G c)(d:ℝ)(Ñ:ChartRatio G)(p:Molecule S)(R:Rep G f)(M:Team R)(w:MulData (others M p))
    (W a:ℝ) (l:ℕ) (y:Air f G):=
    scalp B X C R.beta d y * teamWeight p R M w Ñ W a l (vary X C) (course X d R.beta y C)

def teamWeightRhythm (B:Finset (Bond f)) (X:Coat T F)(C:Config G c)(d:ℝ)(Ñ:ChartRatio G)(p:Molecule S)(R:Rep G f)(M:Team R)(w:MulData (others M p))
    (W a:ℝ)(l:ℕ)(t:F.Slice G × Air f G) := teamWeightRecoil B (X.wrapY t.1) C d Ñ p R M w W a l t.2

abbrev emptyTeamData (M:Team R)(p:Molecule S): MulData (others M p) := fun _ _=>1
lemma lit (p:Molecule S)(M:Team R)(a:ℝ)(z:Air f G) : teamWeight p R M (emptyTeamData M p) Ñ W a l X z=seats p R M Ñ W a l X z := by unfold teamWeight emptyTeamData; simp
lemma absorbs (B:Finset (Bond f)) (X:Coat T F)(C:Config G c)(d:ℝ)(Ñ:ChartRatio G)(p:Molecule S)(R:Rep G f)
    (M:Team R)(w:MulData (others M p))(W a:ℝ)(l:ℕ)(t:F.Slice G × Air f G) : teamWeightRhythm B X C d Ñ p R M w W a l t= teamWeightRhythm B X C d Ñ p R M (emptyTeamData M p) W a l t *
      ∏ i:↑(others M p), w i (row p R Ñ W a l (vary (X.wrapY t.1) C) (course (X.wrapY t.1) d R.beta t.2 C) i):= by
  unfold teamWeightRhythm teamWeightRecoil; rw [lit, teamWeight,mul_assoc]

section meas
variable (X : Coat T F) (hΞ : ShellAccess S G X.x W X.width γ) (h : Intake P T X.x R) (hP : LocalRatio Ñ)
variable (p:Molecule S) (M:Team R) (w:MulData (others M p)) (hw : ∀ i, Measurable (w i))
include hP hΞ h hw
lemma teamCollected {E:Type*}[MeasurableSpace E]{V:E→Config G c}{Y:E→F.Slice G}{u:E→Air f G}
    (hv : Measurable V)(hY:Measurable Y)(hu:Measurable u): Measurable (fun t=> teamWeight p R M w Ñ W a l (drive X (V t) (Y t)) (u t)) :=by
  have hp: Measurable (fun t=> seats p R M Ñ W a l (drive X (V t) (Y t)) (u t)):=by
    unfold seats; split_ifs
    swap; · exact measurable_const
    have hD: Measurable (fun t=> worldZ (drive X (V t) (Y t)) R.beta (u t)) := (compassBro h.ready hv X hY hΞ R.beta).2.2 _ hu
    exact (Finset.measurable_fun_prod M.own (fun i _=>(i.borel.comp (Art.entering _ hv hY hD)).mul ((X.enforce_b (2*a) (X.plaza (areas R T 0 X.B (i.turn.badge S)))).comp hD))).mul (collectionB X hΞ h hP hv hY hu (own p) a l (others M p))
  exact hp.mul (Finset.measurable_fun_prod _ fun i _=> (hw i).comp (bornB X hΞ h hP hv hY hu a l (own p) i))

lemma teamBarsMeasured (I : Finset (Tubular f G)) (a : ℝ) (l:ℕ) : Measurable fun y=> teamWeightBars p I (vary X y) R M w Ñ W a l := by
  let E' := (Config G c × F.Slice G) × Body (↥ I)
  let V (t:E'):= t.1.1; let Y (t:E'):= t.1.2
  let f' (i:E') := lens₀ (Pond.circuit I (vary X (V i)).relating) i.2* teamWeight p R M w Ñ W a l (drive X (V i) (Y i)) (Pond.spill I i.2)
  have hv : Measurable V := measurable_fst.comp measurable_fst
  have hh := c_measured X.shutter (A:=fun i=> (vary X (V i)).plate) (fun i j=> (Art.borel_plate X h.ready i j).comp hv)
  have hz : Measurable f' := (bulbB (fun i j=> hh.1 i.val j.val : Borel fun i=> Pond.circuit I (vary X (V i)).relating) measurable_snd).mul
    (teamCollected X hΞ h hP p M w hw hv (measurable_snd.comp measurable_fst) ((Pond.spill_m I).comp measurable_snd))
  exact ((hz.stronglyMeasurable.integral_prod_right' (ν:=volume)).integral_prod_right' (ν:=F.order G)).measurable
lemma teamShelterMeasured (a:ℝ)(l:ℕ): Measurable fun y=> teamWeightShelter (vary X y) p R M w Ñ W a l:= by
  change Measurable fun y=> if Ac.Spark (areas R T l X.B) p ∧ troupe T R l X.B p then teamWeightSeat (ground R T l X.B p) X.B (vary X y) _ _ _ _ _ _ _ _ else 0
  split_ifs
  · refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> ?_)
    let Z := (preps X (roster p)).taggedL i
    exact teamBarsMeasured Z hΞ (show Intake P T Z.x R from h) hP p M w hw (podium S G _ X.B) a l
  exact measurable_const
end meas

section locality
-- Following Flotsam, Tropolis, Sterad. No evaluation off period chart moved.
variable {X' : Coat T F} (p:Molecule S) (M:Team R) (w:MulData (others M p))
variable {Z : Support c} {u v:Air f G} (hb : Borough X X' Z u v (own p) (own p) R) (hr : Room P S T X.x)
    (hl : 500≤l) (h : Intake P T X.x R)
include hb hr hl h
lemma teamWeightSync (hp : ground R T l X.B p ⊆ Z) : teamWeight p R M w Ñ W a l X u=teamWeight p R M w Ñ W a l X' v := by
  have hx : seats p R M Ñ W a l X u=seats p R M Ñ W a l X' v := by
    unfold seats; split
    next he=>
      have hP(i:Leaf R)(hi:i∈M.own):i.paidU X a (worldZ X R.beta u)=i.paidU X' a (worldZ X' R.beta v):= by
        let t : Head S := i.turn.badge S
        have he : ground R T l X.B {t}⊆ Z:=by unfold ground; rw [singleton_biUnion]; exact (subset_biUnion_of_mem _ (he (show t∈M.signs S from mem_image_of_mem _ hi))).trans hp
        have hc:= i.census (a:=a) (k:=own p) (k':=own p) (W:=W) (Ñ:=Ñ) X {t} h hr hl hb he
        simpa only [Leaf.floret,t,if_pos (mem_singleton_self _), Polar.floating,erase_singleton,prod_empty,mul_one] using hc
      have hZ : ground R T l X.B (others M p) ⊆ Z:= (show ground R T _ _ _ ⊆ ground R T l X.B p from Finset.biUnion_subset.mpr (fun i (hi:i∈others M p)=>subset_biUnion_of_mem _ (sdiff_subset hi))).trans hp
      exact congr_arg₂ (·*·) (prod_congr rfl hP) (hb.flops hr hl h a W Ñ hZ)
    next=> rfl
  unfold teamWeight; rw [hx]
  apply congrArg; apply Finset.prod_congr rfl; intro i hi
  have he:= (hb.rooms hr R.beta).preserve hr hl h a W Ñ (i:=i.val) hb (Subset.trans (subset_biUnion_of_mem (areas R T l X.B) (sdiff_subset (show i.val∈others M p from i.2))) hp)
  dsimp only at he; rw [X.oldysis h.positive, X'.oldysis h.positive] at he
  exact congr_arg (w i) he
omit hb
lemma teamBarsSync (hp : ground R T l X.B p ⊆ Z) (hV : Village X X' Z) :
    teamWeightBars p (podium S G Z X.B) X R M w Ñ W a l=teamWeightBars p (podium S G Z X.B) X' R M w Ñ W a l := by
  let I:=podium S G Z X.B
  have he : Pond.circuit I X.relating=Pond.circuit I X'.relating := by ext i j; exact hV.same_cov hr j.val j.property i.val
  unfold teamWeightBars; rw [he]; apply integral_congr_ae; filter_upwards with q; apply integral_congr_ae; filter_upwards with y
  apply congr_arg₂ (·*·) rfl; let v:=Pond.spill I y
  exact teamWeightSync p M w (show Borough (X.wrapY q) (X'.wrapY q) Z v v (own p) (own p) R from
    ⟨hV.wrap q q (fun _ _=> rfl),fun _ _=> rfl,fun _ _=>Iff.rfl⟩) hr hl h hp

lemma teamShelterLocal : LocalOn (ground R T l X.B p) (fun V:Config G c=> teamWeightShelter (vary X V) p R M w Ñ W a l) := by
  intro V U he
  let s := ground R T l X.B p
  unfold teamWeightShelter; simp_rw [show ∀ V,(vary X V).B=X.B from fun _=>rfl]
  split
  next => apply congr_arg likely; funext k; apply teamBarsSync (X:=(preps (vary X V) (roster p)).taggedL k) p M w hr hl (show Intake P T _ R from h) (show ground R T l X.B p⊆s from Subset.refl _)
          exact ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=> rfl,fun _ _=>rfl,he⟩
  next => rfl
end locality
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
