import YM.FVA2.FkMoment
import YM.FVA2.RankStamp
import YM.FormalOPE.RG10.OpenSlots.Passenger

/-!
# In the inversion RG10 Model, identify `Fk.read` on the top conditional kernel

Use **one** Branch-compatible chosen tag. Fixed positive gauge by Interior P.
No integration of the coarse field in this call. Use bare g on parent, not
shifting the block-cost in this top identity (cost with same g on either side).
`next` implements the actual conditional formal readout after this shared Fk-boundary,
including whole conditional denominator as a function of `field` and every slot
in it. Momentum/Position are future purchaser arguments.

The compatibility here concerns the *actual definitions* of §Fk.read. Do not
interpret this quotient-Planet as asserting `Planet.Steady`, which includes
abstract analytic price/admissibility data unnecessary for any of these formal
identifications. It is a label for the top action and Haar chart, with the same
(nonintegrated) Step.kernel/tag fixed and no ancillary variation of costs. Thus
Fork.ray_value also applies to the bona fide `Planet.Steady` suppliers
(with THEIRS, not our kernel). In particular analytic estimates on a physical
step on full torus (like `parcela`) cannot silently stand in for ones on this
orbit step. Keep the two distinguished by geometry.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.OrbitPlanet
open RayScatter
open Function Filter Topology Metric Finset PowerSeries
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MultiGauge.Blocking FormalOPE.RG10.Sync
open Lattice Gauge Precision Fabric Inherit PertExtension PertExtension.Chart GaussianScore RG RGComparison.Core16 RGComparison.Core16.Lumen
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {c f:Side}{G:Gauge}{S:StepData c f}
variable (P:Inside S.ratio)(t:S.Choices)(h:S.patch.Branches S.kernel G)
local notation "I"=> Blocking.Index S P
local notation "F"=> Cross (G:=G) S P
local notation "C"=> Flats G c
local notation "μ"=> tangent G (Blocking.Index S P)

abbrev Joint := Cross (G:=G) S P × Flats G c
local notation "U"=> initialFull G f 1

def price : Cross (G:=G) S P × Flats G c→ℝ:= firstBill ∘ blankRight P + substep P t
include h
lemma hot : ContDiffAt ℝ ω (price (G:=G) P t) 0:= ContDiffAt.add ( OpenSlots.leaned (blankRight P) firstGranted ) (subReady P t h)
omit h

local notation "Œ"=> LinkFrame G f
local notation "Ō"=> Forge.Sky G (Blocking.Index S P)

-- drape only fast free links. Mesh and offset sit in OEdge; Lumen.loc extended at any edge, irrelevant to prices here.
def drape (y:Forge.Sky G (Blocking.Index S P)): LinkFrame G f:= fun i=> if h: P.Innate i then 1 else y (Subtype.mk i h : Blocking.Index S P)
lemma draped (y: Cross (G:=G) S P): drape P (Fk.spread y)=expLinks G _ (OpenSlots.extend P y):= by
   ext1 i; by_cases he:P.Innate i; simp [drape,he, OpenSlots.extend,expLinks ]; simp [drape,he,OpenSlots.extend,expLinks]; rfl
abbrev chartAt (x:Joint (G:=G) P):= drape P (Fk.spread x.1)

local notation "Sρ"=> Option (Orb.OEdge c)
-- billing from actual log/gauge chart. W.POSE.U cost.Shelf; split to support rays one per coarse entry. Quotient

def plank (y:LinkFrame G f) (e: Orb.OEdge c)(x:G.Color):= S.kernel.penalty * G.price ( G.lieExp x * (atStep S t y e)⁻¹)
def money (s:Option (Orb.OEdge c)) (x:Lumen.Point G (Blocking.Index S P)):=
   let y:= drape P (fun i=> launch ( x.2 i )); match s with
   | none=> Fabric.wilson y
   | some e=> plank t y e x.1

-- Sector record metadata not used in Fk.read. exhibit dummy radii as no claims.
def code : Shelf G (Option (Orb.OEdge c)) (Blocking.Index S P):= { «U»:= money P t, R:=1, δ:=1/2, Q:=1, knot:=1/2, sector:=⟨1,1,1,zero_lt_one,zero_lt_one⟩ }

-- X/Y compatibility.Prediction germs same tag.At each y.F

def frame (y:Flats G c) : Planet (code P t (G:=G)) f I Sρ Unit := {
 loc e:= ((show Orb.OEdge f from e.val).val).1
 root e:=e.elim 0 (fun e=>S.ratio.root e.val.1)
 cost τ _ v j:= Option.elim j ( Fabric.wilson (drape P v) ) (fun e=> plank t (drape P v) e (τ • y e))
 meter _ _ _:=1
 glyph:=id
 stem _ x:= some x
 ray j:=j.elim 0 y }

-- Actual formula in P.bureau(g), at all g (even where Taylor not used). CONNECT.Price exact.
lemma earned (p:Œ)(v:C): ∑ i:Orb.OEdge c, plank t p i (v i)= BlockGauge.penalty S t p (expLinks G _ v):= by unfold BlockGauge.penalty BlockGauge.distance; rw [Finset.mul_sum]; rfl
variable (y:Flats G c)
local notation "ℱ"=> frame P t y
lemma action_true (x:ℝ)(g:Ō): (( frame P t y|>.F x ).action () g) = Fabric.wilson (drape P g) + BlockGauge.penalty S t (drape P g) (expLinks G _ (x • y)):= by
     unfold Forge.Base.action; rw [ Fintype.sum_option ]; refine congr_arg₂ (·+·) rfl (earned t (drape P g) (x • y))
open MeasureTheory
lemma real_bureau (x:ℝ)(v:Ō): (ℱ).bureau x v= Real.exp (-(Fabric.wilson (drape P v)+ BlockGauge.penalty S t (drape P v) (expLinks G _ (x • y)))/x^2) := by
     rw [← action_true]; unfold Planet.bureau Forge.Base.output; rw [Fintype.sum_unique]; change (1:ℝ)*_= _; rw [one_mul]; rfl
-- `∑ k Money·up`. germs (not price-estimates window). All indices allowed. 
lemma launched : ∀ᶠ x:Fk.Door G I in 𝓝 0,∀ i,launch (G.curvature (Fk.spread x.2 i))= Fk.spread x.2 i:= by
     apply Filter.eventually_all.mpr; intro i; let F0(x:Fk.Door G I):=Fk.spread x.2 i; have hz:F0 0=1:= by simp [F0,Fk.spread]
     exact (( show Tendsto F0 (𝓝 0) (𝓝 1) from hz ▸ ((show Continuous F0 from by unfold F0 Fk.spread; fun_prop).tendsto 0) ).eventually leaving)

lemma charge_ray : Fk.rise ℱ =ᶠ[𝓝 0] (RayScatter.charge (price (G:=G) P t) 1 y):= by
   filter_upwards [launched (G:=G) (P:=P)] with x hx; let p:=Fk.spread x.2; let q:=drape P p;
   have he : drape P (fun i=> launch (G.curvature (p i)))=q:= congr_arg _ (funext hx)
   have hM(z:Sρ) : Fk.postage ℱ x z = (ℱ).cost x.1 () (Fk.spread x.2) z:= by
     cases z with
     | none=> exact congr_arg Fabric.wilson he
     | some e => exact congr_arg (fun q=> plank t q e _) he
   rw [Fk.rise, Fk.lapse, show (∑ i:Sρ,Fk.postage ℱ x i) = ((ℱ).F x.1 ).action () p from Finset.sum_congr rfl (fun i _=>hM i), action_true]; change x.1^2+_=1*x.1^2 + ( _ + _); rw [one_mul]; rw [ draped (P:=P) (y:=x.2) ]; rfl

lemma chip_one (u:Joint (G:=G) P→ℝ): chip 1 u= Stack.exponential (Stack.advancing u):=by unfold chip pay; rw [show StationaryMarks.Tracks.shadow (1:PowerSeries ℝ)=0 from ?_, _root_.map_zero,zero_mul, add_zero, show Series.Tested.term 1 0= (1:ℝ) from coeff_zero_one ]; simp [Stack.roll]; apply PowerSeries.ext; intro i; unfold StationaryMarks.Tracks.shadow StationaryMarks.Tracks.deduct Series.Tested.term; rw [ map_neg, map_zero, coeff_mk, coeff_one,if_neg (by omega),neg_zero] -- parser

local notation "pQ"=> gated P U t 1
include h
lemma precision (x: Cross (G:=G) S P × Flats G c): (pQ).flourish x=2* Series.Radial.jet (price P t) 2 x:= by
      unfold price gated; rw [ Inherit.plus (a:= firstBill ∘ blankRight P) _ (OpenSlots.leaned (blankRight P) firstGranted) (subReady P t h) x ]; change Quadratic.flourish (Quadratic.genesis 1 firstBill) (blankRight P x)+ Quadratic.flourish _ x=_; rw [Quadratic.payments (blankRight P) 1 firstBill firstGranted,Quadratic.native,Quadratic.native]; simp [Series.Tested.term]; ring
variable (J:ChartRatio G)
lemma economical : Fork.interaction J (price (G:=G) P t) = receipt P t J 1 U:= by
    unfold Fork.interaction receipt; rw [ price ]; let p:=firstBill (G:=G) (n:=f) ∘ blankRight P; let q:=substep (G:=G) P t
    have he: Stack.advancing (p+q)=Stack.advancing p+ Stack.advancing q:= by
        have hp:p+q=∑ i:Bool,(1:ℝ) • (if i then p else q):= by simp
        rw [hp, OpenSlots.advance_jets (u:=fun _:Bool=>1) Finset.univ _ (fun i=> ?_)]; simp [Stack.roll];
        split; exact OpenSlots.leaned (blankRight P) firstGranted; exact subReady P t h
    rw [ he, compose_two _ _ (Stack.advancing_zero _) (Stack.advancing_zero _),show (U).W=chip 1 firstBill from rfl,pullPay (blankRight P) 1 firstBill firstGranted, chip_one,chip_one,← mul_assoc ]; rw [mul_comm (MarkovChain.Warp.boost _ _)]

-- Hessian core proof needs only positivity of lower projection at any given continuation;
-- here it is born from Bank at the chosen weights rather than postulated. arbitrary steps then use Bank recursively.
variable (hJ:LocalRatio J)(L: Fabric G c)(T:Cloth L)(hf:Even f.val)
local notation "T0"=> Cloth.inLayer (t:=t) (b:=h) (h:=hf) P T
include L T hf in
theorem billedStep : (pQ).core.RespectsPrice := ( paidRoot (J:=Orb.tray G) ( T:= T0 ) (a:=1) (fun i=> by change 0< coeff 0 (1:PowerSeries ℝ); rw [ coeff_zero_one ]; exact zero_lt_one)).respects -- order of T0 definition.Texture
-- more generally if continuation not desired. use floor L originally. needs he even etc.

section mark
open Source
variable (O: Wilson.Observable G f)


abbrev tagAll : Stuff G I I := Sum.inl
def book (O:Wilson.Observable G f)(x:Cross (G:=G) S P):ℝ:= O (Orb.liftLinks (drape P (fun i=> launch ( x i ))))
def ode : Flats G f→ℝ:= (O ∘ Orb.liftLinks) ∘ expLinks G _
omit h in
lemma carried : book P O ∘ Fk.scene (tagAll P) =ᶠ[𝓝 0] (ode O ∘ blankRight P) ∘ recover y:= by
     filter_upwards [launched (G:=G) P] with x hx
     have hv : drape P (fun i=> launch (G.curvature (Fk.spread x.2 i)))= expLinks G _ (OpenSlots.extend P x.2) := (congr_arg (drape P) (funext hx)).trans (draped P x.2); exact congr_arg ( O ∘ Orb.liftLinks ) hv
local notation "h0"=> billedStep P t h L T hf
abbrev distinct (O:Wilson.Observable G f) := ContDiffAt ℝ ω (ode O) 0
variable (hd:distinct O)
-- literal `Fk.read ... a` always defined for any a.For negative powers use via a provided
include h hJ hd L T hf in
lemma arrival (a:ℕ): PowerSeries.mk ( Fk.read ℱ J (tagAll P) (book P O) a)= Stack.drop a ( Stack.read y (Broadcast P t J 1 U h0 (boost (blankRight P) ( imprintRoot O )))):= by
    unfold Broadcast; rw [ Fork.perch ℱ J hJ (hot P t h) pQ (precision P t h) h0 y (tagAll P) ( charge_ray P t y ) (ode O ∘ blankRight P) ( carried P y O ) (OpenSlots.leaned (blankRight P) hd), economical P t h J ]; unfold imprintRoot Stack.imbed; rw [ ← MarkovChain.Vault.climbing (blankRight P) (hd.of_le le_top)]; rfl
include h hJ L T hf
lemma originCost : PowerSeries.mk (Fk.birth ℱ J)= PowerSeries.C ( RayScatter.basePower pQ h0 y μ 1 * Stack.overhead J I ) * ( Stack.read y (Update P t J 1 U h0).W ):= by rw [ Fork.uniform_nil ℱ J hJ (hot P t h) pQ (precision P t h) h0 y ( charge_ray P t y ), economical P t h J, Update ]; -- rfl
omit h hJ L T hf
lemma distinct_source {F':MS.Native.Dot G Lattice.Cover}{b:Weights G}(hp:Brand F' b) (x:Site f) : distinct (Source.put b x) := by
    unfold distinct; let M:=Trans.coverL G f
    rw [show ode (Source.put b x)=( (Source.put b x) ∘ MS.Native.Chart.nation) ∘ M from funext fun i=> congr_arg (Source.put b x) (Trans.assemble_exp G f i) ]; exact leaned M (Source.pos_jet hp x)
lemma distinctOne : distinct (1:Wilson.Observable G f):= contDiffAt_const
lemma distinctProduct {W:Type}(ts:W→Wilson.Observable G f)(s:Finset W)(h:∀ i∈s,distinct (ts i)): distinct (∏ i∈s,ts i):= by
    induction s using Finset.induction_on with| empty=> rw [Finset.prod_empty]; exact distinctOne | insert i s hi ih=> rw [Finset.prod_insert hi]; exact ContDiffAt.mul (h i (by simp)) (ih (fun j hj=> h j (mem_insert_of_mem hj)))

-- eventual umbrella.Covers.Perimeter dimension.G.Rank.
end mark
end YM.FVA2.OrbitPlanet
