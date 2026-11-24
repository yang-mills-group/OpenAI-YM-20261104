import YM.FVA2.OrdersAt

/-!
# Concrete Fk reading on the open-coarse inversion step

All quantifiers finite *regulator*. Uses exactly the prediction map & branch
from Fabric, not a price picked by changing posterior laws. Not identified
with the `Admits` physical block call on a different space (or the same
space away from the common germ). No gas estimates here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Bk
open Filter Topology Function Finset MeasureTheory
open FormalOPE.RG10 FormalOPE.RG10.MarkovChain OpenSlots
open RGComparison.Core16 RGComparison.Core16.Lumen Lumen.Planet
open PertExtension Precision Inherit Push.Loops PertExtension.Chart Lattice RG
    PertExtension.GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
    Papers Warp Line Roof Router Quadratic
open scoped Classical Topology ContDiff BigOperators InnerProductSpace
variable {G:Gauge} {I : Type}[Fintype I] {c f:Side}
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y]

section any
variable [Nontrivial G.Color]

def scalarTag (G:Gauge)[Nontrivial G.Color] : G.Color:= (exists_norm_eq G.Color zero_le_one).choose
def scalarPrice (G:Gauge)[Nontrivial G.Color]:= innerSL ℝ (scalarTag G)
lemma budgetScalar (g:ℝ): scalarPrice G (g • scalarTag G)=g:= by
   have ht : ‖scalarTag G‖=1:= Exists.choose_spec (exists_norm_eq G.Color zero_le_one)
   simp [map_smul,smul_eq_mul,scalarPrice, ht]

variable (y:Y) (S:Direction G I × Y→ ℝ)


def showCosts (z : Lumen.Point G I) := S (fun i=> (@Lumen.axis G).symm (z.2 i), scalarPrice G z.1 • y)
def formalShelf : Shelf G Unit I where
   sector:=⟨1,1,1, Nat.one_pos,zero_lt_one⟩ -- these budgets simply unused, no Uniform assertion here
   U:=fun _=>showCosts y S
   R:=1
   δ:=1
   knot:=1
   Q:=1
-- Allow different realizations, even when non-Steady, for coefficient algebra.
variable {f:Side}
variable (loc:I→ Site f) {T:Type}(W:ℝ→T→Forge.Sky G I→ℝ) (K:ℝ→ T→ Forge.Sky G I→ℝ)
def formalPanel : Planet (formalShelf y S) f I Unit T where
   loc:=loc
   root:=fun _=>0
   meter:=W
   cost:=fun g t x _=> K g t x
   glyph:=id
   stem:=fun _=>some
   ray:=fun _=>scalarTag G
omit [Nontrivial G.Color] in
lemma axis_eq : ∀ᶠ i in 𝓝 (0:G.Color),(@Lumen.axis G).symm (G.curvature (G.lieExp i))=i:=by
   let U:=@Lumen.axis G; filter_upwards [U.open_source.mem_nhds (show 0∈U.source from ContDiffAt.mem_toOpenPartialHomeomorph_source ..)] with x hx using U.left_inv hx
omit [FiniteDimensional ℝ Y] in
lemma costume : Fk.rise (formalPanel y S loc W K) =ᶠ[𝓝 0] mount y S:= by
   filter_upwards [eventually_all.mpr (fun i:I=> ((continuous_apply i).tendsto ((0:Direction G I))).comp ((continuous_snd.tendsto (0:Fk.Door G I)))|>.eventually axis_eq)] with x hx
   unfold Fk.rise Fk.lapse Fk.postage; rw [Fintype.sum_unique];
   exact congr_arg (x.1^2 + ·) (congr_arg S (Prod.ext (funext hx) (congr_arg (· • y) (budgetScalar (G:=G) x.1))))

def origins (G: Gauge) [Nontrivial G.Color] (I:Type): Stuff G I (Option I) := fun i=> match i with
   | some j=> Sum.inl j
   | none=> Sum.inr (scalarTag G)
local notation "U"=> origins G I

def stampF (O:Direction G I × Y → ℝ) (x:Option I→G.Color): ℝ:= showCosts y O (x none, x ∘ some)
omit [FiniteDimensional ℝ Y] in
lemma placed (O:Direction G I × Y → ℝ): stampF y O ∘ Fk.scene U =ᶠ[𝓝 0] O ∘ sideChange y:= by
   filter_upwards [eventually_all.mpr (fun i:I=> ((continuous_apply i).tendsto ((0:Direction G I))).comp ((continuous_snd.tendsto (0:Fk.Door G I)))|>.eventually axis_eq)] with x hx
   exact congr_arg O (Prod.ext (funext hx) (congr_arg (· • y) (budgetScalar (G:=G) x.1)))
end any
section initial
variable {S: StepData c f} (H:S.patch.Branches S.kernel G)
variable (P: Inside S.ratio) (t:S.Choices) (J:ChartRatio G) (hJ:LocalRatio J)
local notation "D"=> Blocking.Index S P
local notation "E"=> Cross (G:=G) S P
local notation "F"=> Flats G f
local notation "Y"=> Flats G c
local notation "K"=> Quadratic.core
local notation "η"=> blankRight (G:=G) P
local notation "Λ"=> (firstBill (G:=G) (n:=f) ∘ η)
local notation "Q"=> gated P (initialFull G f 1) t 1
variable (y:Flats G c)
def physicalStart : E × Y→ℝ:= (firstBill ∘ η)+substep (G:=G) P t
local notation "Ω"=> physicalStart (G:=G) P t
lemma first_bond : ContDiffAt ℝ ω Λ 0:=
  (show ContDiffAt ℝ ω firstBill (η 0) from by rw [map_zero]; exact firstGranted).comp _ (LinearMap.toContinuousLinearMap η).contDiff.contDiffAt
include H
lemma smooth_quarter : ContDiffAt ℝ ω Ω 0:= (first_bond _).add (subReady _ _ H)
lemma castFirst (x:E×Y): (Q).flourish x=2*jet Ω 2 x:= by
    unfold gated; rw [show _=(genesis 1 firstBill).flourish (η x) + (genesis 1 (substep P t)).flourish x from
       (rfl:(addOn (drag η (initialFull G f 1).Q) _).flourish x= (genesis 1 firstBill).flourish (η x) + (genesis 1 (substep P t)).flourish x)];
    rw [payments η 1 firstBill firstGranted x,native,native, physicalStart, Inherit.plus 2 (first_bond _) (subReady P t H)]; simp [term,mul_add]

lemma rayHere : rayBlock J Ω=receipt P t J 1 (initialFull G f 1):= by
    rw [ receipt ]; simp only [initialFull]; rw [pullPay _ _ _ firstGranted]
    have hv:Tracks.shadow 1=0:= by unfold Tracks.shadow Tracks.deduct; rw [neg_eq_zero]; apply PowerSeries.ext; intro i; rw [map_zero]; simp [term]
    have he(g:E × Y→ℝ): pay 1 g=advancing g:= by simp [pay,term,hv,Stack.roll]
    simp_rw [OpenSlots.chip,he]; have hq:advancing Ω= advancing (firstBill ∘ η)+advancing (substep P t):= by
        apply Stack.into; intro x; apply PowerSeries.ext; intro i; rw [map_add,map_add,levels,levels,levels]; unfold Radial.layers; by_cases hx:i=0
        · simp [hx]
        rw [ physicalStart, Inherit.plus _ (first_bond _) (subReady _ _ H)]; simp [hx,add_comm] -- subscript
    unfold rayBlock; rw [hq,compose_two _ _ (advancing_zero _) (advancing_zero _)]; ring

-- For this seam also give actual `cost` germ witness and shared common choice. `meter` here can just pick arbitrary t and use it on *all* markers. No claim of Admits (space differs from Followup force gas).
variable [Nontrivial G.Color]
omit H in
def linksCross (x: Forge.Sky G (Blocking.Index S P)) : LinkFrame G f := fun i=> if h:¬P.Innate i then x (⟨i,h⟩: Blocking.Index S P) else 1
omit H in
def earnings (g:ℝ)(t':S.Choices)(x:Forge.Sky G (Blocking.Index S P)):= wilson (linksCross P x)+penalty S t' (linksCross P x) (expLinks G _ (g • y))
def FirstPanel : Planet (formalShelf y Ω) f D Unit S.Choices:= formalPanel y Ω (fun i=> i.val.val.1) (fun _ t' _=> if t=t' then 1 else 0) (earnings (G:=G) P y)
omit H [Nontrivial G.Color] in
lemma dressStep (x:E): linksCross P (Fk.spread x)= expLinks G _ (OpenSlots.extend P x) := by
    funext i; unfold linksCross; by_cases hx:P.Innate i <;> simp [OpenSlots.extend,expLinks,hx]; rfl
local notation "A"=> FirstPanel P t y

include t
lemma pricedHere : ∀ᶠ x:Fk.Door G D in 𝓝 0, ∀ t':S.Choices, earnings P y x.1 t' (Fk.spread x.2)= (Fk.lapse A x):=by
    have h₁:Tendsto (fun x:Fk.Door G D=> (expLinks G _ (OpenSlots.extend P x.2))) (𝓝 0) (𝓝 1):=by
        let V:= OpenSlots.extend (G:=G) P; have hp: Continuous (fun x:Fk.Door G D=> expLinks G _ (V x.2)):=by
           refine continuous_pi (fun i=>?_); exact (show Continuous G.lieExp from by fun_prop).comp ((continuous_apply i).comp (V.continuous_of_finiteDimensional.comp continuous_snd))
        rw [← show expLinks G _ (OpenSlots.extend P ((0:Fk.Door G D).2))=1 from by rw [Prod.snd_zero, map_zero, identity_zero]]; exact hp.tendsto _
    filter_upwards [h₁.eventually (same_choice S H t), costume y Ω (fun i: Blocking.Index S P=> i.val.val.1) (fun _ t' _=> if t=t' then 1 else 0) (earnings (G:=G) P y)] with x hx hh
    intro t'; change x.1^2+(Fk.lapse A x)= x.1^2+ Ω (sideChange y x) at hh; rw [add_left_cancel hh, earnings, BlockGauge.penalty, dressStep, show atStep S t' _ = atStep S t (expLinks G _ (OpenSlots.extend P x.2)) from funext (fun i=> congr_fun (hx t') i.val)]
    rfl
-- first layer normalized valuation with all tags at once. `r` external powers; only shifted slot range. Need min when truncating negative orders.
include hJ
theorem first_tag (p:Ticket (E×Y)) (g:E × Y→ℝ) (hg:ContDiffAt ℝ ω g 0) (hp: p=Stack.rise g)
   {D':Type}[Fintype D'] (f': Stuff G (Blocking.Index S P) D') (ψ : (D'→G.Color)→ℝ)
   (h:(Quadratic.core Q).RespectsPrice) (he: ψ ∘ Fk.scene f' =ᶠ[𝓝 0] g ∘ sideChange y) (r:ℕ):
    PowerSeries.mk (Fk.read A J f' ψ r)= Stack.drop r (Stack.read y (Broadcast P t J 1 (initialFull G _ 1) h p)):= by
    rw [ hp,Broadcast, ←rayHere H, OrdersAt y J hJ Ω (smooth_quarter H _ _) Q (castFirst H _ _) h (show Fk.rise A =ᶠ[𝓝 0] mount y Ω from costume ..) g hg f' ψ he r];
lemma first_any (O:E×Y→ℝ)(hg:ContDiffAt ℝ ω O 0) (h:(K Q).RespectsPrice) (r:ℕ):
    PowerSeries.mk (Fk.read A J (origins G D) (stampF y O) r)= Stack.drop r (Stack.read y (Broadcast P t J 1 (initialFull G _ 1) h (Stack.rise O))) := first_tag H P t J hJ y _ O hg rfl _ _ h (placed y O) r
end initial
end YM.FVA2.Bk
