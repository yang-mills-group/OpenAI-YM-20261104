import YM.FVA2.StageBill
import YM.FVA2.Blended

/-!
# Finite inversion Wilson prescription

Representatives include literally the (unscaled) invariant Grassmann-free
cylinder plus a definite Laurent power, or a finite linear combination of such
terms and a definite coupling change. `Catalog.receipt` is a closed action /
chart / pure Gaussian definition for them. This module identifies it in the
open coarse variables as well, so theorem using them can depend on the
full running transfer. Clock is arbitrary provided the specified positive
weights and leading-coupling conventions hold. For example one may use the
formal physical resets of the calculation on the cover (in which case any
supply requirements on them like specific high-order flow or penalties are
separate hypotheses; never assuming them in our MS comparison). The vertex
model is given in a common coupling g_N with all log links scaled in g_N,
not a different coupling at each stage. Quotient variable at a coarse step
uses these coordinates as well. In `StageBill.tally_w` the changing β is
fully retained, no dropped l interaction. This prescription also makes sense
without a bulk schedule/certificate.

No relative power-law claims in any of these block estimates. The connection
to Pump covers etc is not licensed; same regulator finite step only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2
open Filter Topology Function Finset MeasureTheory FormalOPE.RG10
open FormalOPE.RG10.MarkovChain OpenSlots
open PertExtension Precision Inherit Push.Loops PertExtension.Chart Lattice RG
    PertExtension.GaussianScore PowerSeries
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric
    Papers Warp Line Roof Router Quadratic
open scoped Classical Topology ContDiff BigOperators InnerProductSpace
variable (G:Gauge) (n:Side)
section clock

structure Reg where
    L: Fabric G n
    sizes : 4 ≤ n.val
    frame: Cloth L

-- variables at step i = g_N * rhythm i. May give physical reset formulas to
-- fix rhythm; in finite correlation statements validity is not conditional on
-- pace supplies, even for orders extended once horizon readout fixed.
variable {G n}

def starts {G:Gauge} {n:Side}(T:Fabric G n) (w:T.Cost → (PowerSeries ℝ)ˣ): Prop:= match T with
 | .endcap _ _=> True
 | .layer _ _ _ _ _=> w none=1
structure Trajectory (R: Reg G n) where
    rhythm : R.L.Cost → (PowerSeries ℝ)ˣ
    zero i: coeff 0 (rhythm i).val =1
    compatible: starts R.L rhythm
variable {R: Reg G n} (T:Trajectory R)
abbrev Trajectory.stride := T.rhythm

def clockUnit (i:R.L.Accounts) : (PowerSeries ℝ)ˣ:= match i with | none=>1 | some i=>(T.stride i)⁻¹ ^2
def basisPrice (i:R.L.Accounts) := (clockUnit T i).val
-- β multiplying. Separate from g-level weight vertices from Jacobian/planted series.
lemma weight_top : basisPrice T none=1:= rfl
lemma weight_steps (i:R.L.Cost): basisPrice T (some i) * ((X* (T.stride i).val)^2) =X^2:= by
   rw [mul_pow,mul_left_comm]; unfold basisPrice clockUnit; rw [Units.val_pow_eq_pow_val,←mul_pow,Units.inv_mul,one_pow,mul_one]
lemma charged : ∀ i,0< term (basisPrice T i) 0:=by
    intro i; cases i with
    | none=> rw [weight_top]; simp [term]
    | some i=>
       have hx : coeff 0 ((T.stride i)⁻¹).val=1:=by
         have he:= congr_arg (fun p : PowerSeries ℝ=> constantCoeff p) (Units.inv_mul (T.stride i)); simp only [map_mul,map_one] at he
         simp_rw [← coeff_zero_eq_constantCoeff_apply] at he; rw [ show coeff 0 _= _ from T.zero i,mul_one] at he; exact he
       unfold term basisPrice clockUnit; simp_rw [Units.val_pow_eq_pow_val, coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, hx, one_pow]; exact zero_lt_one
lemma clock_rel {T Q:Trajectory R} (r:ℕ)(hx:∀ i, Through r (T.stride i).val (Q.stride i).val)(i:R.L.Accounts): Through r (basisPrice T i) (basisPrice Q i):= by
   cases i with
   | none=> rw [weight_top,weight_top]; exact Through.refl _
   | some i=> unfold basisPrice clockUnit; simp_rw [Units.val_pow_eq_pow_val]; exact Through.pow ((hx i).invAlready (Units.mul_inv ..) (Units.mul_inv ..)) _

-- open-step whole history calculation, rooted. `∅` enrollment is the COMMON
-- vacuum, taken in `purchase`, not this independent denominator.
variable (J:ChartRatio G)(hJ:LocalRatio J)
def paperPurchase (q:Ticket (Flats G n)):= purchase R.frame (basisPrice T) (charged T) hJ q
lemma compatible_order {T Q:Trajectory R}{a b:Ticket (Flats G n)}{r:ℕ}(hu:∀ i,Through r (T.stride i).val (Q.stride i).val) (hp : Through r a b) : Through r (paperPurchase T J hJ a) (paperPurchase Q J hJ b):=
    Bk.passage hJ _ _ _ _ _ (OpenSlots.restores _ _) (OpenSlots.restores _ _) (Bk.comparable (clock_rel r hu none)) (fun i=> clock_rel r hu (some i)) hp
end clock
variable {G n} {R : Reg G n}
variable (T:Trajectory R) (J:ChartRatio G)(hJ:LocalRatio J)
open Inversion MS MS.Book MS.Book.Program Coupling MS.Native

section
variable {W:Type}[LinearOrder W]
abbrev PayInput (G:Gauge)(ι:Type) := ι → Unscaled G
variable (s:Finset W) (ι: PayInput G s) (x: W→Cover) (h:Even n.val) (hv:∀ i:s,Continuous ((ι i).stencilVal n))
lemma pre_R {k:Unscaled G}(hv:Continuous (k.stencilVal n)) (x:Cover)(h:Even n.val) : Orb.PreTest (k.carries x n):= by
   let D:= Inversion.canonical G h
   let Z:=k.nativeMark x n
   let O:=k.carries x n
   have ht: Continuous O:= hv.comp (continuous_pi (fun i=> continuous_apply _))
   refine ⟨fun g _=> k.takes x g,⟨ht.comp Orb.continuous_links,?_⟩,ht⟩;
   rw [show (Orb.restrictedO O ∘ expLinks G _)= Z ∘ D.send_A from ?_];
   · apply (show ContDiffAt ℝ ∞ Z (D.send_A 0) from by rw [map_zero]; exact (k.native_smooth x).of_le le_top).comp
     exact D.send_A.contDiff.contDiffAt
   funext y; unfold Z D; simp only [Function.comp_apply]; rw [Cone.rooted_order]; rfl
include h hv in
lemma preSet : Orb.PreTest (unscaleFull s ι x n) := by
   let F: s → Wilson.Config G n→ ℝ:= fun i=> (ι i).carries (x i.val) n
   have ht (q:Finset (↥s)): Orb.PreTest (∏ a∈q,F a):=by
       induction q using Finset.induction with
       | empty=> rw [Finset.prod_empty]; exact ⟨fun _ _ _=> rfl,⟨continuous_const,contDiffAt_const⟩,continuous_const⟩
       | insert i q hi IH=>
          rw [prod_insert hi]; let V:=∏ a∈q,F a
          have hX:Orb.PreTest (F i):= pre_R (hv i) _ h
          exact ⟨fun u hu y=> congr_arg₂ (· * ·) (hX.gauge u hu y) (IH.gauge u hu y), ⟨hX.curved.boundedness.mul IH.curved.boundedness,hX.curved.germ.mul IH.curved.germ⟩, hX.continuous.mul IH.continuous⟩
   exact ht _
-- paper through.N, restores local links.B

def stubs := ∏ a:s, imprintRoot ((ι a).carries (x a.val) n)
include hv
include R in
lemma exposed : imprintRoot (unscaleFull s ι x n) = stubs (n:=n) s ι x := by
   unfold unscaleFull stubs; exact rootOfProduct R.frame _ _ (fun i _=> pre_R (hv i) _ R.L.even)

def payPure := Stack.drop (unscaleTot s ι) (paperPurchase T J hJ (stubs (n:=n) s ι x)) -- ℝ
lemma settled_bill : payPure T J hJ s ι x= Stack.drop (unscaleTot s ι) (PowerSeries.mk (Orb.diag (Orb.restrictedO (unscaleFull s ι x n)))) := by
   unfold payPure paperPurchase; rw [← exposed (R:=R) s ι x hv]; rw [OpenSlots.diagram R.frame (basisPrice T) (charged T) hJ (weight_top T) (preSet s ι x R.L.even hv)]
lemma incomeBill : Sync.align (payPure T J hJ s ι x)= PowerSeries.mk (pureVia n s ι x):= by
   rw [settled_bill T J hJ s ι x hv]; apply PowerSeries.ext; intro i; unfold Sync.align Stack.drop; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk,Nat.add_comm]; rfl

-- Records fixing both entire step choices and raw physical marks
variable {I: W→ Type}[∀ i,Fintype (I i)] (C:(w:W)→ I w→ Unscaled G) (K:(w:W)→ I w → ℝ → Sc)
omit hv

/-- Shared with analytic task: `paperPurchase` on constituent monomials,
retain required high orders, and cut external Laurent factors. Coupling
shift is to g_N at log-spacing. Weight polynomials may be chosen separately
(physical prescriptions below). No positivity consequences claimed here.
At this point coefficients for *individual* marks with all permitted
translations and word joins. -/
def WilsonPrescription (p:Team)(b:ℝ)(a:Cover) : Sc:= ∑ z:(i:s)→ I i.val, multiple (Catalog.multiplied K b s z) (substitute (shift p b) (Catalog.PCS (Sync.align (payPure T J hJ s (fun i=>C i.val (z i)) (fun i=>a+x i)))))
lemma by_stencils (p:Team)(b:ℝ)(a:Cover)(hc:∀ i∈s,∀ z:I i,Continuous ((C i z).stencilVal n)) : WilsonPrescription T J hJ s x C K p b a= Catalog.receipt p b a x C K n s := by
   unfold WilsonPrescription Catalog.receipt; apply Finset.sum_congr rfl; intro t _
   let Y:= fun i:s=> C i.val (t i)
   rw [show Sync.align (payPure T J hJ s Y (fun i=>a+x i))=PowerSeries.mk (pureVia n s Y (fun i=>a+x i)) from incomeBill T J hJ _ _ _ (fun i=> hc _ i.property (t i))]
   simp_rw [show ∀ X:Sc,Catalog.PCS (PowerSeries.mk X)=X from fun X=> funext (fun i=>PowerSeries.coeff_mk ..)]; rfl
open MS.Fleet
/-- End-to-end *finite*, positive marks included. This also works in b independently.
Continuum & normalization NOT a step-by-step equality here. -/
theorem finiteRegulator (p:Team)(b:ℝ)(a:Cover)(hc:∀ i∈s,∀ z:I i,Continuous ((C i z).stencilVal n)) :
   PhysicalSum G p b n true s x a (Catalog.pricing p C K) (WilsonPrescription T J hJ s x C K p b a):= by
   rw [by_stencils T J hJ s x C K p b a hc]; exact Catalog.blend a x p b R.L.even C K s
end
end YM.FVA2
