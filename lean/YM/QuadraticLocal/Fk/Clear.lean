import YM.QuadraticLocal.Fk.Boost
import YM.QuadraticLocal.Fk.Meet
import YM.QuadraticLocal.Earn.Solo
/-!
# Combine also those already globally field-independent marks

They were admitted analytically, hence their full (upper order too) values remain
available before future calls. They are billed even in presence of earth-model clear
peers. The projected analytic cover kernels must account for markReceipt on the output:
 `Row.powerAudit`. This file doesn't even assume that the coherence cut between those
 tasks remains in force after transporting the physical-insertion scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
variable (F: Finset ι) (L:Layout G) (T:Finset Age)
open Comparison.RG02 Comparison.RG02.Bulk
namespace Row
set_option quotPrecheck false
variable (A:Row P R G α)(a:ℂ)
def replaceTest : Row P R G Unit:= { A with paint:=fun _=> a }
local notation "J"=> Row.replaceTest A a
local notation "q"=> A.lamp
local notation "φ"=> A.atom
local notation "ξ"=> A.center
local notation "X"=> Stationary.Link G n
local notation "Λ"=> Poetry.Helmet.frame φ ξ
-- invariant mark receipts across all schemes here. Don't need interpreter lifts.

def bearing (g:ℝ): ℂ:= a*Complex.ofReal (g^A.lamp.stamp*A.atom.unmasked (1:Config G n) A.center)
local notation "ℓ"=> Row.bearing A a
variable (i:ℕ)(h:A.clear)(v:Stationary.Link G n)
lemma breath : ContDiffAt ℝ ω ( Row.bearing A a ) 0:= contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((contDiffAt_id.pow _).mul contDiffAt_const))
include h
lemma vigor (g:ℝ)(V:Config G n): (J).powered () g V=(ℓ) g:= by unfold Row.bearing; change a* Complex.ofReal (_ * A.atom.unmasked V A.center)=_; rw [Row.quietU A V h]; rfl
lemma interest : Assembly.jet ( Row.bearing A a) (A.lamp.power + i) 1= a * Complex.ofReal ( A.markReceipt i v):= by
 let L:= ContinuousLinearMap.fst ℝ ℝ X; let f:ℝ×X := (1,v);
 have hb(i:ℝ×X): (J).powered () i.1 (Stationary.input G n i.2) = Row.bearing A a (L i):= vigor A a h _ _
 exact (Assembly.jet_continuous_right L ((Row.breath A a).of_le le_top) (f:ℝ×X)).symm.trans (by rw [show Row.bearing A a ∘ L= (fun i:ℝ×X => (J).powered () i.1 (Stationary.input G n i.2)) from funext (fun i=> (hb i).symm)]; exact Row.powerAudit J () i v)
variable (Q:Ratio c n)
lemma faithful (v':Stationary.Link G c) : A.markReceipt i (0:Stationary.Link G n) = ( Solo.transmit A Q).markReceipt i v' := by
 let B:= Solo.transmit A Q; have he:A.bearing 1=B.bearing 1:= by funext v; unfold Row.bearing; exact congr_arg (fun p:ℝ=> (1:ℂ)* Complex.ofReal (v^A.lamp.stamp*p)) (Solo.ghost A h _ _ _ _)
 let H:Assembly.jet ( Row.bearing A 1 ) (A.lamp.power+i) 1= Assembly.jet ( Row.bearing B 1 ) (B.lamp.power+i) 1:=by rw [he]; rfl
 rw [Row.interest A 1 i h (0:Stationary.Link G n), Row.interest B 1 i h v'] at H -- Supply v
 exact Complex.ofReal_inj.mp (mul_left_cancel₀ one_ne_zero H)
end Row
namespace ScatterR
set_option quotPrecheck false
variable (q:ι→ℂ)(w:V→ℕ)(H: ∀i∈F,(M i).lamp.toll=Launch.index R w (M i).mode)
private abbrev opaqueF := F.filter (fun i=> ¬(M i).clear)
def opening := F.filter (fun i=> (M i).clear)
local notation "P₀"=> opaqueF M F
local notation "Φ"=> opening M F
local notation "D"=> ScatterR.actor M
local notation "ν" i:max=> ScatterR.colors M i L T R (ScatterR.actor M) q w
local notation "R₀"=> (ν (P₀))
local notation "R₁"=> (ν F)
local notation "U"=> ( (P₀:Set ι) ∪ (Φ:Set ι) )
variable {c' : Side} {S:StepData c' n} {B₀:Clip} {D':PathData G}{O:ChartRatio G}
open Comparison.RG02.Bulk
variable (K:Comparison.RG02.Bulk.Kernel S B₀ D' O)(X:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c' 1)
local notation "τ"=> Bulk.Fk K X t
local notation "G0" v:max=> Bulk.markFn S X v
local notation "Φc" v:max x:max=> Assembly.affine (v).power ( G0 v ) (Bulk.geometric K X t v) x
local notation "Kᶲ"=> ſ
variable (z:Precision.Key X G→ℝ)
local notation "A"=> (Bulk.translated K X x z)
local notation "r₀" i:max=> ( (M i).lamp.power )
variable (i:ℕ)
local notation "χ"=> (0:Stationary.Link G n)
local notation "p'" i:max=> (M i)
def drawing (d:ℕ)(v:ι) := Poly.send ( (M v).mode) ( q v * Complex.ofReal ((M v).markReceipt d (0: Stationary.Link G n)))
local notation "U₁"=> ScatterR.drawing M q
lemma fruitful {v:ι}(he:(M v).clear): q v * Complex.ofReal ((M v).markReceipt i (0:Stationary.Link G n))= Assembly.jet (Bulk.posed S X (familyAt M q v)) ((M v).lamp.power+i) (Bulk.translated K X x z):= by
 let A₁:= (p' v); let l:= ContinuousLinearMap.fst ℝ ℝ (Bulk.SliceDir S X G); let g:= Row.bearing A₁ (q v); have Hb: l A=1:= congr_arg Prod.fst (footing K X x z); rw [show (posed S X (familyAt M q v))= g ∘ l from funext (fun i=> Row.vigor A₁ (q v) he _ _), Assembly.jet_continuous_right l ((Row.breath A₁ (q v)).of_le le_top), Hb]; exact (Row.interest A₁ (q v) i he χ).symm -- Row.bearing namespace
-- maybe needed.Prefix shift. boost phase equality.
open Comparison.RG02.Order
variable [Fintype V]

def axisTape : Comparison.RG02.Order.PTable R:= PowerSeries.mk (fun i=> ∑ v∈ opening M F, drawing M q i v)
local notation "F0"=> ScatterR.axisTape M F q
local notation "α₀"=> (Comparison.RG02.Order.series R k (F0))
include H
lemma imprint : (Φc (R₁) A)= (F0) + (Φc (R₀) A) := by
 ext1 i; rw [map_add,axisTape,PowerSeries.coeff_mk,wave M F L T _ _ _ _ K X t H A i,wave M (P₀) L T _ _ _ _ K X t (fun i hi=> H _ (Finset.mem_filter.mp hi).1) A i,add_left_comm];
 let f i'(h:ℕ):= Poly.send (M i').mode (Assembly.jet (Bulk.posed S X (familyAt M q i')) ((M i').lamp.power+h) (Bulk.translated K X x z)); apply congr_arg₂ (·+·); · rfl
 change ∑ v∈F,f v i= (∑ v∈opening M F,(drawing M q i v))+∑ v∈opaqueF M F,f v i -- parentheses issue
 have hp: (∑ v∈opening M F,f v i)=∑ v∈opening M F, drawing M q i v:= by apply Finset.sum_congr rfl; intro v hv; exact congr_arg (Poly.send (M v).mode) (fruitful M q K X x z i (Finset.mem_filter.mp hv|>.2)).symm
 rw [← hp]; symm; apply Finset.sum_filter_add_sum_filter_not -- name
omit H
lemma deposits : Order.denominator (Order.series R k (axisTape M F q))=0:= by
 rw [ Order.denominator, Order.bottom_map];
 let A₀:= axisTape M F q; have he:PowerSeries.map (Order.blanked R) (axisTape M F q)=0:= by
    ext1 i; apply Marker.Poly.ext; intro s; rw [PowerSeries.coeff_map,Order.pure_marks]; split;
    next h=> rw [axisTape,PowerSeries.coeff_mk, Poly.part_sum]; simp_rw [show ∀ j,(drawing M q i j).part R.quiet=0 from fun j=> part_quiet_hot ( ScatterR.actor M j) (q j * Complex.ofReal ((M j).markReceipt i χ))]; simp
    next h=> simp
 rw [he,map_zero]
include H
lemma income : Order.logMarked (Bulk.Fk K X t (ScatterR.colors M F L T R (ScatterR.actor M) q w) x k)= Order.series R k (F0) + Order.logMarked (Bulk.Fk K X t R₀ x k) := Morph.regularize K X (R₀) (R₁) t x α₀ (ScatterR.deposits M F q) (fun z=> by rw [imprint M F L T q w H, _root_.map_add]) -- arg order
omit H
variable [DecidableEq ι]
lemma email : ScatterR.lounge M ( opaqueF M F )= lounge M F := by ext1 i; simp only [ScatterR.lounge, Finset.mem_preimage, Finset.mem_powerset]; constructor; intro hi; exact Subset.trans hi (Finset.filter_subset ..); intro he j hj; exact Finset.mem_filter.mpr ⟨he hj,Club.all_masked M i j hj⟩
include H
theorem total (he:d≤k) : Order.observe R k (Order.logMarked (Bulk.Fk K X t (ScatterR.colors M F L T R (actor M) q w) x k)) d= (∑ v∈ lounge M F, ScatterR.unitTerm M L T K X t x q d k v)+(∑ i∈ opening M F, ScatterR.drawing M q d i):= by
   rw [ScatterR.income M F L T q w H K X t x,Order.observe_add, Order.observation R k F0 he, axisTape, PowerSeries.coeff_mk, ScatterR.participates M (P₀) L T K X t x q w (fun i hi=> H _ (Finset.mem_filter.mp hi).1) (fun i hi=>(Finset.mem_filter.mp hi).2) he, ScatterR.email, add_comm] -- Observe params test.
end ScatterR
end YM.QuadraticLocal.Earn
