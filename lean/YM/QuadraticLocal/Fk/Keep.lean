import YM.QuadraticLocal.Fk.Unit
import YM.Comparison.RG02.Sources.Naming
/-! # One query on a subalphabet. Exact normalized transfer and joint component -/
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
variable {V:Type}{G:Gauge} {n c:Side} {k j e d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker Multi
open QuadraticLocal.Sunrise
variable {ι α ι₀: Type} [DecidableEq V] {P:Passport n V} {R:Census V}
variable (M:ι→ Row P R G α)
variable (L:Layout G) (T:Finset Age)
namespace ScatterR
open Comparison.RG02
section limiting
variable {V₁:Type}[DecidableEq V₁](J:Census V₁)
lemma extC (A B:Bulk.Colors J G n)(he:A.mark=B.mark)(hv:A.power=B.power)(hp:A.vac=B.vac): A=B:= by cases A; cases B; congr
end limiting
variable [DecidableEq ι][DecidableEq ι₀] [Fintype ι][Fintype ι₀](u:ι₀ ↪ ι)
local notation "Z"=> Focus.census ι
local notation "V₀"=> Focus.census ι₀
open Extra.Trajectories (Names)
open Comparison.RG02.Sources

def pouch : Names (Focus.census ι₀) (Focus.census ι):= ⟨u, fun _=>mem_univ _⟩
local notation "pu"=> (ScatterR.pouch u)
lemma keeps (P:Finset ι₀): (pu).share (Focus.onto P)=Focus.onto (P.image u):=rfl
lemma secs (P:Finset ι₀)(h:P.Nonempty): (pu).look (show Multi.Hot (Focus.census ι₀) from ⟨Focus.onto P,h⟩)= ⟨Focus.onto (P.image u),h.image u⟩:=rfl
variable (N:ι₀→Row P R G α)(hN:M ∘ u=N)
local notation "S'"=> ScatterR.edition M univ L T
local notation "q₀"=> 1
local notation "T₀"=> ScatterR.edition N univ L T
set_option quotPrecheck false
-- power desc left. Full polynomial, group with quiet marks
include hN
lemma sieve (X: (Focus.census ι₀).Mode) : Launch.index (Focus.census ι) (fun i=>(M i).lamp.toll) ((pu).share X)=Launch.index (Focus.census ι₀) (fun i=>(N i).lamp.toll) X := by subst N; unfold Launch.index Extra.Trajectories.Names.share; exact Finset.sum_image u.injective.injOn
lemma flow (U:Multi.Hot (Focus.census ι₀)): (ScatterR.edition M univ L T).mark ((pu).look U)=(ScatterR.edition N univ L T).mark U:=by
 subst N; unfold edition; rw [markEq,markEq];
 let v (i:ι):Prop:= (pu).share U.val= (Focus.detailI i).val; let s:= Finset.univ.filter fun j:ι₀=> U.val=(Focus.detailI j).val; let S:= Finset.univ.filter v
 have he(i:ι₀):((pu).share (Focus.detailI i).val)= (Focus.detailI (u i)).val:= (pu).fire _;
 have hS:s.image u=S:= by
    ext i; constructor
    · intro h; obtain ⟨z,hz,rfl⟩:= Finset.mem_image.mp h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Eq.trans (congr_arg _ (Finset.mem_filter.mp hz|>.2)) (he z)⟩
    intro h; obtain ⟨i',hi⟩:=U.prop; have hv := (show u i'∈ ((pu).share U.val).val from Finset.mem_image_of_mem _ hi); have ht:v i:= (Finset.mem_filter.mp h).2; unfold v at ht; rw [ht] at hv; have h' : i=u i':=(Finset.mem_singleton.mp hv).symm; subst i; exact Finset.mem_image.mpr ⟨i',Finset.mem_filter.mpr ⟨Finset.mem_univ _, (pu).inj (ht.trans (he i').symm)⟩,rfl⟩
 change (∑ i∈S,familyAt M 1 i)=∑ i∈s,familyAt _ _ i; rw [← hS,sum_image u.injective.injOn]; rfl
lemma shaped : Comparison.RG02.Sources.pin (pouch u) (S')= ScatterR.edition N univ L T := extC _ _ _ (funext (flow M L T u N hN)) (funext (fun v: Multi.Hot (Focus.census ι₀)=> by
 change Launch.index Z _ _+1=Launch.index V₀ _ _+1; rw [← show (pu).share v.val=((pu).look v).val from rfl]; rw [sieve M u N hN])) rfl -- target uses implicit arguments via funext binder
variable {c' : Side} {S:StepData c' n} {B₀:Clip} {D':PathData G}{O:ChartRatio G}
open Comparison.RG02.Bulk
variable (K:Comparison.RG02.Bulk.Kernel S B₀ D' O)(X:Forest S.ratio)(t:S.Choices)(x:Exterior.fieldDir G c' 1)
set_option quotPrecheck false
local notation "Z'"=> (Comparison.RG02.Bulk.Fk K X t (S') x k)
local notation "μ"=> (Comparison.RG02.Bulk.Fk K X t (T₀) x k)
open Comparison.RG02
open Extra.Trajectories (connected)
local notation "O₀" v:max z:max=> Order.observe v k z j
include hN
lemma visible (hv: j ≤ k) : (pu).restriction ( Order.observe (Focus.census ι) k (Order.logMarked (Z')) j)= Order.observe (Focus.census ι₀) k ( Order.logMarked (Bulk.Fk K X t (T₀) x k)) j:= by
 let h:=Function.Embedding.refl (Fin k); let o':=Order.truncate (pu) h;
 rw [← shaped M L T u N hN]; let U':= S'; have he : o' ( (Bulk.Fk K X t (S') x k))=Bulk.Fk K X t (pin (pu) (S')) x k:= criterion _ _ _ _ _ _ _ -- signature
 rw [← he]; have hg: (Order.logMarked (o' (Z')))=o' (Order.logMarked (Z')):= (trunc_marked (pu) h (Bulk.fk_unit ..)).symm; rw [hg]; exact Order.trunc_observe (pu) h (Order.sym_logMarked (Bulk.fk_unit ..) (Bulk.fk_sym ..)) hv
-- `(F.image u → grants)` version
lemma transfer_part (P: Finset ι₀)(hv: j≤k) : ( Order.observe (Focus.census ι) k (Order.logMarked (Z')) j).part (Focus.onto (P.image u)) = ( Order.observe (Focus.census ι₀) k ( Order.logMarked (Bulk.Fk K X t (ScatterR.edition N univ L T) x k)) j).part (Focus.onto P):= by rw [← visible M L T u N hN K X t x hv]; rfl
end ScatterR
end YM.QuadraticLocal.Earn
