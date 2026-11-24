import YM.QuadraticLocal.Fk.Airport
import YM.Comparison.RG02.Integral.Model
/-!
# Countable analytic packets are true native Wilson Step Colors

Uses `function.support`-independent hypotheses. The expenditure `Air.Staff`
from actual supplied exponential widths may depend on the stage and publication;
not assuming Well in building Fk. Bounded marks on the true gauge integral at each
real parameter (before taking canonical relative-value continuation.Owner.Current.Penna).
Not changing power accounting issue: lift by tall g then restore those powers.

Assembly of all rows and hermetic startup k.Scope still separate.
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
namespace Air
variable (q:ι→ℂ)(w:V→ℕ)(U:Staff M q w a k)
variable (L:Layout G)(T:Finset Age)
set_option quotPrecheck false
open Comparison.RG02 Comparison.RG02.Bulk
local notation "Yₐ"=> Launch.index R w
local notation "Ptv" i:max=> ScatterR.actor M i
local notation "τ" p:max=> (fun i:ι=> Subtype.val p = (ScatterR.actor M i).val)
def craft : Bulk.Colors R G n:= Fk.grant L T {vac:=0,mark r:= Air.sums M q (fun i:ι=> ( ScatterR.actor M i).val=r.val),power r:= (Launch.index R w r.val)+1 }
local notation "R₀"=> Air.craft M q w L T
local notation "μ" t:max=> (fun i:ι=> (ScatterR.actor M i).val=Subtype.val t)
local notation "H₁" t:max i:max=> (( ScatterR.actor M i).val=Subtype.val t)
variable (y:Multi.Hot R)
local notation "X"=> ℝ × Exterior.fieldDir G n 1
include U
lemma grade : Assembly.GradeAt ((R₀).power y) (projected ((R₀).mark y)):= by
 let f:= (R₀).mark y; let p:= μ y; let H j (v:Fin j→ X):= Air.rings M q w U p Prod.fst ( (Precision.represent (G:=G) (n:=n)) ∘ Prod.snd) (0:X) (contDiffAt_fst) (fun i=> (Work.F03.represent_smooth i).contDiffAt.comp (f:= Prod.snd) 0 contDiffAt_snd) j v
 refine ⟨(H 0 0).1,?_⟩; intro j hj; ext1 z; let T':= Multi.Hot R;
 let f i (t:X):= if p i then ScatterR.familyAt M q i t.1 (represent t.2) else 0; have he (i:ι) : iteratedFDeriv ℝ j (f i) 0 z=0:= by
    unfold f; by_cases h:p i
    · simp_rw [if_pos h]; have hV : (M i).lamp.power=(R₀).power y:= congr_arg (·+1) ((U.written i).trans (congr_arg ( Launch.index R w ) h)); exact congr_arg (fun (k:ContinuousMultilinearMap ℝ (fun _ : Fin j=> X) ℂ)=> k z) (( ScatterR.mature M q i ).vanish j (hV ▸ hj))
    simp_rw [if_neg h]; simp
 change (iteratedFDeriv ℝ j _ _ z)=0; let hz:= H j z|>.2; apply HasSum.unique hz _; exact hasSum_zero.congr_fun (fun i=> by convert he i using 3; by_cases h:p i <;> simp [f,h,Function.comp_def])
lemma standard (he:Legal T L) : (Air.craft M q w L T).Standard:= by
 refine Fk.standard L T he _ (fun i=> Air.grade M q w U L T i) (?_) (?_) -- check arity D?
 · intro i g v x; unfold sums; apply tsum_congr; intro i; split; next h=> exact congr_arg (fun z:ℝ=> q i* Complex.ofReal z) (Loan.natural _ _ _ _ ((M i).lawful) v x)
   next h=> rfl
 intro i g; have hp:= Air.continuous M q w U g (μ i); obtain ⟨C0,hx⟩:= isCompact_univ.exists_bound_of_continuousOn hp.continuousOn; exact ⟨hp.measurable,C0,fun z=> hx z (Set.mem_univ _)⟩ -- arguments.continuous order v i
variable {c' : Side} {S:StepData c' n}
variable (X':Forest S.ratio)
local notation "E"=> (Bulk.Joint (G:=G) S X')
variable (F:Finset ι)
local notation "W" i:max=> ScatterR.colors M i L T R (ScatterR.actor M) q w
local notation "Ξ" v:max=> ( Bulk.markFn S X' v y )

variable (j:ℕ)(x:Fin j→Bulk.Joint (G:=G) S X')
local notation "Ω" i:max=> Bulk.posed S X' (ScatterR.familyAt M q i)
local notation "f₀" i:max=> (if ( H₁ y i) then iteratedFDeriv ℝ j (Ω i) 0 x else 0)

lemma convergence : Tendsto (fun F:Finset ι=> iteratedFDeriv ℝ j (Bulk.markFn S X' ( ScatterR.colors M F L T R (ScatterR.actor M) q w) y) 0 x) atTop (𝓝 ( iteratedFDeriv ℝ j (Bulk.markFn S X' (Air.craft M q w L T) y) 0 x)) := by
 let p:= μ y
 let h(j'): ContDiffAt ℝ ω ( Bulk.posed S X' (ScatterR.familyAt M q j')) 0:= (Bulk.joint_receipt S X' ( ScatterR.mature M q j')).smooth; let u(j):= Ω j; let g(j)(z:E):= if p j then (u j z) else 0; let z j':= if p j' then iteratedFDeriv ℝ j (u j') 0 x else 0;
 have Hp (i:ι) : iteratedFDeriv ℝ j (g i) 0 x=z i:= by by_cases h:p i; simp_rw [z,g,if_pos h]; simp_rw [z,g,if_neg h]; simp -- syntax
 have he : HasSum z (iteratedFDeriv ℝ j ( Ξ (R₀) ) 0 x):= (( Air.rings M q w U p Prod.fst ((Work.F03.live (G:=G) X') ∘ Prod.snd) (0:E) (contDiffAt_fst) (fun i=> by
    change ContDiffAt ℝ ω ((fun x:Bulk.SliceDir S X' G => G.mat (Work.F03.live X' x i)) ∘ Prod.snd) (0:E); apply ContDiffAt.comp; exact Work.F03.live_smooth X' i; exact contDiffAt_snd) j x).2).congr_fun (fun i=> by convert (Hp i).symm using 3; by_cases h:p i <;> simp [g,h,u,posed, Function.comp_def])
 have hg (F: Finset ι) : Ξ (W F)= ∑ i∈F.filter p,u i:= by ext1 x; unfold markFn posed; rw [ScatterR.markEq]; simp_rw [Finset.sum_apply]; simp_rw [Finset.sum_filter]; refine Finset.sum_congr rfl (fun i _=>?_); unfold p; simp only [eq_comm (a:= y.val)]; rfl
 apply he.congr' (Eventually.of_forall fun F=>?_); rw [hg,iteratedFDeriv_sum_apply (fun i _=> (h i).of_le le_top),_root_.sum_apply]; change ∑ i∈F,z i=_; rw [Finset.sum_filter] -- `HasSum` reducible?
end Air
end YM.QuadraticLocal.Earn
