import YM.FVA2.Speed.Firm
import YM.FVA2.Smooth.Point
import YM.FVA2.XReg.Sum
/-!
# At the D-posted stage: strengthen to uniform powers on compact tests

For each fixed compact subset of separated configurations prove `Star.sharp`
(the compact-uniform point estimate) and `Star.scope` (`Labor`, including
test-budgeted smearing), for the posted Wilson point array vs the MS result.
This part is before any real layout solve or coupling calibration. But already
with the D field change at finite mesh, an important prerequisite for the
position-normalization proof. Keep continuum smoothness at those configurations.
See `Smooth` about getting that at all perturbative orders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Speed.Star
open XSpace XSpace.Expense XSpace.Cirrus XSpace.TestBudget MS MS.Tide Lattice
open MS.Tone MS.Book MS.Book.Convolve MS.Fleet MS.Menus MS.Wind MS.Land MS.Theater MS.Rake MS.Dial
open XSpace.Normalize XSpace.Normalize.Fray XSpace.Structure1 Position Position.Axes Arrival Dframe
open Asymptotics Set Function Metric Filter MeasureTheory Real
open Reg Reg.Pivot Reg.CoverTest
open scoped Topology BigOperators ContDiff Classical
variable {I:Type*} {n d k:ℕ} {G:Gauge}{K:Set (Points n)}(ν:ℝ)(Y:Initialize G) {O: Land.Booked (Press.portDeck G)} (P: MS_Data G O) (S: Land.Prescription (Press.portDeck G))
variable (h:G.Simple)(hs:TaylorOKF P (Press.wickInput Y) S)
open Arrival.Schedule
-- explicits ContDiff.P.Points alg.
lemma plotSmooth : ContDiff ℝ ∞ (plot (n:=n)):= by
    apply contDiff_pi.mpr; intro i; exact Theater.out.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp ( PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin n=> E4) i ).contDiff
lemma moondye_r (p:Fin n→Label (Press.portDeck G))(t:Finset (Fin n))(k:ℕ)(x:Points n)(hc:x∈conf n): ContDiffAt ℝ ∞ (Landing.moondye ν P p t k) x:= (Smooth.Cruise.passes P p ν _ (track hc) _ _).comp x plotSmooth.contDiffAt
variable (p: Tags G d n)
local notation "U"=> postedPoint
lemma smooth_r (k:ℕ)(x:Points n)(hc:x∈conf n): ContDiffAt ℝ ∞ (fun x=> meteor ν P d x k p) x:= by simp_rw [stencil_he ( meteor ν P d _ _ ) p,ribbon]; exact ContDiffAt.sum ( fun i hi=> (moondye_r ν P ( flash ∘ i ) _ _ x hc ).const_smul ( 𝕜:=ℝ ) (each i p) ) -- field `const_smul` applies ℂ? annotation ν
variable (hK:IsCompact K)(hk:K⊆ conf n)
include h hs hK hk
lemma sharp (k:ℕ): Sharp (Pose K) grab (fun i=> postedPoint ν Y S d i k p) (fun i=> meteor ν P d ( familiar i ) k p):= by
    apply Sharp.of_bounds ( Y:=fun x=> meteor ν P d x k p ) K hK ( (Each K).mono fun i hi=> hi.2 ) ( ( CoverTest.measurable ν P k p ).mono hk ); unfold comp; simp_rw [ stencil_he (postedPoint ν Y S d _ _) p, stencil_he ( meteor ν P d _ _ ) p,ribbon, Dframe.reads ]; refine Fast.sum _ _ _ fun i hi=> Fast.scalar ( cartel.mp (show Strength K _ _ from ( Landing.adj_uniform ν Y P S _ _ _ h hs K hK hk ).points ) ) _ -- infer f ℂ.Chk
lemma scope (k:ℕ): Labor K (fun i t=> posted ν Y S d i k n t p) (fun t=> Rates ν P d k n t p):= by simp_rw [ Reg.CoverTest.price_m _ ν Y S _ k p,Rates]; exact ahead ( cartel.mpr ( sharp ν Y P S h hs p hK hk k |>.sails ) ) hK hk ( smooth_r ν P p k ) ( Reg.CoverTest.regular ν Y S p k ) -- k conflict implicit ahead binder
omit hK hk
open Maxwell Maxwell.Free
abbrev Bills {I:Type*}(l:Filter I)(τ:I→ Mesh)(p:I→ Normalize.Prediction G d)(q:I→Prediction G d):=∀ (n:ℕ)(t:Test n)(v:Tags G d n), Sharp l τ (fun i=> p i n t v) (fun i=> q i n t v)
abbrev Resin {I:Type*}(l:Filter I)(τ:I→Mesh)(f:I→Reports G d)(g:I→Reports G d):=∀ n, Bills l τ (fun i=>f i n) (fun i=>g i n)
lemma pens : Resin Front id (posted ν Y S d) (fun _=> Rates ν P d):= by
    intro k n t v; exact Sharp.above (( scope ν Y P S h hs v t.hasCompactSupport t.tsupport_subset k ).single t (Subset.refl _))
end YM.FVA2.Speed.Star
