import YM.QuadraticLocal.Fk.Climate
import YM.QuadraticLocal.Fk.Ballot
import YM.Integration.LocalFormalAction
import YM.AllOrder.Floe.Stars
/-!
# Whole `vacuumAction`, not logVac, tied to native prescription at any tree path.

Determine precursor Response & prePhase. Includes scalar density log.Price.O.Scale/n log marker.Will
caller distinguish real expression clipping from formal at X/V.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Fk.Dress
open Filter Function Finset Lattice Wilson RG Pressure RG.Supply Input Org Precision
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat Lapis
open AllOrder AllOrder.Floe AllOrder.Response Extra.Iteration Tree Blaze MeasureTheory
open Comparison.RG02 Comparison.RG02.Bulk Assembly Next.SectorChange
open Marker Extra.Trajectories Multi Push Push.Uniform Laplace Laplace.SigmaP
open PertExtension PertExtension.Series PertExtension.GaussianScore
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge} {f c:Side}{V:Type}[DecidableEq V] {J:Census V} {S:StepData c f}
local notation "X"=> Apex c G
variable (F : Forest S.ratio) (k:S.Choices) {p:Clip}{R:PathData G}{O:ChartRatio G}
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "E"=> Apex c G × Poll.Body (Precision.Key F G)
local notation "χ"=> ℝ× (Apex c G × Poll.Body (Precision.Key F G))
local notation "v"=> weld (Precision.Key F G)
local notation "w"=> tint G (Exterior.Body 1 c)
local notation "r"=> (Precision.Key F G → ℝ)
variable (M:Layout G)(A:Finset Age)
variable (h:Legal A M)
variable (C:Bulk.Kernel S p R O)
variable {a C₀ Λ:ℝ}{N:ℕ} (F' : (Bid.Dir G c) → AxisChart G F) (U : Push.Uniform.Before G a C₀ S.patch.J S.kernel (N+3)) (hT:U.Service F p R F')
variable (hG:Bid.Larger (G:=G) S)(hQ:R.Bounds p a C₀ Λ)
local notation "K"=> Laplace.startup F O k R p U hG hQ hT C.ratio
local notation "K0"=> augment F M A K h
set_option quotPrecheck false
local notation "Γ"=> Response.castle (K0).hard (K0).quiet (K0).pay.steer
local notation "C'"=> C.covariance F k
local notation "Cost"=> (Gaussian.coat (C'))
local notation "μ"=> (volume: Measure Y)
local notation "Ω₁"=> (Impulse (fderiv ℝ (K0).quiet 0) (K0).high (K0).paid)
variable (D:Bulk.Colors J G f)
local notation "R₀"=> Fk.grant M A D
local notation "U₀" x:max y:max=> Bulk.translated C F (w x) y
local notation "B₀"=> trim G F
local notation "A₀"=> Bulk.geometric C F k R₀
local notation "α"=> fderiv ℝ (K0).quiet 0
local notation "L"=> liftQ (K0).hard α
open Radial
include C in
lemma phase0 (x:X): L x= Bulk.infrared S p R F k (C.b F) (w x):=by
    let f':= Floe.slidL (G:=G) F; let u := α x; let t := f'.toContinuousLinearMap; let s:=Bulk.Surface S p R F k
    have he : (K0).hard=s ∘ t := rfl
    change Radial.jet ((K0).hard) 2 (x,u)=_; rw [he]; refine Eq.trans (Assembly.jet_continuous_right t (f:=s) (i:=2) (((C.critical F).2.2 k).1.of_le le_top) _) ?_; unfold Bulk.infrared; exact congr_arg (Assembly.jet s 2) (show ((t) (x,u))=Bulk.classical S F (C.b F) (w x) from Prod.ext rfl (Moved F k C F' U hT x).symm)
variable [Fintype V]
local notation "Θ" n=> Bulk.Fk C F k R₀ · n -- remove
lemma connected_at (x:X)(n:ℕ): Order.logVac (Bulk.Fk C F k R₀ (w x) n)= Ballot.pure J n (fun i=>distilled (K0) i x):=by
    let f i:= climate Γ μ Ω₁ i x; let z:= (K0); have hx : f 0=1:= congr_fun (toward μ («Γ»:=Γ) (win0 (token α (K0).high (K0).paid))) x
    exact Ballot.log_mono J n f _ hx (Bulk.fk_sym ..) (raw F k M A h C F' U hT hG hQ D x n)
lemma ground (x:X)(n i:ℕ)(hi:i≤n) : Symmetry.Orbit.ground C F k R₀ n i (w x)= Complex.ofReal (distilled (K0) i x - if i=0 then liftQ (K0).hard α x else 0):=by
    unfold Symmetry.Orbit.ground; rw [connected_at F k M A h C F' U hT hG hQ D]
    change ((Order.observe J n (Ballot.pure J n _) i).part _)+_= _
    rw [Ballot.seen J n _ hi, Ballot.inc_quiet, Complex.ofReal_sub]; split; rw [phase0]; rfl
    next=> simp only [Complex.ofReal_zero, sub_zero,add_zero]
lemma forecast (x:X)(n i:ℕ)(hi:i≤n) : ratePlan (K0) i x=PositionX.Jet.just (preview (K0)) i + (Symmetry.Orbit.ground C F k R₀ n i (w x)).re:=by
    rw [Dress.ground F k M A h C F' U hT hG hQ D x n i hi]
    unfold ratePlan; change (PositionX.Jet.just (_-L x) i+_)= PositionX.Jet.just _ i +(Complex.ofReal _).re; unfold PositionX.Jet.just; split; next=> rw [Complex.ofReal_re]; ring -- maybe rfl
    next=> simp
include U h hG hT hQ in
lemma tangible (x:X)(n i:ℕ)(hi:i≤n) : Complex.ofReal ((Symmetry.Orbit.ground C F k R₀ n i (w x)).re)=Symmetry.Orbit.ground C F k R₀ n i (w x):= by rw [ground F k M A h C F' U hT hG hQ D x n i hi,Complex.ofReal_re]
private lemma free_lift : L (0:X)=0:= by
   unfold Response.liftQ Laplace.curvature; rw [map_zero]; change Radial.jet _ 2 (0:E)=_; rw [Laplace.jet_two_H]; simp
lemma zeroBase : ratePlan (K0) 0 (0:X)=preview (K0):=by
   unfold ratePlan preview; let L' := Γ; have hz: climate L' μ Ω₁ 0 0=1:= congr_fun (Response.toward μ («E»:=Ω₁) (win0 _) («Γ»:=L')) 0 -- E notation issue.E macro
   have he :distilled (K0) 0 (0:X)=0:= Ballot.shift _ hz
   change preview _- liftQ _ _ _ + _=_; rw [he,free_lift (C:=C) ..]; abel -- holes
end YM.QuadraticLocal.Fk.Dress
