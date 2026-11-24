import YM.FVA2.Speed.Ports
import YM.FVA2.XReg.Continuum
/-!
# Real near-scheme comparison *after* position layout

Eventual availability of the solve is crucial; use `Reg.Pivot.Ready`.
Continue at **every** positive order, not estimating D but using `coast`
and `timely`. See `Speed/Distill` for final estimates through the coupling change.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Speed.Cake
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries
open Normalize.Fray Reg Reg.Pivot Reg.Point Reg.Unique CoverTest Photo Higher State
open scoped Topology ContDiff BigOperators Classical
open Speed.Star Asymptotics Finset
variable {n d k:ℕ}{G:Gauge}
variable (ν:ℝ)(Y:Initialize G)(V:Normalize.Store G)(S:Prescription (Press.portDeck G)){O: Booked (Press.portDeck G)}(T: MS_Data G O) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)
include h hs
lemma coast : FFrame Front id (fun i=> Reg.Pivot.chalk ν Y V S d i) (State.root ν V T d):= controller frontier _ _ _ _ (freeT ν T) (pens ν Y T S h hs)
lemma orders : Resin Front id (fun i=> Pivot.coupledBatch ν Y V S d i) (fun _=> State.author ν V T d):= satisfies frontier _ _ ( coast ν Y V S T h hs ) _ _ (pens ν Y T S h hs)
variable (hr:Position.Favors.Horder S)(hv:Position.Ace.UnitP S)
include hr hv
lemma entitle : Resin Front id (fun i=> substitute ( reset ν S i ) (V.opens Y i d)) (fun _=> State.author ν V T d) := by intro k n t p; apply ( orders (d:=d) ν Y V S T h hs k n t p ).tee _ (.refl ..); filter_upwards [timely ν Y V S ( d:=d ) T h hs hr hv frontier] with i hi; rw [rulers ν Y V S i hi]
variable {K:Set (Points n)}(hc:IsCompact K)(hk:K⊆ conf n)
include hc hk
local notation "A"=> XSpace.Cirrus.Sample
local notation "κ"=> Pose K
omit hr hv in
lemma gaunt : NPoints (Pose K) grab (fun i: Sample n=>coupledPoints ν Y V S i d) (fun i:Sample n=> wall ν V T d (familiar i)):= by
    let f := grab (n:=n); exact Speed.paints ( F:=κ ) (travels K) (fun i=> Pivot.chalk ν Y V S d ( f i )) _ ( fun k=> Fast.comp f ( grows K ) ( coast ν Y V S T h hs k )) (fun i=> postedPoint ν Y S d i) (fun i=> meteor ν T d ( familiar i )) (fun k p=> Star.sharp ν Y T S h hs p hc hk k)
lemma feature : NPoints (Pose K) grab (fun i:Sample n=> substitute (reset ν S i.F) (Rose.cooked Y V d i)) (fun i: Sample n=> wall ν V T d (familiar i)):= by
    intro k p; apply (gaunt ν Y V S T h hs hc hk k p).tee _ (.refl ..); filter_upwards [(grows K).eventually (timely (d:=d) ν Y V S T h hs hr hv frontier)] with i hi; rw [ Pivot.whole ν Y V S _ hi ]
omit h hs hr hv hc hk
lemma wall_s (p:Tags G d n) (k:ℕ)(x:Points n)(h:x∈conf n): ContDiffAt ℝ ∞ (fun x=> wall ν V T d x k p) x:= by simp_rw [wall,seen]; exact ContDiffAt.sum (fun i hi=> Star.smooth_r ν T _ _ x h)
include h hs hr hv hc hk
lemma billed (k:ℕ)(p:Tags G d n): Labor K (fun i t=> substitute ( reset ν S i ) ( V.opens Y i d ) k n t p) (fun t=> State.author ν V T d k n t p) := by
    let f(a:Sample n):= substitute ( reset ν S a.F ) ( Rose.cooked Y V d a ) k p; let W(x:Points n):= wall ν V T d x k p; have he:= Speed.ahead ( f:=f ) ( Y:= W ) ( cartel.mpr (( feature ν Y V S T h hs hr hv hc hk k p ).sails) ) hc hk ( wall_s ν V T p k ) ( fun _ _ _=> rfl );
    have h (i:Mesh)(t:Test n): Deposit i f t=substitute ( reset ν S i ) ( V.opens Y i d ) k n t p:= ( CoverTest.sense i (fun i=>V.opens Y i d) (fun i=>Rose.cooked Y V d i) p ( fun i=> reset ν S i ) t ( fun k p=> (Rose.smeared ..).symm ) ).symm; -- implicit expects V etc
    simp only [ ← h, Reg.State.exact_trace ]; exact he
end YM.FVA2.Speed.Cake
