import YM.FVA2.Speed.Poll
/-!
# Position-frame comparison after re-expression: power costs on compact supports

At this stage after coupling calibration and inverse-substitution.
No claim about using the **bare** D matrix to take a limit. For the proof see
especially `Timeframe.payment` & `cash`. We keep the C∞ assertion on the (continuum)
`Reg.Faith.rate` at each order, and use strength on the points to extend
uniformly to C1 test budgets in `tested`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Speed.Timeframe
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries
open Normalize.Fray Reg Reg.Pivot Reg.Point Reg.Unique CoverTest Photo Higher State Reg.Choice
open scoped Topology ContDiff BigOperators Classical
open Speed.Star Asymptotics Finset Clock Detected Reg.Token Reg.Faith
variable {n d k:ℕ}{G:Gauge}
variable (ν:ℝ)(Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(S:Prescription (Press.portDeck G)){O: Booked (Press.portDeck G)}(T: MS_Data G O) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)
variable (hr:Position.Favors.Horder S)(hv:Position.Ace.UnitP S)
variable (p:Tags G d n){U:Set (Points n)}
-- `rate.Res.Target` independent mesh.PowerCosts.Any shape budget. need ambient MS faith.
local notation "θ"=> Reg.Choice.choice ν K T
local notation "χ"=> Reg.Token.conversion ν K T
local notation "κ"=> Pose U
open Rose
include h hs hr hv
lemma payment (hc:IsCompact U)(hx:U ⊆ conf n): Sharp (Pose U) grab (fun i:Sample n=> Rose.measureₓ Y K d i k p ) (fun i:Sample n=> Reg.Faith.rate ν K T d (familiar i) k p):= by
    let P(i:Sample n):= Point.story (measureₓ Y K d i) p; let M(i:Sample n):= Reg.Faith.Touch ν K T (familiar i) p; let Q(i:Sample n):= prospects ν Y K S i.F; have ht:= hearty ν Y K S T h hs hr hv;
    have he(x:Points n): (Reg.Faith.Touch ν K T x p).subst θ=Point.story (State.wall ν V T d x) p:= by unfold Reg.Faith.Touch; rw [rate_era ν Y K S T h hs hr hv,moves _ _ ht.cost.own,subst_comp_subst_apply ( licence χ ht.cost.own ) ( licence θ (proper ν K T)),ht.cost.left, X_subst];
    have hw : Clock.Sure κ grab (fun i=> (P i).subst (Q i)) (fun i=> (M i).subst θ):= by
       let Z (i:Sample n):= Point.story (substitute ( reset ν S i.F ) ( Rose.cooked Y V d i )) p; have hh:Clock.Sure κ grab Z (fun i=> Point.story ( State.wall ν V T d (familiar i) ) p):= by intro k; simp_rw [ Z,Point.story,coeff_mk ]; exact Cake.feature ν Y V S T h hs hr hv hc hx k p
       refine hh.tee ?_ ( Eventually.of_forall (fun i=> ( he (familiar i) ).symm ) ); filter_upwards [( grows U ).eventually ( usable Y K h ) ] with i hi; unfold Z P Q; rw [ moves _ _ (share ..), recompose ν Y K S i p hi ]
    have hp: Sharp κ grab (fun i=> coeff k (P i)) (fun i=> coeff k (M i)):= Clock.Sure.reverse (travels U) θ ( proper ν K T ) ( by rw [ stance ν Y K S T h hs hr hv ]; exact one_ne_zero ) ( fun k=> Sharp.once (w:=grab) (grows U) ( Clock.Detected.clocked ν Y K S T h hs hr hv k ) ) ( Eventually.of_forall (fun i=> g0 ν Y K S _) ) hw k
    simpa only [ Reg.Faith.Touch,M,P,Point.story,coeff_mk ] using hp
omit h hs hr hv
-- `rate_s` from hard atmosphere even without reporting.A;
lemma cash (x:Points n)(hx:x∈conf n)(k:ℕ): ContDiffAt ℝ ∞ (fun x=> Reg.Faith.rate ν K T d x k p) x:= by
    unfold Reg.Faith.rate; simp_rw [ Dframe.seen, Dframe.translate,rules ]; exact ContDiffAt.sum fun i hi=> ContDiffAt.sum fun j _=> ( Star.smooth_r _ T _ j x hx ).const_smul _
include h hs hr hv
lemma poet (hc:IsCompact U)(hx:U⊆ conf n)(k:ℕ): Strength U (fun i:Sample n=> Rose.measureₓ Y K d i k p ) (fun x=> Reg.Faith.rate ν K T d x k p ):= cartel.mpr ( payment ν Y K S T h hs hr hv p hc hx ).sails
lemma tested (hc:IsCompact U)(hx:U⊆ conf n)(k:ℕ): Labor U (fun i t=> Rose.proposed Y K i d k n t p) (fun t=> Reg.Faith.reports ν K T d k n t p):= by
    simp_rw [ Rose.represents, Reg.Faith.report_price ν Y K S T p h hs hr hv ]; exact Speed.ahead ( poet ν Y K S T h hs hr hv p hc hx k ) hc hx (fun t hx=> cash ν K T p t hx k) (fun _ _ _=> rfl)
end YM.FVA2.Speed.Timeframe
