import YM.FVA2.Notch.Card
/-!
 # Beyond fitted center. Final comparable arrays, with the one regulated
 position prescription staying fixed (so performing at other centers WITHOUT
 choosing another convention for readings at those stages).
 `Pose`/Front previously used cube choices only; costs now retain their power
 even after this more general allowance. Proof uses true exact D frame equality
 `Pivot.whole` from the finite regulator position normalization (keep the qualifications as in
 `Main.Match.cancelsBare`). Thus no multiplying the estimate
 by a matrix of unestimated cost. Points always at same regulator choices.
 See `Speed.{Hearth,Distill,Faith}`; uses same argument after the `Frame`
 estimates have been established. This completes and extends pre-position quantities
 with all profiles as well (including one-time choices of center shape beyond initial
 calibration patch for point interpretation).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Notch.Pitch
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet MS.Koszul
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries
open Normalize.Fray Reg Reg.Pivot Reg.Point Reg.Unique CoverTest Photo Higher State Reg.Choice
open scoped Topology ContDiff BigOperators Classical
open Speed Speed.Star Asymptotics Finset Speed.Clock Speed.Timeframe Arrival.Episodic
open FVA2.Scale.Measure FVA2.Scale.System FVA2.Scale.Facets Speed.Cake Reg.Token Reg.Faith Rose
variable {n d k:ℕ}{G:Gauge}{O: MS.Land.Booked (Press.portDeck G)}
variable (ν:ℝ)(Y:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(S:Prescription (Press.portDeck G))
variable (T: MS_Data G O) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)
variable (ht:Position.Favors.Horder S)(hv:Position.Ace.UnitP S)
variable (r:ℝ){U:Set (Points n)}(hc:IsCompact U)(hp:U⊆ conf n)(hr:0<r)
variable (p:Tags G d n)
local notation "κ"=> Notch.Pitch.frame r U
include h hs hc hp hr
lemma stamped (k:ℕ): Sharp (Notch.Pitch.frame r U) grab (fun i=> postedPoint ν Y S d i k p) (fun i=> meteor ν T d ( familiar i ) k p):= by
    apply Sharp.of_bounds ( Y:=fun x=> meteor ν T d x k p ) U hc ( ( Notch.Pitch.room r U ).mono fun i hi=> hi.2 ) ( ( CoverTest.measurable ν T k p ).mono hp ); unfold comp; simp_rw [ stencil_he (postedPoint ν Y S d _ _) p, stencil_he ( meteor ν T d _ _ ) p,ribbon, Dframe.reads ]; refine Fast.sum _ _ _ fun i hi=> Fast.scalar ( Notch.Pitch.one _ _ _ _ _ _ _ h hs hc hp hr ) _ -- order check
include ht hv
lemma frame_price : NPoints (Notch.Pitch.frame r U) grab (fun i:Sample n=> substitute (reset ν S i.F) (Rose.cooked Y V d i)) (fun i: Sample n=> wall ν V T d (familiar i)):= by
    intro k p; let f:= grab (n:=n); obtain H: NPoints κ grab (fun i: Sample n=>coupledPoints ν Y V S i d) (fun i:Sample n=> wall ν V T d (familiar i)):= Speed.paints ( F:=κ ) ( stretches .. ) (fun i=> Pivot.chalk ν Y V S d ( f i )) _ ( fun k=> Fast.comp f ( Notch.Pitch.timely r U ) ( coast ν Y V S T h hs k )) (fun i=> postedPoint ν Y S d i) (fun i=> meteor ν T d ( familiar i )) (fun k p=> stamped ν Y S T h hs r hc hp hr p k)
    apply (H k p).tee _ (.refl ..); filter_upwards [( Notch.Pitch.timely r U ).eventually ( Reg.Pivot.timely (d:=d) ν Y V S T h hs ht hv frontier ) ] with i hi; rw [ Pivot.whole ν Y V S _ hi ]
local notation "θ"=> Reg.Choice.choice ν K T
local notation "χ"=> Reg.Token.conversion ν K T
lemma phase (k:ℕ): Sharp (Notch.Pitch.frame r U) grab (fun i:Sample n=> Rose.measureₓ Y K d i k p ) (fun i:Sample n=> Reg.Faith.rate ν K T d (familiar i) k p):= by
    let P(i:Sample n):= Point.story (measureₓ Y K d i) p; let M(i:Sample n):= Reg.Faith.Touch ν K T (familiar i) p; let Q(i:Sample n):= prospects ν Y K S i.F; have ho:= hearty ν Y K S T h hs ht hv;
    have he(x:Points n): (Reg.Faith.Touch ν K T x p).subst θ=Point.story (State.wall ν V T d x) p:= by unfold Reg.Faith.Touch; rw [rate_era ν Y K S T h hs ht hv,moves _ _ ho.cost.own,subst_comp_subst_apply ( licence χ ho.cost.own ) ( licence θ (proper ν K T)),ho.cost.left, X_subst];
    have hw : Speed.Clock.Sure κ grab (fun i=> (P i).subst (Q i)) (fun i=> (M i).subst θ):= by
       let Z (i:Sample n):= Point.story (substitute ( reset ν S i.F ) ( Rose.cooked Y V d i )) p; have hh:Speed.Clock.Sure κ grab Z (fun i=> Point.story ( State.wall ν V T d (familiar i) ) p):= by intro k; simp_rw [ Z,Point.story,coeff_mk ]; exact frame_price ν Y S T h hs ht hv r hc hp hr k p
       refine hh.tee ?_ ( Eventually.of_forall (fun i=> ( he (familiar i) ).symm ) ); filter_upwards [( Notch.Pitch.timely r U ).eventually ( usable Y K h ) ] with i hi; unfold Z P Q; rw [ moves _ _ (share ..), recompose ν Y K S i p hi ]
    have hp: Sharp κ grab (fun i=> coeff k (P i)) (fun i=> coeff k (M i)):= Speed.Clock.Sure.reverse (stretches ..) θ ( proper ν K T ) ( by rw [ stance ν Y K S T h hs ht hv ]; exact one_ne_zero ) ( fun k=> Sharp.once (w:=grab) ( Notch.Pitch.timely r U ) ( Speed.Clock.Detected.clocked ν Y K S T h hs ht hv k ) ) ( Eventually.of_forall (fun i=> g0 ν Y K S _) ) hw k
    simpa only [ Reg.Faith.Touch,M,P,Point.story,coeff_mk ] using hp
-- require specific T plot when reading outlook. (in `pose`).
omit h hs ht hv hc hp hr
variable (B: MS_Data G (Position.OpenAxis.Plot ( Press.portDeck G )))
lemma pose (H:TaylorOKF B (Press.wickInput Y) S) (g:G.Simple)(Gz:Position.Favors.Horder S)(FP:Position.Ace.UnitP S)(k:ℕ)(hu:IsCompact U)(hh:U⊆ conf n)(hr:0<r): Fast (Notch.Pitch.frame r U) grab (fun x=> forms_t Y K x d k p ) (fun x=> MeasureAt ν Y K B ( familiar x ) d k p):= by
 simp_rw [forms_t,MeasureAt,Dframe.seen ( FVA2.Scale.Measure.adjust Y K d ) ]; exact Fast.sum _ _ _ (fun i _=> ( Notch.Pitch.phase ν Y K S B g H Gz FP r hu hh hr ( pulseU i ( FVA2.Scale.Measure.adjust Y K d ) p ) _ ).sails)
end YM.FVA2.Notch.Pitch
