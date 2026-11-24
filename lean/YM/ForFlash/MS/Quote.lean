import YM.ForFlash.MS.Layout
import YM.FVA2.Speed.Faith

/-! Scale.Measure.start price (through its `Faith.rate` incarnation).
Adapted from Speed/Cells, Hearth, Faith on the Mesh payment `Layout`
and hence with polynomial diameter allowed. No resizing the spacing
late enough for a new compact profile. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.FVA2.Speed
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
variable (p:Tags G d n){I:Type}{l:Filter I}{s:I→Sample n}
local notation "θ"=> Reg.Choice.choice ν K T
local notation "χ"=> Reg.Token.conversion ν K T
open Rose
structure WideForFlash (l:Filter I)(s:I→Sample n) : Prop where
    clock : Stretched l (grab∘s)
    fit : ∃ (c C:ℝ)(m:ℕ), 0<c ∧ 0≤C ∧ ∀ᶠ i in l, Schedule.FitsWidthForFlash c C m (s i)
variable (L:WideForFlash l s)
local notation "F"=> (grab∘s)
include h hs L

private lemma layout_s : Sharp l F (fun i=> postedPoint ν Y S d (s i) k p) (fun i=> meteor ν T d (familiar (s i)) k p):=by
    obtain ⟨c,C,m,hc,hC,hA⟩:= L.fit
    simp_rw [ stencil_he (postedPoint ν Y S d _ _) p, stencil_he ( meteor ν T d _ _ ) p,ribbon,Dframe.reads]
    refine Sharp.sum _ _ _ fun j _=>?_
    exact Sharp.scalar (Schedule.sharpForFlash ν hC hc L.clock Y (flash ∘ j) T S h hs hA Finset.univ k) _ -- flash ambiguous
include hr hv

private lemma selected : NPoints l F (fun i=> substitute (reset ν S (F i)) (Rose.cooked Y V d (s i))) (fun i=> wall ν V T d (familiar (s i))) :=by
    have hp:NPoints l F (fun i=>coupledPoints ν Y V S (s i) d) (fun i=> wall ν V T d (familiar (s i))):=
        paints («F»:=l) L.clock (fun i=>Pivot.chalk ν Y V S d (F i)) _ (fun k=>Fast.comp F (goesFront L.clock) ( Cake.coast ν Y V S T h hs k )) (fun i=>postedPoint ν Y S d (s i)) (fun i=>meteor ν T d (familiar (s i))) fun k p=>layout_s ν Y S T h hs p L
    intro k x; refine (hp k x).tee ?_ (.refl ..); filter_upwards [(goesFront L.clock).eventually (timely (d:=d) ν Y V S T h hs hr hv frontier)] with i hi; rw [ show (F i)= (s i).F from rfl ]; rw [ Pivot.whole ν Y V S (s i) hi ]

lemma paymentForFlash : Sharp l F (fun i=> Rose.measureₓ Y K d (s i) k p ) (fun i=> Reg.Faith.rate ν K T d (familiar (s i)) k p):=by
    let P(i:I):= Point.story (measureₓ Y K d (s i)) p; let M(i:I):= Reg.Faith.Touch ν K T (familiar (s i)) p; let Q(i:I):= prospects ν Y K S (s i).F; have ht:= hearty ν Y K S T h hs hr hv
    have he(x:Points n): (Reg.Faith.Touch ν K T x p).subst θ=Point.story (State.wall ν V T d x) p:= by unfold Reg.Faith.Touch; rw [rate_era ν Y K S T h hs hr hv,moves _ _ ht.cost.own,subst_comp_subst_apply ( licence χ ht.cost.own ) ( licence θ (proper ν K T)),ht.cost.left, X_subst]
    have hw : Clock.Sure l F (fun i=> (P i).subst (Q i)) (fun i=> (M i).subst θ):= by
       let Z (i:I):= Point.story (substitute ( reset ν S (s i).F ) ( Rose.cooked Y V d (s i) )) p; have hh:Clock.Sure l F Z (fun i=> Point.story ( State.wall ν V T d (familiar (s i)) ) p):= by intro k; simp_rw [ Z,Point.story,coeff_mk ]; exact selected ν Y S T h hs hr hv L k p
       refine hh.tee ?_ ( Eventually.of_forall (fun i=> ( he (familiar (s i)) ).symm ) ); filter_upwards [( goesFront L.clock ).eventually ( usable Y K h ) ] with i hi; unfold Z P Q; rw [ moves _ _ (share ..), recompose ν Y K S (s i) p hi ]
    have hp: Sharp l F (fun i=> coeff k (P i)) (fun i=> coeff k (M i)):= Clock.Sure.reverse L.clock θ ( proper ν K T ) ( by rw [ stance ν Y K S T h hs hr hv ]; exact one_ne_zero ) ( fun k=> Sharp.once (w:=F) (goesFront L.clock) ( Clock.Detected.clocked ν Y K S T h hs hr hv k ) ) ( Eventually.of_forall (fun i=> g0 ν Y K S _) ) hw k
    simpa only [ Reg.Faith.Touch,M,P,Point.story,coeff_mk ] using hp

end YM.FVA2.Speed
end
