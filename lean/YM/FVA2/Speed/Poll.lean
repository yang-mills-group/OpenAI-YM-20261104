import YM.FVA2.Speed.Hearth
import YM.FVA2.XReg.Faith
/-!
# Coupling calibration at ALL orders

Keep `Sure`, an order-by-order assertion, through the calibrated
coupling test (and under reversing the substitution with this coupling).
See `Speed/Distill` for the use. This is the **same** detector (`b3` on
horizon 6) at all stages.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Speed.Clock
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival Dframe Expense
open MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors MS.Theater PowerSeries Rose
open Normalize.Fray Reg Reg.Pivot Reg.Point Reg.Unique CoverTest Photo Higher State Reg.Choice
open scoped Topology ContDiff BigOperators Classical
open Speed.Star Asymptotics Finset
variable {n d k:ℕ}{G:Gauge} {I E:Type*}{l:Filter I}{τ:I→Mesh}
local notation "Φ"=> PowerSeries ℂ
abbrev Sure (l:Filter I)(τ:I→Mesh)(x y:I→Φ): Prop:= ∀ k, Sharp l τ (fun i=> coeff k (x i)) (fun i=> coeff k (y i))
local notation "W"=> Sure l τ
namespace Sure
variable {x y z v:I→Φ}
lemma add (hf: Sure l τ x y)(hg: Sure l τ z v): Sure l τ (x+z) (y+v):= by intro i; simp_rw [Pi.add_apply,map_add]; exact (hf i).add (hg i)
lemma sub (hf: Sure l τ x y)(hg: Sure l τ z v): Sure l τ (x-z) (y-v):= by intro i; simp_rw [Pi.sub_apply,map_sub]; exact (hf i).sub (hg i)
lemma unit (l: Filter I)(τ:I→Mesh)(x:Φ): Sure l τ (fun _=>x) (fun _=>x):= fun _=> Sharp.joy ..
lemma tee (hf: Sure l τ x y)(hg:x=ᶠ[l] z)(ht:y=ᶠ[l] v): Sure l τ z v:= fun i=> (hf i ).tee ( hg.fun_comp (coeff i) ) (ht.fun_comp (coeff i))
lemma scalar (σ:ℂ)(hf: Sure l τ x y): W ( σ • x ) (σ • y):= by intro i; simp_rw [Pi.smul_apply,map_smul]; exact (hf i).scalar σ
variable (h:Stretched l τ)
include h
lemma mul (hf: Sure l τ x y)(hg: Sure l τ z v): Sure l τ (x*z) (y*v):= by intro i; simp_rw [Pi.mul_apply, coeff_mul]; exact Sharp.sum _ _ _ (fun i _=> Sharp.mul h (hf i.1) ( hg i.2 ))
lemma pow (i:ℕ)(hf: Sure l τ x y): Sure l τ (fun j=>x j^i) (fun j=>y j^i):= by induction i with | zero=> simp_rw [pow_zero]; exact Clock.Sure.unit l τ 1 | succ i ih=> simp_rw [pow_succ]; exact mul h ih hf
lemma cycle {C T: I→ℕ→ Point G 6 3}(H:NPoints l τ C T): Sure l τ (fun i=> b3 (batchT (C i))) (fun i=> b3 (batchT (T i))):= by
    have ht(w:Badge): Sure l τ (fun i=> batchT (C i) w) (fun i=> batchT (T i) w):= by intro i; simp_rw [batchT,coeff_mk]; exact H i _
    unfold b3; exact add (sub (ht Finset.univ) ( add (add (mul h (ht _) (ht _)) (mul h (ht _) (ht _))) (mul h (ht _) (ht _)))) ( scalar 2 (mul h (mul h (ht _) (ht _)) (ht _)) )
-- unlead. FAST even after slope meter because q fixed input.
lemma reverse (q:Φ)(hq:Rooted q)(ht:coeff 1 q≠0)(hp:Sure l τ z (fun _=> q))(hz:∀ᶠ i in l,Rooted (z i))(hh:Sure l τ (fun i=> ( x i ).subst (z i)) (fun i=> ( y i ).subst q)): Sure l τ x y:= by
    intro m; induction m using Nat.strong_induction_on with| h m ih=>
      let a:= coeff m (q^m); have he : a≠0:= by unfold a; rw [ Token.stamp_n q hq ]; exact pow_ne_zero _ ht;
      have hT : Sharp l τ (fun i=> Token.tend (x i) (z i) m) ( fun i=> Token.tend ( y i ) q m ):= Sharp.sum _ _ _ (fun i hi=> Sharp.mul h ( ih i ( Finset.mem_range.mp hi ) ) ( pow h i hp m ));
      let Z i:= coeff m (z i ^ m); have hw:Fast l τ (fun i=> (Z i)⁻¹ ) (fun i=> a⁻¹ ):= Fast.constant (w:=fun z:ℂ=> z⁻¹) h ( differentiableAt_id.inv he ) (pow h m hp m).sails
      refine ( Sharp.mul h (( hh m ).sub hT ) ( Sharp.above hw ) ).tee ?_ ( Eventually.of_forall fun i=>?_ );
      · filter_upwards [hz, ( Fast.aims h _ (( pow h m hp m ).sails ) ).eventually ( eventually_ne_nhds he )] with i hi hv; rw [ ← div_eq_mul_inv ]; exact Eq.symm ( Token.meter ( x i ) hi m hv )
      dsimp only; rw [ ← div_eq_mul_inv ]; exact Eq.symm (Token.meter ( y i ) hq m he)
end Sure
variable (ν:ℝ)(Y:Initialize G){V:Normalize.Store G}(X:Rose.Pick V)(S:Prescription (Press.portDeck G)){O: Booked (Press.portDeck G)}(T: MS_Data G O) (h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)
variable (hr:Position.Favors.Horder S)(hv:Position.Ace.UnitP S)
namespace Detected
variable [NormedAddCommGroup E][NormedSpace ℝ E](u:E)
abbrev whole (v:E→ Cn)(u:E):=∀ n, ContDiffAt ℝ ∞ (fun i=> coeff n (v i)) u
variable {u} {x y:E→ Cn}
lemma add (hx:whole x u)(hy:whole y u): whole ( x+y ) u:= by intro k; simp_rw [Pi.add_apply,map_add]; exact (hx k).add (hy k)
lemma sub (hx:whole x u)(hy:whole y u): whole ( x-y ) u:= by intro k; simp_rw [Pi.sub_apply,map_sub]; exact (hx k).sub (hy k)
lemma mul (hx:whole x u)(hy:whole y u): whole ( x*y ) u:= by intro k; simp_rw [Pi.mul_apply,coeff_mul ]; exact ContDiffAt.sum ( fun i hi=> (hx _).mul (hy _) )
lemma scalar (a:ℂ)(hx:whole x u): whole (a • x) u:= by intro k; simp_rw [Pi.smul_apply,map_smul]; exact (hx k).const_smul a
lemma clock (v:Points 3)(h:v∈conf 3): whole (Reg.Choice.trace ν T V) v:= by
    have ht (s:Badge): whole (fun i:Points 3=> batchT (wall ν V T 6 i) s) v:= by intro i; simp_rw [batchT,coeff_mk]; exact Cake.wall_s ν V T _ _ v h
    unfold trace b3; exact add (sub (ht Finset.univ) ( add (add (mul (ht _) (ht _)) (mul (ht _) (ht _))) (mul (ht _) (ht _)))) ( scalar 2 (mul (mul (ht _) (ht _)) (ht _)) )
-- strengthen: uniform all K.M;
include h hs hr hv
lemma degree {K:Set (Points 3)}(hc:IsCompact K)(ht: K⊆ conf 3): Sure (Pose K) grab (fun i:Sample 3=>(Rose.together Y V i).subst ( reset ν S i.F )) ( Choice.trace ν T V ∘ familiar ):= by
    apply Sure.tee ( Sure.cycle ( C:=fun i:Sample 3=> substitute (reset ν S i.F) ( Rose.cooked Y V 6 i ) ) (travels K) (Cake.feature ν Y V S T h hs hr hv hc ht) ) _ ( .refl .. ); exact Eventually.of_forall fun i=> b3_p ( Rose.cooked Y V 6 i ) _ ( share .. )
private abbrev vision (v:Mesh) := (Rose.Detector Y X v).subst (reset ν S v)
lemma report (k:ℕ): Sharp Front id (fun i=> coeff k (( Rose.Detector Y X i ).subst (Dframe.reset ν S i))) (fun _=> coeff k (sky ν X T)):= by
    let f(i:Sample 3):= ( together Y V i ).subst (reset ν S i.F); let Y':= Rose.test X; let t:Sample 3→ MS.Book.Convolve.T ℂ := fun i j=> coeff j (together Y V i);
    let F:=fun i=> coeff k (trace ν T V i); let P:= tsupport Y'; have he:=degree ( K:=P ) ν Y S T ( V:=V ) h hs hr hv ( Y'.hasCompactSupport ) Y'.tsupport_subset k;
    have hw(i: Mesh): coeff k (vision ν Y X S i)= Deposit i (fun i=>coeff k (f i)) Y':= by
        unfold vision f; symm; simp_rw [ ← Constants.actual_subst _ (reset _ _ _) (share ..), coeff_mk ]; rw [ CoverTest.sub_s i ( q:=fun i=> reset ν S i ) Y' ( ζ:=t ) ]; simp_rw [Rose.detector]; rfl
    unfold Choice.sky; apply Sharp.above; change Fast Front id (fun i=> coeff k (vision ν Y X S i)) _;
    simp_rw [ hw, coeff_mk ]; apply Labor.single ( x:=fun i t=> Deposit i (fun i=> coeff k (f i)) t ) ( y:=fun t=>t.applyTo F ) ( f:=Y' ) _ ( Subset.refl P ); exact Speed.ahead ( cartel.mpr he.sails ) Y'.hasCompactSupport Y'.tsupport_subset ( fun i hi=> clock ν T _ hi k ) (fun _ _ _=>rfl)
lemma clocked : Sure Front id (prospects ν Y X S) (fun _=> Choice.choice ν X T):= by
    have he:= report ν Y X S T h hs hr hv; have hf: ∀ i,prospects ν Y X S i=tune X (( Detector Y X i ).subst ( Dframe.reset ν S i )):= fun i=> tune_p X _ _ (share ..); intro i; simp_rw [hf]; apply Sure.scalar _ _ i; apply Sure.sub he _; intro k; simp_rw [ coeff_C ]; split_ifs; exact he 0; exact Sharp.joy ..
end Detected
end YM.FVA2.Speed.Clock
