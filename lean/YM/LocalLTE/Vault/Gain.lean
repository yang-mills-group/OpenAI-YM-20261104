import YM.LocalLTE.Vault.Body
import YM.LocalLTE.Orbit.Costs
/-!
# Summit power costs. Including birth. Requires ONE adjacent Step aspiring course.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spool
open Function Filter Set Lattice RG RG.Shoot Pressure Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Mallow ConnectedActivityE6 Push.AbsoluteSums LocalLTE LocalLTE.Vinca VoucherB LocalLTE.Fan
open Next.Scheduling.Clock Next.Scheduling.Instrument Progress.DirectedRecipe Pressure
attribute [local instance] Gauge.frobInner
variable {G:Gauge} (Y:Stage)(d c i p :ℕ)(e v t:ℝ) (L:Side)
open YM.LocalLTE.Vault Animals
-- Stature bound
noncomputable def hullF (W:Stage)(c:ℕ):ℝ:= Vault.froth W.columns W.order c+1
noncomputable def culture (W:Stage)(c:ℕ):ℝ:= (Real.exp ((W.supportExponent+2)*ballCost 1)) * hullF W c+1
lemma culture_pos (W:Stage)(c:ℕ):1 ≤ culture W c:=by
    have h : 0 ≤ W.columns:=zero_le_one.trans W.columns_ge; unfold culture hullF Vault.froth; apply le_add_of_nonneg_left; positivity
lemma cover_boot (t:ℝ) {s:ℕ}{n:Side}{o:Site n}(h: s+1 ≤ Pressure.radiusB t) : coverNumber (Pressure.radiusB t) (Animals.neighbors (s+1) o) ≤ ballCost 1:=by
    refine (Corona.cover_mono ?_ (Pressure.radiusB t)).trans (Corona.tile o 1 (Pressure.radiusB t) (show 0<Pressure.radiusB t from Nat.zero_lt_succ s|>.trans_le h))
    intro i hi; apply halo_spec.mpr; refine ⟨o,Finset.mem_singleton_self _,?_⟩; rw [one_mul]; exact ((neighbors_mem ..).mp hi).trans h
set_option quotPrecheck false
-- calendar pre/post. W clocks appearance.H.
structure Majesty (G:Gauge) (W:Stage)(d c p K:ℕ)(κ x:ℝ) :Prop where
   β: 1 ≤ x
   tempo : terr G d + 1 ≤ Pressure.radiusB x
   budgets (c':Side)(P:BudgetPoint)(_h:P.order=W.order)(_ht:P.power=W.power)(_hd:P.supportExponent=W.supportExponent)(hz:P.threshold=Pressure.temp x)(_he:P.B= Pressure.radiusB x): let y:= Urns.divisor x; let v:=Vault.wideFare G d x c+1; let S:= Animals.neighbors (terr G d+1) (0:Site c'); let u:=(x)^(echoBit K-1); Push.Local.hitWidth P*y ≤1 ∧ (Push.Local.hitWidth P*y*Push.Local.reservedMass P S v ≤ weightC x K)∧ P.mass S (2*u) ≤ weightC x K ∧P.mass S (hullF W c+2*u) ≤ x ∧
     ∀ (_:2*(terr G d+1)< c'.val)(_ :2*(2*(terr G d)) ≤ c'.val)(ι:Type)(J:ι→ℕ)(a:∀ i:ι, ((Labels.frames G).level (J i)).Coeff)(I:Finset ι), I.card≤c→ (∀ z∈I,J z ≤ d)→ (∀ z∈I, ((Labels.frames G).level (J z)).coeffSize (a z) ≤ 1) → let f:= fareK P J a I (0:Site c'); let g:= f-Vault.halcyon f;∀ Y:FrameBox.Grove (0:Site c'), (P.Regular (neighbors (terr G d) (0: Site c')) g∧P.supBounds (0:Site c') (neighbors (terr G d) (0:Site c')) g (hullF W c))→ ∀ b:Bool, let T:=Port.scaleQ b∘g; P.supBounds 0 S (T- FrameBox.Hall.shave Y (terr G d) κ p T) u
variable (G)
private lemma corporate : Rate G L 0 (fun x=> ((Pressure.radiusB x+Pressure.radiusB x+1)^4:ℕ)):=by
   have h:= Rate.radius_price (G:=G) (L:=L)
   simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one,zero_mul] using! (((h.add h).add (Rate.const 1)).pow 4)
lemma estate_value : Rate G L ((Vault.most G d:ℝ)*c) (fun x=> Vault.wideFare G d (betaF G x L) c+1):=by
    apply Rate.add _ ((Rate.const _).weaken (by positivity)); unfold Vault.wideFare
    have h:= (((Rate.hat (G:=G) (L:=L)).pow (Vault.most G d)).mul_left (Vault.widest G d)).pow c; simpa only [one_mul] using h
variable {κ ν:ℝ}(hk:Reliable G κ ν)
local notation "b'"=> (terr G d)
-- p: rank. K=i. epsilon gain. proof all eventual.
include hk
lemma estate_cap (H: (Vault.most G d:ℝ)*c -(1/4:ℝ)*p< echoBit i-1) : ∀ᶠ x in atTop, Majesty G Y d c p i κ x:=by
    let L:= Port.oneQ; let y:= Urns.divisor; let v t:=((Pressure.radiusB t+Pressure.radiusB t+1)^4 :ℕ); let z:=Y.supportExponent+2; let Y₀:= Real.exp (z*ballCost 1)
    let t t:= Vault.wideFare G d t c+1; let e:=echoBit i; let k:ℝ→ℝ:= fun x=> (v x:ℝ)*y x*(Y₀*t x);
    have hy(q:ℝ):Rate G L q y:=by simpa only [L,Port.oneShift] using! Mallow.afterShift L (G:=G) q
    have hx(q:ℝ):Rate G L q (fun x=> (v x:ℝ)*y x):=by simpa only [zero_add] using! ((corporate G L).mul (hy q))
    let w:=(most G d:ℝ)*c; have hβ:Rate G L w t:=by simpa only [L,Port.oneShift] using! estate_value G d c L
    have hP:Rate G L (e-1) k:=by convert! (hx (e-1-w)).mul (hβ.mul_left Y₀) using 1; ring
    let u t:= (t:ℝ)^(e-1)
    have hu:Rate G L (e-1) u:=by simpa only [L,Port.oneShift] using! (Rate.power (G:=G) (L:=L) (a:=e-1))
    have he': e-1<0:=by change echoBit i - 1 < 0; linarith only [bitN i]
    let a t:= Y₀*(hullF Y c+2*u t)
    have ha:Rate G L 0 a:= ((Rate.add (Rate.const _) ((hu.weaken he'.le).mul_left _)).mul_left _)
    let s t:= Y₀*(2*u t); have hs:Rate G L (e-1) s:= (hu.mul_left _).mul_left _
    let r:=(terr G d+1); let g0(ζ:ℝ):= Vault.glass G d (p+Y.order) c (betaF G ζ L)
    have hp:= FrameBox.Hall.prunes G L Y.order Y.power p (g:=g0) (n:=fun _=>r) (Rate.const _) hk (show -(7/16:ℝ) ≤ -(1/4:ℝ) by norm_num) (by norm_num : -(1/4:ℝ)<0) (Vault.glass_bill (G:=G) _ _ d c) (show (most G d:ℝ)*c+ -(1/4:ℝ)*p< echoBit i-1 from (by linarith only [H]))
    filter_upwards [eventually_ge_atTop (1:ℝ), Work.E01.radiusB_tendsto.eventually_ge_atTop r, hp,hP e (by linarith only),ha 1 zero_lt_one,hs e (by linarith only),(hx (-1)) 0 (neg_lt_zero.mpr zero_lt_one)] with x ht' hh hv hf ha hu hx
    rw [show L=Port.oneQ from rfl,Port.oneShift,Real.rpow_zero] at hx
    have hz0:0 < x:=zero_lt_one.trans_le ht'
    refine ⟨ht',hh,fun n P h hj hx' hB hq=>?_⟩
    dsimp only
    let Z:= neighbors (terr G d+1) (0:Site n); have hA : (Push.Local.hitWidth P) = v x:=by rw [Push.Local.hitWidth,hq]
    have hΩ : (P.supportExponent+2)*coverNumber P.B Z ≤ z*ballCost 1:=by
       rw [hx',hq]; change z*_ ≤ _; refine mul_le_mul_of_nonneg_left (by exact_mod_cast cover_boot x («s»:=terr G d) («n»:=n) («o»:=(0: Site n)) hh ) (add_nonneg Y.price_pos.le zero_le_two)
    have hν0(g:ℝ)(hg:0 ≤g): P.mass Z g ≤ Y₀*g:= mul_le_mul_of_nonneg_right (Real.exp_monotone (le_trans (by apply mul_le_mul_of_nonneg_right _ (show _ from (by positivity)); linarith only) hΩ)) hg
    have hyP:0≤t x:=by unfold t wideFare; have hZ:0 ≤ Vault.widest G d:=zero_le_one.trans (Vault.wideOne ..); positivity
    simp only [show L=Port.oneQ from rfl,Port.oneShift,Real.rpow_one] at hf ha hu
    have hxP:0≤u x:= Real.rpow_nonneg hz0.le _; have ht0:0 ≤ hullF Y c:=by unfold hullF Vault.froth; have hP:0≤ Y.columns:=zero_le_one.trans Y.columns_ge; positivity
    refine ⟨?_,?_,(hν0 _ (mul_nonneg zero_le_two hxP)).trans ((le_abs_self _).trans hu),(hν0 _ (add_nonneg ht0 (mul_nonneg zero_le_two hxP))).trans ((le_abs_self _).trans ha),?_⟩
    · rw [hA]; exact (le_abs_self _).trans hx
    · rw [hA]; refine le_trans ?_ ((le_abs_self (k x)).trans hf); exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (Real.exp_monotone hΩ) hyP) (mul_nonneg (Nat.cast_nonneg _) (Urns.nonzero _|>.le))
    intro hN hD V J a I ht hi h A he b
    let f:= fareK P J a I (0:Site n); let g :=Port.scaleQ b ∘ (f-halcyon f)
    apply (show P.supBounds 0 Z (g- FrameBox.Hall.shave A (terr G d) κ p g) (u x) from ?_); -- substitute Y.order=P.order
    have hv' : P.threshold ≤2*fiery G x L:=by unfold fiery; rw [show L=Port.oneQ from rfl,Port.oneShift]; have he:= P.threshold_pos; rw [hB] at he ⊢; linarith only [he]
    have hK:= hv P hj (by assumption) hB hv' r (terr G d) le_rfl le_rfl n 0 hN hD A g (Port.framesV he.1 he.2 b|>.1)
    have hu(U: Directions G n)(hu:‖U‖< LocalLTE.Inset.cone (-(1/4:ℝ)) (betaF G x L)): Blaze.Brush (p+Y.order) (1*g0 x) 1 (g ∘ LocalLTE.FrameBox.Grove.soloV) U:=by
       rw [show L= Port.oneQ from rfl, Port.oneShift] at hu; rw [one_mul,show g0 x=Vault.glass G d (p+Y.order) c x from congr_arg (Vault.glass G d (p+Y.order) c) (Port.oneShift G x)]; exact Vault.shades (p+Y.order) P J a I h d c hi ht ht' (by rw [hB]; exact Doors.temp_cheap ht') 0 b U (hu.le.trans (Real.rpow_le_one_of_one_le_of_nonpos ht' (by norm_num : -(1/4:ℝ) ≤ 0))) -- c shadow!
    have h:= hK _ zero_le_one hu; rwa [show L=Port.oneQ from rfl, Port.oneShift,one_mul] at h
end YM.PhysicalNext.Repeat.Legato.Spool
