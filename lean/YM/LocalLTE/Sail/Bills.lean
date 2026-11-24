import YM.LocalLTE.Sail.Campaign
import YM.LocalLTE.Brochure.Millet
/-!
# The per-step investment routine for canonical local panels
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Spiral
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca YM.LocalLTE LocalLTE.Ticket LocalLTE.River LocalLTE.Sail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}
open Pressure ConnectedActivityE6 Bandage.Harmonics Motion
variable (K:ℕ)
noncomputable def chronicleShift (u:ℕ):ℝ := 9+6*(u:ℝ)
noncomputable abbrev intakeWeight (u:ℕ)(Y:ℝ) :ℝ:= Y^(-chronicleShift u)
noncomputable abbrev reburn (t:ℝ):= t^(-(4:ℝ))
noncomputable abbrev allocationF (t:ℝ):= 2*reburn t
noncomputable abbrev allocationK (t e:ℝ):= reburn t * t^(-e)
noncomputable abbrev waterline (y:ℝ):= y^(-(3:ℝ))
-- budget after individual calibration.Motion appeal at THAT true geometry.
variable (d q0 u TT p₀ :ℕ)(L:Side) (i j: Stage)(p l:ℕ) -- p0 permit. precision p in public book.
variable (G) (s e :ℝ)
structure Lagging (d p u:ℕ)(L:Side)(i j:Stage)(C ε x:ℝ) (G:Gauge)(P TT l:ℕ):Prop where
   -- unfolded.X.B&T. Ξ errors eager.
   q : let y:= betaF G x L; intakeWeight u y * chanF G d i l L j C (y^(grantZ P TT u)) ≤ y^aust
   h : let y:= betaF G x L; intakeWeight u y * chanT G d i l L j C y (y^(grantZ P TT u)) ≤ waterline y
   z : let y:= betaF G x L; y^ε* (2*intakeWeight u y*(chanK G d i C (y^(grantZ P TT u))+y^(grantZ P TT u))) ≤ waterline y
   price : ∀ v:ℝ, betaF G x L/2 ≤ v→ v≤ 2*betaF G x L→ rotationP ((Labels.frames G).level d) j.order j.power * C * x^(grantZ P TT (u+1)) ≤ (Coat.gStep v)^((p:ℝ)+1)
variable (hp: grantZ p₀ TT u + e≤ 0)(he: grantZ p₀ TT (u+1)< -((p:ℝ)+1)/2)(hu:u≤TT)
include hp he
lemma planting : ∀ᶠ x in atTop,Lagging d p u L i j s e x G p₀ TT l:=by
    let X t:= betaF G t L; let A:= chronicleShift u
    let r:= grantZ p₀ TT u; let R:= grantZ p₀ TT (u+1); let V t:= X t ^ r
    have hv : Rate G L r V:= Rate.power
    have h0 : R ≤ 0:=by linarith only [he, Nat.cast_nonneg (α:=ℝ) p]
    have hp0:r ≤ 0:=by
       have hr':r≤R:=by unfold r R grantZ;push_cast; linarith only
       exact hr'.trans h0
    have hA : 9≤ A:=le_add_of_nonneg_right (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    let z(u):= X u^(-A); have hZ:Rate G L (-A) z:= Rate.power
    let t0 t:= chanT G d i l L j s (X t) (V t)
    let f0 t:= chanF G d i l L j s (V t)
    let k0 t:= chanK G d i s (V t)
    let Y:= (Labels.frames G).level d
    have hT:Rate G L 1 t0 :=by
       have hz: Rate G L 1 X:=by simpa only [Real.rpow_one] using! (Rate.power (G:=G) (L:=L) (a:=1))
       have hV:= hv.weaken (hp0.trans zero_le_one)
       exact (((((((Rate.const (payG G j i l d L).beam).weaken zero_le_one).add (((hz.add hV).add (hV.add hV)).mul_left 2)).mul_left _).mul_left _).mul_left _).mul_left _)
    have hF:Rate G L 0 f0 :=by
       have hV:=hv.weaken hp0
       exact ((((Rate.const _).add (((Rate.const _).add (hV.add hV)).mul_left _)).mul_left _).mul_left _)
    have hK:Rate G L r k0:= (((((hv.add (hv.add hv)).mul_left _).mul_left _).mul_left _).mul_left _).mul_left _
    have hs: e+(-A+r) ≤ -9 := by change r+e≤0 at hp; linarith only [hp,hA]
    filter_upwards [(hZ.mul hF) aust (by unfold aust; linarith only [hA]),(hZ.mul hT) (-3) (by linarith only [hA]), ((Rate.power (G:=G) (L:=L) (a:=e)).mul ((hZ.mul_left 2).mul (hK.add hv))) (-3) (by linarith only [hs]), Urns.actualG (G:=G) L ((p:ℝ)+1) _ R ((Mallow.flagE L _ h0).mul_left (rotationP Y j.order j.power*s)) he] with x h hx ht hj;
    exact ⟨(le_abs_self _).trans h,(le_abs_self _).trans hx,(le_abs_self _).trans ht,hj⟩
omit he hp
section stage
structure Repl (K:ℕ)(e:ℝ)(i: Stage)(P u:ℕ)(G:Gauge)(L:Side)(x:ℝ) : Prop where
   repaint (V:Type)[Fintype V] (h:Fintype.card V ≤ K) (P':BudgetPoint) (hp:P'.order=i.order)(he:P'.power=i.power) : let y:= betaF G x L; Port.capacity P' V (allocationF y) (allocationK y e) (Urns.divisor y) (allocationK y e) (y^e) (L.val*Pressure.radiusB x) ≤ waterline y
   transfers : intakeWeight (u+1) x ≤ reburn x* intakeWeight u (betaF G x L)
   ceiling : let y:= betaF G x L; ((K:ℝ)*waterline y)+((K:ℝ)*waterline y)+waterline y ≤ wound y
   stamp : let y:= betaF G x L; wound y+(Real.exp (wound y)-1) ≤ y^(-(1:ℝ))
   issue : let y:= betaF G x L; ∀ β:ℝ, y/2≤β→β≤2*y→ y^(chronicleShift u*K)* y^(-e) ≤ (Coat.gStep β)^((P:ℝ)+1)
local notation "X"=>fun t:ℝ=> betaF G t L
lemma nextWeight : ∀ᶠ t in atTop, intakeWeight (u+1) t ≤ reburn t*intakeWeight u (X t) :=by
    let y:= chronicleShift u; let z:= -y; let f :ℝ→ℝ:= X; let a:= G.slopeConstant * Real.log L.val; have he:z≤0:=by unfold z y chronicleShift; linarith only [Nat.cast_nonneg (α:=ℝ) u]
    filter_upwards [eventually_ge_atTop a,eventually_ge_atTop ((2:ℝ)^(-z)),eventually_ge_atTop (1:ℝ),(Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx h ht hv
    have hp:0<x:=zero_lt_one.trans_le ht
    have hK:(2:ℝ)^z*x^z ≤ f x^z:=by rw [← Real.mul_rpow (by norm_num) hp.le]; apply Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hv) _ he; change x+a ≤ 2*x; linarith only [hx]
    apply le_trans _ (mul_le_mul_of_nonneg_left hK (show 0≤reburn x from Real.rpow_nonneg hp.le _)); unfold intakeWeight reburn
    have hx0:-chronicleShift (u+1) ≤ -(4:ℝ) + (-(1:ℝ)+z):=by unfold z y chronicleShift; push_cast; linarith only
    refine le_trans (Real.rpow_le_rpow_of_exponent_le ht hx0) ?_; rw [Real.rpow_add hp, Real.rpow_add hp]; apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hp.le _); refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hp.le _); rw [Real.rpow_neg (by norm_num)] at h; rw [Real.rpow_neg_one]; have hk:= (inv_le_inv₀ hp (inv_pos.mpr (Real.rpow_pos_of_pos (show (0:ℝ)<2 by norm_num) z))).mpr h; rwa [inv_inv] at hk
variable (hT:chronicleShift u*K + (-e)< -((p:ℝ)+1)/2)
include hT
lemma replacement : ∀ᶠ x in atTop, Repl K e i p u G L x:=by
    let f:= (X); let g t:= allocationK (f t) e; let s t:= allocationF (f t); let h t:= Urns.divisor (f t); let b t:= L.val* radiusB t; let c t:= (1+(b t:ℝ))^(i.power*i.order)
    have hz: Rate G L (-4+ -e) g:= Rate.mul Rate.power Rate.power; have hs:Rate G L (-4) s:= Rate.mul_left Rate.power 2
    have hb : Rate G L 0 (fun t=> ((L.val*Pressure.radiusB t:ℕ):ℝ)):=by simp_rw [Nat.cast_mul]; exact Rate.radius_price.mul_left _
    have hc:Rate G L 0 c:=by simpa only [zero_mul] using! (((Rate.const 1).add hb).pow (i.power*i.order))
    let P(t):= 2*(c t*((K:ℝ)*s t))+ (f t)^e*(2*((K:ℝ)*g t)+2*((K:ℝ)*(g t*h t)))
    have hP : Rate G L (-4) P:=by
       have hx:= hc.mul (hs.mul_left (K:ℝ))|>.mul_left 2; rw [zero_add] at hx; apply Rate.add hx; have hh:Rate G L 0 h:= Mallow.afterShift L (G:=G) 0; have hy:= hz.mul hh; rw [add_zero] at hy
       convert! Rate.mul Rate.power (((hz.mul_left (K:ℝ)).mul_left 2).add ((hy.mul_left (K:ℝ)).mul_left 2)) using 1; ring
    have hx:Rate G L (-3) (fun t=> (K:ℝ)*waterline (X t)+(K:ℝ)*waterline (X t)+waterline (X t)):=((Rate.mul_left Rate.power _).add (Rate.mul_left Rate.power _)).add Rate.power
    filter_upwards [nextWeight G u L,hP (-3) (by norm_num),hx (-2) (by norm_num),(Work.E09.betaF_growth G L).eventually_ge_atTop 4, Urns.actualG (G:=G) L ((p:ℝ)+1) _ _ ((Rate.power (a:=chronicleShift u*K)).mul Rate.power) hT] with t ht hK he hh hY
    have hz: 1 ≤ f t:= le_trans (by norm_num : (1:ℝ) ≤ 4) hh; have hp : 0 ≤ f t:= zero_le_one.trans hz; have hX:0<f t:=zero_lt_one.trans_le hz
    refine ⟨fun V hv ht P' hx hy=>?_,ht,(le_abs_self _).trans he,?_,hY⟩
    · apply le_trans _ ((le_abs_self _).trans hK); unfold Port.capacity Port.turnQ; rw [hx,hy]; let j:= Fintype.card V; change 2*(c t*((j:ℝ)*s t))+(f t)^e*(2*((j:ℝ)*g t)+2*((j:ℝ)*(g t*h t))) ≤ _
      have hi:(j:ℝ)≤ K:= Nat.cast_le.mpr ht; have hb:0 ≤ c t:=by unfold c; positivity; -- next
      have hv:0≤ s t:=by unfold s allocationF reburn; positivity
      have hz:0≤ g t:=by unfold g allocationK reburn; positivity
      have hs:0≤ h t:=(Urns.nonzero _).le
      exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi hv) hb) zero_le_two) (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi hz) zero_le_two) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hi (mul_nonneg hz hs)) zero_le_two)) (Real.rpow_nonneg hp _))
    have hh0: wound (f t)+(Real.exp (wound (f t))-1) ≤ 3*wound (f t):= by
            have hh :0 ≤ wound (f t):= Real.rpow_nonneg hp _; have ht: |wound (f t)| ≤ 1:= (abs_of_nonneg hh).trans_le (Real.rpow_le_one_of_one_le_of_nonpos hz (by norm_num : (- (2:ℝ))≤0)); have hx :=(le_abs_self _).trans (Real.abs_exp_sub_one_le ht);rw [abs_of_nonneg hh] at hx; linarith only [hx]
    intro y; refine hh0.trans (?_); unfold wound; change 3*_≤ (f t)^(-(1:ℝ)); rw [Real.rpow_neg hp, Real.rpow_neg hp, Real.rpow_one, Real.rpow_two]; have hh : 4 ≤ f t:= hh; field_simp; nlinarith only [hh,hX]
end stage
end YM.PhysicalNext.Repeat.Legato.Spiral
