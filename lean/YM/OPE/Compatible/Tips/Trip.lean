import YM.OPE.Compatible.Hike.Joke
import YM.OPE.Compatible.Rave.Orb
import YM.OPE.Compatible.Karls.Jay
import YM.OPE.Compatible.Hike.Piece
import YM.OPE.Compatible.Karls.Bent
import YM.OPE.Compatible.Karls.York
/-!
# H.Launch supplies.Born.Cumul integrations at Mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
variable {n c f:Side}{I J M E F Q:Type}{G:Gauge}{r i j d m l k e:ℕ}{τ:Phase→ℕ}
variable {K:Sponsor G}{T:Seasons K}{P:Patch}{R:ChartRatio G}{C:KernelChoices}{p:Clip}
variable {v v' b:ℝ} {A:Alps K T i v}{D:Alps K T j v'}{U:Boxes G P K.K}
local notation "Y!"=> solar G d τ
local notation "T!"=> Tracts G d τ
open PriceZ
local notation "L!"=> Tower (Shade G) d τ
local notation "D!"=> Shade G
local notation "Y"=> solar G d τ
open JetS
open Finset
open PriceZ Hark
open Hark Nestle StageLight Shrew Balsam
lemma mount (P:Patch) : P.L.val>1:=by have ht:=P.coarse;omega
lemma staysX (i:ℕ)(c:Side): CountL c P.L i=stageN P.L c i:=by induction i with
    | zero=> change c= c*_; simp
    | succ i ih=> unfold stageN; change (CountL c P.L i)*_=_; rw [ih, pow_succ]; exact mul_assoc ..
lemma changedH (i:ℕ)(x:Cover):spikeS K P (wrap c x) i=wrap _ (Prairies.rangeS P.L i x):=by induction i with
   | zero=> simp only [Prairies.rangeS,ζ,pow_zero,PNat.one_coe, one_smul]
   | succ i ih=> change (trip K P i c).embed (spikeS K P (wrap c x) i)=_; rw [ih,(trip K P i c).embed_wrap]; simp only [Prairies.rangeS,ζ,pow_succ',PNat.mul_coe,mul_smul];rfl
lemma supnatMultip (f:I→ℕ)(s:Finset I)(n:ℕ): n*s.sup f=s.sup (fun i=>n*f i):=by
     induction s using Finset.induction with
     | empty=> simp
     | insert i s h ih=> rw [Finset.sup_insert,Finset.sup_insert]; change n*(max (f i) _)=max _ _; rw [←ih,max_comm (f i),mul_max_of_nonneg _ _ (Nat.zero_le _)]; exact max_comm .. -- lemma name
lemma sexH (_p:Patch)(c L:Side)(S:Ratio c L)(x y: Site c): separation (S.embed x) (S.embed y)= S.count.val * separation x y :=by
    unfold separation; rw [show S.embed x-S.embed y= S.embed (x-y) from ?_]; swap;· exact (map_sub S.root x y).symm -- `.root`? 
    -- pdist = frame step.Try
    unfold pdist; rw [S.lift_embed]; simp only [Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul,Int.natAbs_natCast]; let f(i):=(lift (x-y) i).natAbs; symm; apply supnatMultip
lemma north (x y:Site n)(h:Even n.val)(he:∀ k:Kv,decks k x≠y):Pins K P x y:=by
     let q:=spikeS K P x; let t:=spikeS K P y; refine ⟨max 2 ((n.val:ℝ)),le_max_left ..,fun i k=>?_⟩; induction i with
     | zero=> have ht: (0:ℕ)<separation (decks k x) y:= by
                 exact pdist_pos (sub_ne_zero_of_ne (he k))
              have hh: (n.val:ℝ) ≤ (n.val:ℝ)* separation (decks k x) y:= le_mul_of_one_le_right (by positivity) (by exact_mod_cast (show 1 ≤ _ from ht)); exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (Nat.cast_nonneg _))
     | succ i ih=>
        let Q:=trip K P i n; let v:=CountL n P.L i; have hp : decks k (q (i+1))=Q.embed (decks k (q i)):= (StageLight.orbitD Q (evenBoot K P h i) k (q i)).symm
        change ((CountL n P.L (i+1)).val:ℝ)≤ (max 2 ((n.val:ℝ))) * ↑(separation (decks k (q (i+1))) (Q.embed (t i))); rw [hp,sexH P, show (CountL n P.L (i+1)).val=v.val* Q.count.val from rfl, Nat.cast_mul, Nat.cast_mul]; apply le_trans (mul_le_mul_of_nonneg_right ih (by positivity : (0:ℝ)≤ ↑Q.count.val)); exact le_of_eq (by ring)
lemma togetherH {ℓ:Filter I}(p q:Cover)(t:I→Side)(hp:Ncap t ℓ)(hx:p≠q)(he:∀ i,Even (t i).val):∀ᶠ i in ℓ,Pins K P (wrap (t i) p) (wrap (t i) q):=by
     filter_upwards [spaceBeam _ t hp p q, hp.eventually (eventually_ge_atTop (2*(size p+size q)+1))] with i hi hN; apply north _ _ (he i); intro k; by_cases h:k=0; swap; · exact hi k h
     subst k; rw [Weir.flats]; exact fun h=> hx ((gentle (by omega) (n:=t i) (x:=p)).symm.trans ((congr_arg _ h).trans (gentle (by omega))))
end YM.OPE.Quit.Jac
