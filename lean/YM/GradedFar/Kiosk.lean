import YM.GradedFar.Marquee
/-!
# Differentiating ordinary OPE comparison series in H frame

First compare in FTC. Prices authorized `(M.4)` for **values** (via Regained).
Proof first line adapt Tariff.{Increment,Sunshine}, on physical `packet` after center normalization. `launch` derivatives are shape compare, x only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Window
open Function Filter Set MeasureTheory Metric PowerSeries
open Extraction Table Spec OPE OPE.Orbits OPE.Nesting PhysMS Trace.Pilot
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh MS MS.Native MS.Land MS.Fleet
open Tariff Tariff.Sunshine
open private YM.Integration.GradedFar.Tariff.Sunshine.increment_cmp YM.Integration.GradedFar.Tariff.Sunshine.turn_zero from YM.GradedFar.Glow
open scoped Topology BigOperators ContDiff Classical
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (F : Final C f S) (P: ℝ→tower S) (R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
variable (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "V"=> Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)
variable {n h d:ℕ} (l:Toon G d)
local notation "X" => Points n
local notation "ι" => Fin n×Axis
local notation "Y" => Toon G (h+1)
variable {t:ℝ→ℝ} (ht:Coupling G t) (Hn: ∀ h, Regained F P R (Scale.Measure.outlook (WilsonPrescription.scheme Z) (WilsonPrescription.criterion Z)) t n h d)
    (Hs: Neighbor.Included F P h (h+1) (Nat.le_succ h))(α: Future G h)(hα: PaidFuture F P α t)
variable {a b:ℝ}
variable (u:ListInput G n h)
def beam (o:E4)(r:ℝ)(x e:X):ℂ:= ∑ i: ι, parallel i e* messenger F P R o r l x (update (climbing u) i.1 (push F P h i.2 r (u i.1)) : ListInput G n (h+1))
-- include not explicit? section variable used in body implicit binder becomes include
lemma release (o:E4)(r:ℝ)(hk:Going F P h r)(x e:X)(hh:∀ s∈uIcc a b, arena F R d o r (slopePath x e s)):
 messenger F P R o r l (slopePath x e b) u - messenger F P R o r l (slopePath x e a) u= ∫ s in a..b, beam F P R l u o r (slopePath x e s) e:=by
 apply Eq.symm; apply intervalIntegral.integral_eq_sub_of_hasDerivAt; rotate_left
 · apply ContinuousOn.intervalIntegrable; exact continuousOn_finsetSum _ (fun i _=> continuousOn_const.mul (fun k hk=> ((breeze F P R o r l (slopePath x e k) (hh k hk) _).continuousAt.comp (walking_cont x e).continuousAt).continuousWithinAt))
 intro i hi; refine (slope_chain (f:=fun x=> messenger F P R o r l x u) x e i ((breeze F P R _ _ l _ (hh i hi) u).differentiableAt (by simp))).congr_deriv ?_
 rw [evaluate]; exact Finset.sum_congr rfl fun a _=> congrArg (parallel a e*·) (mete F P R o r l hk u _ a (hh i hi))

def projectionOne (i:ι)(x:X):PowerSeries ℂ:= ∑ j:Y, α i.2 (u i.1) j * Cargo V x (update (climbing u) i.1 (theory j) : ListInput G n (h+1)) l
def projection (x e:X) := ∑ i: ι, PowerSeries.C (parallel i e) * projectionOne Z l α u i x
include H
lemma lighting (i:ι)(p:ℕ) : ContinuousOn (fun x=> coeff p (projectionOne Z l α u i x)) (conf n):=by
 simp_rw [projectionOne, map_sum, coeff_mul]; exact continuousOn_finsetSum _ fun a _=> continuousOn_finsetSum _ fun q _=> continuousOn_const.mul (cargo_cont Z M H _ _ _)
omit H
section
variable (x e:Points n)(hx: Walks x e a b) (o:E4)
-- avoid macros by changing
include hx Hn
local notation "K"=> (slopePath x e) '' (uIcc a b)
local notation "Vt"=> slopePath x e
-- Continuum margin at every shape on path, enough to spend. enlarge via near_collar
lemma earnsShape {w:Fin n→ℕ}(u:AppointedH140Inputs G w)(hw: AppointedH140Through h w) : Receives t trail (fun r (s:↥(uIcc a b))=> messenger F P R o r l (Vt s) u)
    (fun s=> Cargo V (Vt s) u l):=
       Receives.along (Hn h hw K (isCompact_uIcc.image (walking_cont x e)) hx.image_subset l u) (fun i=> (o,⟨_,mem_image_of_mem _ i.property⟩))
include ht hα hG
lemma earnsAngle : Receives t trail (fun r (s:↥(uIcc a b))=> beam F P R l u o r (Vt s) e) (fun s=> projection Z l α u (Vt s) e) := by
 unfold beam projection projectionOne; simp_rw [changing (messenger F P R _ _ _ _) (climbing u) (push F P h _ _ _)]; have he:=Coupling.conforms hG ht
 refine Receives.sum _ fun i _=> Receives.mul (Receives.fix _) (Receives.sum _ (fun j _=>?_)) he; exact Receives.mul (Receives.along (hα _ _ _) (fun _=>()))
      (earnsShape F P R Z l Hn x e hx o _ (fun _=>le_rfl)) he
include H Hs
lemma earnsRoll : Cargo V (Vt b) u l - Cargo V (Vt a) u l= operand a b (fun s=> projection Z l α u (Vt s) e):=by
 obtain he :=earnsShape F P R Z l Hn x e hx (o:=0) u (fun _=>le_rfl); -- choose fixed center
 obtain hh:= Receives.sub (he.along (fun _:Unit=>⟨b,right_mem_uIcc⟩)) (he.along (fun _:Unit=>⟨a,left_mem_uIcc⟩))
 obtain hb : ∀ᶠ r in trail, ∀ i∈ uIcc a b, arena F R d 0 r (Vt i) := (near_collar F R n d (isCompact_uIcc.image (walking_cont x e)) hx.image_subset).mono (fun r hr i hi=> hr _ (mem_image_of_mem _ hi) 0)
 have ht':∀ᶠ r in trail, IntervalIntegrable (fun i=> beam F P R l u 0 r (Vt i) e) volume a b := hb.mono fun r hr=> ((continuousOn_finsetSum Finset.univ (fun j _=> continuousOn_const.mul
    (fun k hk=> ((breeze F P R _ _ l _ (hr k hk) _).continuousAt.comp (walking_cont x e).continuousAt).continuousWithinAt)))).intervalIntegrable
 obtain hf:= integrates (F:=fun i=> projection Z l α u (Vt i) e) (f:=fun r i=> beam F P R l u 0 r (Vt i) e) (earnsAngle F P R Z l ht Hn α hα u x e hx 0 (hG:=hG)) ht' (fun i=> show IntervalIntegrable _ _ _ _ from
    (by simp_rw [projection, map_sum, coeff_C_mul]; exact ((continuousOn_finsetSum _ (fun j _=> ((lighting Z M H l α u j i).comp (walking_cont x e).continuousOn hx).const_mul _ ))).intervalIntegrable ))
 apply Receives.same (Coupling.conforms hG ht) (ht.positive.mono fun x hx=>hx.ne') (F:=fun (_:Unit)=> Cargo V (Vt b) u l - Cargo V (Vt a) u l) _ hf ()
 exact Receives.congr hh ((hb.and Hs).mono (fun r hr=> funext fun _=> release F P R l u 0 r hr.2 x e hr.1)) fun _=> rfl
end
-- CLM port
include H
def launch (k:ℕ)(x:X) : X →L[ℝ] ℂ := ∑ i: ι, (coeff k (projectionOne Z l α u i x)) • ticketOne i
lemma admit_ride (i:ℕ): ContinuousOn (launch Z l α u i) (conf n):=continuousOn_finsetSum Finset.univ (fun j _=> (lighting Z M H l α u j i).smul continuousOn_const)
omit H in
lemma launchSlot (i:ℕ)(x:X)(b:ι) : launch Z l α u i x (Points.direction b.1 b.2)=coeff i (projectionOne Z l α u b x):= by
 rw [launch, _root_.sum_apply, Finset.sum_eq_single b]; simp only [_root_.smul_apply,smul_eq_mul]; change _ * parallel b _ = _; simp [parallel,Points.direction,basis];
 · intro j _ he; rw [_root_.smul_apply,YM.Integration.GradedFar.Tariff.Sunshine.turn_zero _ _ he,smul_zero];
 simp
include ht Hs Hn hα
lemma trueC (k:ℕ){x:X}(hx:x∈ conf n): HasFDerivAt (fun x=> coeff k (Cargo V x u l)) (launch Z l α u k x) x:=by
 refine YM.Integration.GradedFar.Tariff.Sunshine.increment_cmp (conf n) (conf_open _) (admit_ride Z M H l α u k) (fun x v he=>?_) hx; let e:= v-x; have hh(y:X): launch Z l α u k y (v-x)= coeff k (projection Z l α u y (v-x)):=by
    simp_rw [launch, _root_.sum_apply, projection, map_sum, coeff_C_mul]; exact Finset.sum_congr rfl fun _ _=> mul_comm ..
 obtain ht:= congrArg (coeff k) (earnsRoll F P R Z M H l ht Hn Hs α hα u x (v-x) he); simp_rw [map_sub,Crosser.endsZero,Crosser.endsOne,operand,coeff_mk] at ht
 simp_rw [hh]; exact ht
end YM.Integration.GradedFar.Window
