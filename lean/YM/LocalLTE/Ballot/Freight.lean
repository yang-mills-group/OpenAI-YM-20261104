import YM.LocalLTE.Vinca.Yield
import YM.LocalLTE.Ballot.Elegy
/-! Estate assembly and window budgets helper, true proofs. Use W1 to instantiate downstream step consumption. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Bandage Mallow Coterie
open YM.MergeProof YM.LocalLTE.Vinca
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
section
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{P:Bolt A}{e η:ℝ}{R:Factor A}
local notation "H"=> Issue.trail P
variable {C:ℕ→ℝ}{W:Bid.Worth}{p0 q l r:ℕ}{k:ℝ} (U:Harmonics R C W P l)
-- window height supplier
variable (hr:Legato.Elevera R.shape p0 k q l r e A.delay)(hx:∀ i j,(R.target i j).halo=500)(hp:East.stagnate q 500<l) {N n m:ℕ} (hm:m<N)
local notation "T"=> U.port N m n hm
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "Y"=> A.B.a.clock.hatBeta m
set_option quotPrecheck false
open Pressure ConnectedActivityE6 Push.AbsoluteSums
include hr
lemma lenV (m n:ℕ) :10*(l*Pressure.radiusB (A.B.a.clock.hatBeta m))< (A.B.a.S.side m n).val:=by
   let y:= A.delay; let a:= (A.B.a.budget m); let w:= A.B.a.budget (m+1); let u:=1+a.B+w.B; have hx:= hr.side (A.B.a.clock.J (m+1)); refine lt_of_lt_of_le ?_ (A.B.valid.volume m n); change 10*(l*a.B)< _* u^y.growth _
   rw [← Nat.mul_assoc]; refine lt_of_le_of_lt (Nat.mul_le_mul_right a.B (le_trans ?_ hx)) (Nat.mul_lt_mul_of_pos_left ?_ (show 0<_ from lt_of_lt_of_le ?_ hx))
   · omega
   · refine lt_of_lt_of_le (b:=u) (by unfold u; omega) (le_self_pow₀ (show 1 ≤ u from by unfold u; omega) ?_); have he:=hr.grew (A.B.a.clock.J (m+1)); change A.delay.growth (A.B.a.clock.J (m+1)) ≠ 0; omega
   omega
include hr
-- outer α across N,n. H1. Price.Manifest same Y. (not statement of motion choices before opportunities).
lemma votedK (m:ℕ) : ∃ K dα:ℕ, YM.LocalLTE.Fan.ManifestC (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (D.L (A.B.a.clock.J (m+1))) (R.shape.o (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.expense (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) Push.SectorMeasure.Chi.canonical (A.B.a.budget m).order (A.B.a.budget m).power p0 q l (A.B.a.clock.J (m+1)) K dα k e Mallow.aust (A.B.a.clock.hatBeta m) (R.shape.μ (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)):=by
   obtain ⟨u,v,ht⟩:= hr.time _ _ (step_paid A.B.a m); have hh:=ht _ (A.B.valid.pays m); rw [Rain.jersey (A:=A) (m:=m)|>.1,Rain.jersey (A:=A) (m:=m)|>.2.1]; exact ⟨_,_, hh⟩
omit hr
lemma coreSway {G:Gauge}{d N n m:ℕ}{F: Labels.Frame G d}{A:Hol G}{Ht:History G} {P:Rep G (Ht.S.side (m+1) n)} (hp:Ht.rep N n (m+1)=P)(U:Gateway F A P (Ht.S.side m n))(i:F.Index) : (YM.LocalLTE.Vinca.sway Ht N n m A P hp U).core i=U.core i:=by subst P; rfl
lemma plantC (d:ℕ) (hd:d+3≤ A.B.a.clock.J m): (U.lays d N n m hm).core = fun i=> Graces.canvasB d (T) (Circlet.lark ((T).inPort) i (Bandage.aperture U.tag N m n T d hd) (U.ore hm)) l (U.space N m n hm):=by
    unfold Harmonics.lays Bandage.purser; rw [dif_pos hd]; funext i; exact Legato.coreSway ..
end
end YM.PhysicalNext.Repeat.Legato
