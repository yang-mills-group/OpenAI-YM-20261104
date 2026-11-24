import YM.MergeProof.Escarp
import YM.LocalLTE.Georges.Mile
import YM.LocalLTE.Georges.CrowdingT
/-! Adaptation of YM/MergeProof/Escarp; same budget on Career. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom
open Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} (hG : G.Simple)
namespace Bandage
variable {M : Metals G} {P:Rolls M.p}{A:Alloy M P}{X:Factor A}{C : ℕ→ℝ}{K:Bid.Worth} (b:Bandage X C K) (Y:Bolt A)
open YM.MergeProof
local notation "H"=> Issue.trail Y
set_option quotPrecheck false
local notation "G'"=> Labels.frames G
-- keep chosen Sage. Different d reuse. Legato.
def ClimbsT (X:Factor A) (Y:Bolt A) (N m p:ℕ) (D:GaugeDoor ((Issue.trail Y).rep N p (m+1)) ((Issue.trail Y).rep N p m)):Prop:= ∃ (U:Turf X N m p)(he:(Issue.trail Y).rep N p m=U.output)(h:(Issue.trail Y).rep N p (m+1)=U.inPort), D= duet _ _ _ _ he h U.door
structure Dynamo (X:Factor A) (Y:Bolt A):Prop where
    born : ∀ N p, HasSlots (Y.history N p N).p (Y.history N p N).activities
    samples (N m p:ℕ): m≤ N → HasSlots ((Issue.trail Y).rep N p m).p ((Issue.trail Y).rep N p m).activities
    twinkles : ∀ N m p, m<N →∃ U:Turf X N m p,(Issue.trail Y).rep N p m=U.output ∧ (Issue.trail Y).rep N p (m+1)=U.inPort
include b hG
-- support leaves roots to membership choose orbit finite after current Torus geometry closure. 
lemma chorusT (h:Dynamo X Y) (N p m :ℕ)(hm:m<N): ∃ D:GaugeDoor ((H).rep N p (m+1)) ((H).rep N p m), ClimbsT X Y N m p D ∧ ∀ d:ℕ, d+3 ≤ A.B.a.clock.J m → Tune (localSection G d) H N p (hol G) K m D (waybill A.B.a m):=by
    obtain ⟨U,hb,ht⟩:= h.twinkles N m p hm
    let D:= duet _ _ _ _ hb ht U.door; refine ⟨D,⟨U,hb,ht,rfl⟩,fun d hd=>?_⟩
    let T:= A.B.a; let i:= T.clock.J m; let j:=T.clock.J (m+1); let c:= C j
    have hz:= step_paid A.B.a m; let V:= (H).rep N p (m+1)
    let Y':= Guard.Keeper.sufficient (h.samples N (m+1) p hm)
    let n:= (H).S.side (m+1) p; let A₀ := (0:Site n); let X₀ (i:{i : Support n// A₀∈i}): Wing:=.logKey (Blush.found A₀ i.val i.property)
    let Xk(q : StockTag n): Wing:= Wing.gasKey (cart Y' q)
    let V' := Set.range X₀ ∪ Set.range Xk; have hf: V'.Finite:= (Set.finite_range X₀).union (Set.finite_range Xk)
    obtain ⟨Vj,hV⟩:= clocksHereT hm b.songs b.PStage b.wait (Graces.feet hd b.clock) (h.samples N m p hm.le) b.r U hb ht hG b.tunes b.furthering b.corners b.shape b.clock b.stamp hd (ht ▸ h.samples N (m+1) p hm) -- edit. namespace PriceCompiler?
    have hv := hV V' (fun i hi=> Or.inl ⟨⟨i,hi⟩,rfl⟩)
    have hE: waybill A.B.a m= 2*(Real.exp (V.p.supportExponent)* Cub.title G (M.p.profile j)):= by unfold waybill; rw [params_eq A.B.valid]; have he: V.p=A.B.a.budget (m+1):= Y.choice.represents N p (m+1) hm|>.vac; rw [he]
    rw [hE]; refine ⟨⟨V',hf,Y',fun i=> Or.inr ⟨i,rfl⟩,Vj,c,_,hv,b.clock.fits H rfl m d (by have hδ:=hd; omega)⟩, sound_duet H N p m hb ht U.door _ (U.opensV hG hm b.r),?_,(glyphBound A.B.a (m+1)).2⟩
    apply mul_nonneg zero_le_two (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans (Cub.title_one ..)))
end Bandage
end YM.PhysicalNext.Repeat.Legato
