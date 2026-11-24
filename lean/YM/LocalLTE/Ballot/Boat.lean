import YM.LocalLTE.Ballot.Breath
import YM.LocalLTE.Ballot.Pane
import YM.LocalLTE.Ballot.Freight
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
variable (hG:G.Simple)
variable (h0:∀ N m n:ℕ,∀ hm:m<N,(U.port N m n hm).ac=p0 ∧ (U.port N m n hm).ranch.allocation.κ=k)
-- strict Treasury.Ph.Require body consumed on actual jobs. ALL compact scales. Origin only here.All frames.Orth at placement after actual.Factory not re-expression leakage.
structure Astonish (U:Harmonics R C W P l) (q r:ℕ)(e:ℝ): Prop where
    ground : ∀ (m:ℕ),∃ K dα:ℕ,∀ (N n:ℕ)(hm:m<N),∃ hP:2*(2*(East.stagnate q (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo* Pressure.radiusB (A.B.a.clock.hatBeta m))) ≤ (A.B.a.S.side m n).val, let Z:= U.port N m n hm;
       ∀ (d:ℕ) (hd:d+3≤ A.B.a.clock.J m), ∀ (X: LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side m n))), let YU0 := Bandage.aperture U.tag N m n Z d hd;
       let D:= U.ore hm; let T':=U.space N m n hm; ∀ i: ((Labels.frames G).level d).Index, i≠0 →
             let z:= Circlet.lark Z.inPort i YU0 D;
             (U.lays d N n m hm|>.core i)=Graces.canvasB d Z z l T' ∧ Mallow.Turf.Diary Z X d T' YU0 D l q K dα r e i hP
include hG h0 hp hr hx
lemma showsP : Astonish U q r e:=by
    constructor; intro m; obtain ⟨K,dα,hK⟩:= votedK (A:=A) hr m; refine ⟨K,dα,fun N n hm=>?_⟩
    let M:= (U.port N m n hm); let I':=A.B.a.clock.J m; let J':= A.B.a.clock.J (m+1); let x₀:= A.B.a.clock.hatBeta m; have he:= step_paid A.B.a m
    have hx0: East.stagnate q (R.target J' I'|>.halo)<l:= by rw [hx]; exact hp
    have hi: (East.stagnate q (R.target J' I'|>.halo))*radiusB x₀<l*radiusB x₀:= mul_lt_mul_of_pos_right hx0 (show 0<radiusB x₀ from (A.B.a.budget m).B_pos)
    have hL:=Legato.lenV (A:=A) hr m n
    have hP: 2*(2*(East.stagnate q (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).halo*Pressure.radiusB (A.B.a.clock.hatBeta m))) ≤ (A.B.a.S.side m n).val:=by change 2*(2*(East.stagnate q (R.target J' I'|>.halo)*radiusB x₀)) ≤ _; change 10*(l*radiusB x₀)< _ at hL; omega
    refine ⟨hP,?_⟩; intro Z d hd x Yb Q' Tb i hi' c
    refine ⟨congr_fun (plantC U hm d hd) i,?_⟩
    have hs: d ≤ I':= (Nat.le_add_right d 3).trans hd
    obtain ⟨hR,hΘ,Hb⟩:= hr.tempo _ _ he _ (A.B.valid.pays m) d hs
    have hY0:= Rain.jersey (A:=A) (m:=m+1); have hM : Z.inPort.p = A.B.a.budget (m+1):= Z.senses.1.point
    let b:= U.tag; have hv := P.choice.represents N n m hm.le|>.good; have hw : (Issue.trail P).rep N n m= Z.output:= U.baptism N m n hm; rw [hw] at hv
    obtain ⟨bY,hD⟩:= Cub.wagesB hm b.songs b.PStage b.wait (Graces.feet hd b.clock) (U.samples N m n hm.le) b.r Z hw (U.charged N m n hm) hG b.tunes b.shape b.clock b.stamp hd Q' Yb i hi' -- possible needs hT.wait.
    have hy: Push.Local.Readable (hol G) (localSection G d) M.output.p (A.B.a.S.side m n) (Cub.title G (X.p.profile I')):=by rw [show Cub.title G (X.p.profile I')=authors A.B.a m from (by unfold authors; rw [params_eq A.B.valid]; rfl)]; exact Graces.livelyCard b.clock hs
    have hh: Push.Local.hitWidth (A.B.a.budget m)*Real.sqrt (A.B.a.clock.forcedAllowance m)≤1:=by rw [Blush.glyph_eq]; exact b.stamp _ _ he _ hs _ (A.B.valid.pays m)|>.2 _ _ (params_eq A.B.valid m) rfl
    obtain ⟨hx1,hx2⟩:= h0 N m n hm
    have h: minSide G d≤ M.inPort.p.B:=by rw [show M.inPort.p= _ from hM]; change minSide G d ≤ radiusB (A.B.a.clock.hatBeta (m+1)); rw [beta_eq A.B.valid]; exact hΘ
    exact Turf.diagnosis Z hm l q J' K dα e hx0 (hx1.symm ▸ hx2.symm ▸ hK) hL hP x d hG b.r Tb hh hv Yb Q' i (Hb _) (hs.trans he.1) hD hy r h hR -- order.
end
end YM.PhysicalNext.Repeat.Legato
