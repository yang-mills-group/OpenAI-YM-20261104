import YM.Integration.FVA1Physical.Wilson.PacketGate

/-! All actual receipts for the inherited packet on any period and cutoff
of the same calibrated construction with two reserve orders. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Qlocal.Schedule RGComparison.Core16.Spool YM.MSbar Push.Uniform
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open scoped Topology BigOperators Classical
variable {G : Gauge}



open YM.Integration.FVA1Physical.Wilson YM.Integration YM.MSbar.Heath
open YM.Wilson Exterior Tree MSbar.Rolling MSbar.Midpoint MSbar.Whisk Pressure

open MSbar.Bakery.Film MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Bulk MSbar.Lis
open YM.Integration.FVA1Physical.Round2.Curvature

theorem packet_sharp_on_eventually (simple:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (p s m:ℕ) (hs:6 ≤ s) (hm:1 ≤ m) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) (hp:η < (p:ℝ)+1)
    (threshold:∀ᶠ j:ℕ in atTop,∀ n,sharpPacketGate V cle simple p s m hm hD hη hp
      (R.family.path.levels.params j) (R.family.path.levels.params (j+1))
      (R.family.path.levels.clock.op j n).patch (R.family.path.levels.clock.op j n).kernel ≤
        R.family.path.levels.clock.hatBeta j)
    (fields:packetInvoice u V R.metals R.rolls R.alloy R.kit)
    (vac:vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    ∀ᶠ k:ℕ in atTop,∀ N n,k ≤ N →
      (∃ S:Scene R.family.path.levels n (p+2),Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n (p+2)) (scene:Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S)
        (j:ℕ) (kj:k ≤ j) (jN:j<N),
        let F:=(scene.step j jN kj).choose;let v:=(scene.step j jN kj).choose_spec.choose
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
        let y:=R.family.path.levels.clock.hatBeta (j+1);let g:=A.fClock
        S.Poly j=A.Zpost R.metals.O ∧
        ∀ (b:Site A.f) (Z:Positions (Primary A.c G)) (T:Nesting G A.f), ‖g•Z‖ ≤ D*room y →
          BankPaid b y s p m (packetReserve (p+2) m (div_pos hη (by norm_num : 0<(8:ℝ)))) T →
          (PowerSeries.coeff 0 T).totalDegree=0 →
          ∀ (pal:Palisade) (copied:Bool) (U:Config G A.f), U∈A.regionX y b Z V pal →
          |A.modelP y b Z pal V (fun w=>clockReading p g T (chartLog g (packetConfig A V y b Z copied w))) U -
            clockReading p g (emittedRows A R.metals.O (enterRows A T) p) Z| ≤ g^((p:ℝ)+1-η) := by
  let r:=p+2
  let d:=m+r+4
  have use:=packet_ports_pinned_on simple R u V fields vac
  have docket:=(docket_of_invoice simple R u V vac).1
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hi
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hi).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  obtain ⟨since,paid⟩:=eventually_atTop.mp threshold
  filter_upwards [use r s d hs (by dsimp [d];omega) (by dsimp [d];omega),
    docket.purse s r d hs (by dsimp [d];omega) (by dsimp [d];omega),eventually_ge_atTop since] with k loc budget ready N n start
  obtain ⟨ex,ports⟩:=loc N n start
  refine ⟨ex,?_⟩
  intro S scene j kj jN
  let F:=(scene.step j jN kj).choose;let v:=(scene.step j jN kj).choose_spec.choose
  let chain:=RunFormalChain.fromRun R
  let A:=sceneIssue (N:=N) chain S F v
  let x:=R.family.path.levels.clock.hatBeta j;let y:=R.family.path.levels.clock.hatBeta (j+1)
  let H:=R.family.path.levels.params j;let H':=R.family.path.levels.params (j+1)
  obtain ⟨reproduces,readings⟩:=ports S scene j kj jN
  refine ⟨reproduces,?_⟩
  intro b Z T hz bank flat
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN simple (vac.1 growth).sees
    (fun i=>vac.2.1 _ _ (R.alloy.B.valid.pays i) _ (step_paid R.alloy.B.a i))
  have branch:A.S.patch.Branches A.S.kernel G:=season.bends.1
  have kj':k ≤ j+1:=by omega
  have bud:=(scene.budget (j+1) jN kj').1
  have wedge:=((budget N n start).2 S scene).2.2 (j+1) kj' jN
  have prem:Premier (Rolling.main A.f A.pre.clip A.pre.path):=by
    change Premier (Rolling.main _ (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path)
    rw [chain.clips N n (j+1) jN,chain.selected N n (j+1) jN];exact bud.quiet
  have crit:Critical A.F A.pre.clip A.pre.path A.ρ:=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [chain.clips N n (j+1) jN,chain.selected N n (j+1) jN];exact (chain.planned.critical N j n jN F).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [chain.clips N n (j+1) jN,chain.selected N n (j+1) jN]
    exact blueprint F v (chain.kin.path N (j+1)) _ branch bud.quiet (chain.post.price _) (chain.planned.gap N j n jN F)
  have price:=gate_packet V cle simple p s m hm hD hη hp H H' A.S.patch A.S.kernel branch
    (x:=x) (paid j (ready.trans kj) n) A b Z T rfl rfl season
  have height:tip G A.S.patch.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  dsimp only at price
  rw [height,←frame] at price
  apply price (zero_lt_one.trans (R.family.path.levels.fits.delayed (j+1))) hz bud.bond bud.plane wedge prem crit pd bank flat
  intro cap
  have sized:m ≤ (d+1)*(r+2):=by
    exact (show m ≤ d+1 by dsimp [d];omega).trans (Nat.le_mul_of_pos_right _ (by omega))
  exact InheritedPort.restrict_degree A R.metals.O V b Z (readings b Z cap) sized

theorem packet_sharp_on (simple:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (p s m:ℕ) (hs:6 ≤ s) (hm:1 ≤ m) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) (hp:η < (p:ℝ)+1)
    (threshold:selectedThreshold (sharpPacketGate V cle simple p s m hm hD hη hp) R.metals R.rolls R.alloy R.kit)
    (fields:packetInvoice u V R.metals R.rolls R.alloy R.kit)
    (vac:vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    ∀ᶠ k:ℕ in atTop,∀ N n,k ≤ N →
      (∃ S:Scene R.family.path.levels n (p+2),Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n (p+2)) (scene:Realized R.alloy.B.kin N n k (p+2) (Lis.sun G u) S)
        (j:ℕ) (kj:k ≤ j) (jN:j<N),
        let F:=(scene.step j jN kj).choose;let v:=(scene.step j jN kj).choose_spec.choose
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
        let y:=R.family.path.levels.clock.hatBeta (j+1);let g:=A.fClock
        S.Poly j=A.Zpost R.metals.O ∧
        ∀ (b:Site A.f) (Z:Positions (Primary A.c G)) (T:Nesting G A.f), ‖g•Z‖ ≤ D*room y →
          BankPaid b y s p m (packetReserve (p+2) m (div_pos hη (by norm_num : 0<(8:ℝ)))) T →
          (PowerSeries.coeff 0 T).totalDegree=0 →
          ∀ (pal:Palisade) (copied:Bool) (U:Config G A.f), U∈A.regionX y b Z V pal →
          |A.modelP y b Z pal V (fun w=>clockReading p g T (chartLog g (packetConfig A V y b Z copied w))) U -
            clockReading p g (emittedRows A R.metals.O (enterRows A T) p) Z| ≤ g^((p:ℝ)+1-η) :=
  packet_sharp_on_eventually simple R u V cle frame p s m hs hm hD hη hp
    (Eventually.of_forall fun j n=>threshold j n) fields vac

end YM.Integration.FVA1Physical.Wilson
