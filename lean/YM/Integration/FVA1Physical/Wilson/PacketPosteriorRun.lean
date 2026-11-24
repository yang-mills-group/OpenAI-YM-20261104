import YM.Integration.FVA1Physical.Wilson.PacketPosterior

/-! A common calibrated physical trajectory, with an unrestricted normalized Haar comparison for every admitted inherited packet. -/
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

theorem packet_posterior_on (simple:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (p s m:ℕ) (hs:6 ≤ s) (hm:1 ≤ m) {D η:ℝ} (hD:0 ≤ D) (hη:0 < η) (hp:η < (p:ℝ)+1)
    (threshold:∀ᶠ j:ℕ in atTop,∀ n,fullPacketGate V cle simple p s m hm hD hη hp
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
          BankPaid b y s p m (packetReserve (p+2) m (div_pos (half_pos (half_pos hη)) (by norm_num : 0<(8:ℝ)))) T →
          (PowerSeries.coeff 0 T).totalDegree=0 →
          |expect A.S A.pre (postcard G A.c g Z) (fun w=>clockReading p g T (chartLog g (canoe (S:=A.S) A.F w)))-
            clockReading p g (emittedRows A R.metals.O (enterRows A T) p) Z| ≤ g^((p:ℝ)+1-η) := by
  have hh:=half_pos (half_pos hη)
  have hbound:η/2/2 < (p:ℝ)+1:=(half_lt_self (half_pos hη)).trans ((half_lt_self hη).trans hp)
  have early:∀ᶠ j:ℕ in atTop,∀ n,sharpPacketGate V cle simple p s m hm hD hh hbound
      (R.family.path.levels.params j) (R.family.path.levels.params (j+1))
      (R.family.path.levels.clock.op j n).patch (R.family.path.levels.clock.op j n).kernel ≤
        R.family.path.levels.clock.hatBeta j:=threshold.mono fun j ready n=>(le_max_left ..).trans (ready n)
  have advance:=packet_sharp_on_eventually simple R u V cle frame p s m hs hm hD hh hbound early fields vac
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hi
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hi).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  obtain ⟨since,paid⟩:=eventually_atTop.mp threshold
  filter_upwards [advance,eventually_ge_atTop since] with k offers after N n kN
  obtain ⟨existsScene,offer⟩:=offers N n kN
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN
  let F:=(scene.step j jN kj).choose;let v:=(scene.step j jN kj).choose_spec.choose
  let chain:=RunFormalChain.fromRun R
  let A:=sceneIssue (N:=N) chain S F v
  let H:=R.family.path.levels.params j;let H':=R.family.path.levels.params (j+1)
  let x:=R.family.path.levels.clock.hatBeta j;let y:=R.family.path.levels.clock.hatBeta (j+1)
  obtain ⟨same,point⟩:=offer S scene j kj jN
  refine ⟨same,?_⟩
  intro b Z T narrow bank head
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN simple (vac.1 growth).sees
    (fun i=>vac.2.1 _ _ (R.alloy.B.valid.pays i) _ (step_paid R.alloy.B.a i))
  have br:A.S.patch.Branches A.S.kernel G:=season.bends.1
  have bill:fullPacketGate V cle simple p s m hm hD hη hp H H' A.S.patch A.S.kernel ≤ x:=paid j (after.trans kj) n
  rw [fullPacketGate,dif_pos br] at bill
  have final:=(eventually_atTop.mp (full_packet_release V cle simple H H' A.S.patch A.S.kernel br p m s hD hη hp)).choose_spec x
    ((le_max_right ..).trans bill) A rfl rfl season
  have scale:tip G A.S.patch.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  dsimp only at final
  rw [scale] at final
  apply final Z b narrow T _ _ ((min_le_left ..).trans (by norm_num : (1/4:ℝ)≤1/2)) bank
  exact fun pal=>point b Z T narrow bank head pal true

end YM.Integration.FVA1Physical.Wilson
