import YM.Integration.FVA1Physical.Round2.FieldEmissionMenu

/-! The rooted emitted rows of an independent physical field bank, on every
realization at the very order used by the comparisons of actual readings. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open MSbar.Midpoint MSbar.Cacao MSbar.CrossH MSbar.Bakery.Film MSbar.Whisk MSbar.Rolling MSbar.Kelvin MSbar.Lis MSbar.Bulk
open Tree Pressure Push.Uniform Exterior
open MSbar.Mosaic
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

def PinnedEmissions (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex) : Prop :=
  ∀ (p r s q L : ℕ),  p ≤ r → 6 ≤ s → ∀ (D η : ℝ),  0 ≤ D → 0 < η → 
    ∀ᶠ k:ℕ in atTop, ∀ N n,k ≤ N → 
      (∃ S:Scene R.family.path.levels n r,Realized R.alloy.B.kin N n k r (Lis.sun G u) S) ∧
      ∀ (S:Scene R.family.path.levels n r) (scene:Realized R.alloy.B.kin N n k r (Lis.sun G u) S)
        (j:ℕ) (kj:k ≤ j) (jN:j < N),
        let F:=(scene.step j jN kj).choose
        let v:=(scene.step j jN kj).choose_spec.choose
        let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
        let x:=R.family.path.levels.clock.hatBeta j
        let y:=R.family.path.levels.clock.hatBeta (j+1)
        ∀ (b:Site A.c) (z:Positions (Primary A.c G)), ‖z‖ ≤ D → 
          ∀ (o:ι → Site A.f), (∀ t:Slice J,separation (A.S.ratio.embed b) (legs J o t).1 ≤ L*closeN y) → 
          ∀ (part:Bool) (i:ℕ),i ≤ p → Vault (MSbar.Measuring.chart A.c G) {b} (Mosaic.αm x) s q z
            (PowerSeries.coeff i (emittedRows A R.metals.O (jointFieldBank J A o part) p)) (x^η)

theorem pinned_emissions (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex)
    (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (rows:emissionInvoice J V cle hG R.metals R.rolls R.alloy R.kit)
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    PinnedEmissions J R u := by
  obtain ⟨docket,_⟩:=docket_of_invoice hG R u V invoice
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  intro p r s q L pr hs D η hD hη
  obtain ⟨d,hd⟩:=exists_nat_ge D
  obtain ⟨h,marg⟩:=margin_eventually hη
  let demand:=d+p+s+q+L+h
  filter_upwards [docket.purse s r (r+4) hs (by omega) (by omega),eventually_ge_atTop (R.t demand)] with k budget menu N n kN
  obtain ⟨existsScene,paid⟩:=budget N n kN
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN F v A x y
  let Z:=RunFormalChain.fromRun R
  let H:=R.family.path.levels.params j
  have ord:demand ≤ H.order:=(Nat.le_succ demand).trans (((R.makes.stages demand).2 j (menu.trans kj)).1)
  dsimp only [demand] at ord
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN hG (invoice.1 growth).sees
    (fun i=>invoice.2.1 _ _ (R.alloy.B.valid.pays i) _ (step_paid R.alloy.B.a i))
  have je:=kj.trans (Nat.le_succ j)
  have tr:=(scene.budget (j+1) jN je).1
  have wedge:=(paid S scene).2.2 (j+1) je jN
  have height:tip G A.S.patch.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  have land:=emission_bought J V cle hG R.metals.K H (R.family.path.levels.params (j+1)) (A:=A)
  have branch:=season.bends.1
  have prem:Premier (main A.f A.pre.clip A.pre.path):=by
    change Premier (main _ (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path)
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN];exact tr.quiet
  have crit:Critical A.F A.pre.clip A.pre.path A.ρ:=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN];exact (Z.planned.critical N j n jN F).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN]
    exact blueprint F v (Z.kin.path N (j+1)) _ branch tr.quiet (Z.post.price _) (Z.planned.gap N j n jN F)
  intro b z hz o near part i hi
  have use:=land p s q L h part (by omega) (by omega) (by omega) (by omega) (by omega) (x:=x) (rows j n) season
  dsimp only at use
  rw [height] at use
  have plane:Expanse A.T 1 p:=⟨fun a ha=>tr.plane.profile a (ha.trans pr)⟩
  have pieces:Alto.Wedge A.T Alto.Dean (Mosaic.hatW y) (Alto.cWidth y) s p:=⟨fun a ha=>wedge.shares a (ha.trans pr)⟩
  have result:=use tr.bond plane pieces prem crit pd (fun ha small=>selected_land R jN S F v s ha small)
    b z (hz.trans (hd.trans (Nat.cast_le.mpr (by omega : d ≤ H.order)))) o near i hi
  change R.metals.O=chart G at frame
  rw [frame]
  exact Quote.widen result (Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed j).le marg) le_rfl

end YM.Integration.FVA1Physical.Round2.Curvature
