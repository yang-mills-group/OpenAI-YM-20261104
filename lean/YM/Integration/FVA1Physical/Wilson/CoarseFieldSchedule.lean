import YM.Integration.FVA1Physical.Wilson.CoarseRows
import YM.Integration.FVA1Physical.Wilson.CoarseGate

/-! On the selected all-orders physical family, the independently calculated
complete mixed coefficient is already an admissible rooted polynomial on
the next torus. Its allowed power, its differentiated norm, and its physical
origin may all be chosen after fixing the construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {μ:Type} [Fintype μ] {κ:μ→Type} [∀ a,Fintype (κ a)]
variable (I:∀ a,κ a→Lamp G)

theorem all_orders_coarse_fields {goal:Qlocal.Schedule.Goal G} (extra:Qlocal.Schedule.Obtainable goal)
    (simple:G.Simple) (b₀:ℝ) (hb:0 < b₀) :
    ∃ (R:Run G) (u:G.ColorIndex), R.family.path.levels.clock.kernel.penalty=b₀ ∧
      goal R.metals R.rolls R.alloy R.kit ∧ R.metals.O=chart G ∧
      ∀ (p s q L:ℕ), 6 ≤ s → ∀ (D η:ℝ), 0 ≤ D → 0 < η →
      ∀ᶠ k:ℕ in atTop, ∀ N n,k ≤ N → ∃ S:Scene R.family.path.levels n (p+1+p),
        Realized R.alloy.B.kin N n k (p+1+p) (Lis.sun G u) S ∧
        ∀ j,k ≤ j → j < N → ∀ (F:Forest (R.family.path.levels.clock.op j n).ratio)
          (v:(R.family.path.levels.clock.op j n).Choices),
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let x:=R.family.path.levels.clock.hatBeta j
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          ∀ (a:μ) (part:Bool) (b:Site A.c) (z:Positions (Primary A.c G)), ‖z‖ ≤ A.fClock*D →
            ∀ o:κ a→Site A.f,(∀ t:Slice (I a),separation (A.S.ratio.embed b) (legs (I a) o t).1 ≤ L*closeN y) →
              ∀ i ≤ p, let bank:=jointFieldBank (I a) A o part
                let f:=PowerSeries.coeff i (emittedRows A R.metals.O bank p)
                PowerSeries.coeff i (bulkColumn A R.metals.O z bank p)=MvPolynomial.eval (A.fClock⁻¹•z) f ∧
                Vault (Measuring.chart A.c G) {b} (αm x) s q (A.fClock⁻¹•z) f (x^η) := by
  have offer:=extra.also (Qlocal.Schedule.mapThreshold_obtainable (G:=G) (railMenu simple))
  obtain ⟨R,u,cost,⟨other,threshold⟩,chart,held⟩:=all_orders_physical_fields I offer simple b₀ hb
  refine ⟨R,u,cost,other,chart,?_⟩
  intro p s q L hs D η hD hη
  obtain ⟨l,hl⟩:=margin_eventually (half_pos hη)
  let nice:=max l (max q s)
  filter_upwards [held p s q L hs D (margin l) hD (margin_pos l),eventually_ge_atTop (R.t nice)] with k money cut
  intro N n hN
  obtain ⟨S,scene,rows⟩:=money N n hN
  refine ⟨S,scene,?_⟩
  intro j kj jN F v A x y a part b z hz o near i hi bank f
  let Z:=RunFormalChain.fromRun R
  let H:=R.family.path.levels.params j
  let H':=R.family.path.levels.params (j+1)
  have wide:nice ≤ H.order:=(Nat.le_succ nice).trans (((R.makes.stages nice).2 j (cut.trans kj)).1)
  dsimp only [nice] at wide
  have HB:=railMenu_covers simple R.metals.K H H' A.S.patch A.S.kernel (by omega : s≤H.order) (by omega : l≤H.order)
    (x:=x) (threshold j n)
  have block:tip G A.S.patch.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  dsimp only at HB
  rw [block] at HB
  have tr:=(scene.budget (j+1) jN (kj.trans (Nat.le_succ j))).1
  have branch:= (R.family.path.levels.blocks j n).branches
  have prem:Premier (main A.f A.pre.clip A.pre.path):=by
    change Premier (main _ (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path)
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN]; exact tr.quiet
  have crit:Critical A.F A.pre.clip A.pre.path A.ρ:=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN];exact (Z.planned.critical N j n jN F).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN]
    exact blueprint F v (Z.kin.path N (j+1)) _ branch tr.quiet (Z.post.price _) (Z.planned.gap N j n jN F)
  refine ⟨emitted_read A R.metals.O bank p i branch prem crit pd z,?_⟩
  have fund:=rows j kj jN F v a part (A.S.ratio.embed b) z hz o near i hi
  have issued:=selected_land R jN S F v s HB.1 HB.2.1
  have transported:=emitted_rows A R.metals.O bank p i s q branch prem crit pd b z HB.1 HB.2.2.1 issued fund
  exact Quote.widen transported ((HB.2.2.2 q (by omega)).trans
      (Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed j).le (by linarith only [hl]))) le_rfl

end YM.Integration.FVA1Physical.Wilson
