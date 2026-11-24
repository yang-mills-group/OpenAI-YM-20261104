import YM.Integration.FVA1Physical.Wilson.FieldRows
import YM.Integration.FVA1Physical.Wilson.DistributedSchedule

/-! All mixed subproducts of a fixed finite physical menu, on the same
arbitrarily long realized trajectory. No geometry or coupling order enters
the choice of the construction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Duel MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Midpoint
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open RGComparison.Core16.Spool RGComparison.Core16.Lumen YM.Integration.FVA1Physical.Round2.Curvature
open scoped Classical Topology BigOperators
variable {G:Gauge} {μ:Type} [Fintype μ] {κ:μ→Type} [∀ a,Fintype (κ a)]
variable (I:∀ a,κ a→Lamp G)

private noncomputable def fieldGate (J:Voice G) (clear:Clear G J) (simple:G.Simple)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) (a:μ) (part:Bool) (p s j:ℕ) : ℝ :=
  if branch:P.Branches K G then
    (eventually_atTop.mp (physical_field_rows (I a) J clear (chart G) (chart_ok G) simple H H' P K branch
      p s H.order H.order part (Nat.cast_nonneg H.order) (margin_pos j))).choose else 0

private noncomputable def fieldMenu (J:Voice G) (clear:Clear G J) (simple:G.Simple)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) : ℝ :=
  ∑ e:μ × Bool × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1),
    |fieldGate I J clear simple H H' P K e.1 e.2.1 e.2.2.1.val e.2.2.2.1.val e.2.2.2.2.val|

private theorem fieldMenu_le (J:Voice G) (clear:Clear G J) (simple:G.Simple)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) (a:μ) (part:Bool) {p s j:ℕ}
    (hp:p ≤ H.order) (hs:s ≤ H.order) (hj:j ≤ H.order) :
    fieldGate I J clear simple H H' P K a part p s j ≤ fieldMenu I J clear simple H H' P K := by
  let e:μ × Bool × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1):=
    (a,part,⟨p,by omega⟩,⟨s,by omega⟩,⟨j,by omega⟩)
  let v (e:μ × Bool × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1)):=
    fieldGate I J clear simple H H' P K e.1 e.2.1 e.2.2.1.val e.2.2.2.1.val e.2.2.2.2.val
  exact (le_abs_self (v e)).trans (single_le_sum (fun j _=>abs_nonneg (v j)) (mem_univ e))

/-- Any finite menu of field types, including all subproducts with their own
numbers of separate slots. Both physical components and every fixed
perturbative order share the Run and the realized vacuum. The power η and
the support and derivative order may all be selected after the Run. -/
theorem all_orders_physical_fields {goal:Qlocal.Schedule.Goal G} (extra:Qlocal.Schedule.Obtainable goal)
    (simple:G.Simple) (b₀:ℝ) (hb:0 < b₀) :
    ∃ (R:Run G) (u:G.ColorIndex), R.family.path.levels.clock.kernel.penalty=b₀ ∧
      goal R.metals R.rolls R.alloy R.kit ∧ R.metals.O=chart G ∧
      ∀ (p s q L:ℕ), 6 ≤ s → ∀ (D η:ℝ), 0 ≤ D → 0 < η →
      ∀ᶠ k:ℕ in atTop, ∀ N n,k ≤ N → ∃ S:Scene R.family.path.levels n (p+1+p),
        Realized R.alloy.B.kin N n k (p+1+p) (Lis.sun G u) S ∧
        ∀ j,k ≤ j → j < N → ∀ (F:Forest (R.family.path.levels.clock.op j n).ratio)
          (v:(R.family.path.levels.clock.op j n).Choices),
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          ∀ (a:μ) (part:Bool) (b:Site A.f) (z:Positions (Primary A.c G)), ‖z‖ ≤ A.fClock*D →
            ∀ o:κ a→Site A.f,(∀ t:Slice (I a),separation b (legs (I a) o t).1 ≤ L*closeN y) →
              ∀ i ≤ p, Vault (address A.F G) {b} (αm y) s q (bulkPoint A z)
                (PowerSeries.coeff i (normalizedRows A R.metals.O (jointFieldBank (I a) A o part) p)) (y^η) := by
  haveI:=simple.nontrivial_color
  have dim:0 < G.lieDim:=by rw [Gauge.lieDim,←G.colorIso.finrank_eq];exact Module.finrank_pos
  let u:G.ColorIndex:=⟨0,dim⟩
  obtain ⟨J,clear⟩:=MSbar.Heath.vocals G
  let gate:=fieldMenu I J clear simple
  have offer:=((extra.also Qlocal.Schedule.fixedWilsonChart_obtainable).also
    (Qlocal.Schedule.selectedThreshold_obtainable (G:=G) gate)).also (Qlocal.Schedule.vacuumInvoice_obtainable simple u J clear)
  obtain ⟨R,penalty,⟨⟨grant,hchart⟩,threshold⟩,invoice⟩:=Run.rampK simple offer b₀ hb
  obtain ⟨docket,_⟩:=Qlocal.Schedule.docket_of_invoice simple R u J invoice
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  refine ⟨R,u,penalty,grant,hchart,?_⟩
  intro p s q L hs D η hD hη
  obtain ⟨d,hd⟩:=exists_nat_ge D
  obtain ⟨ℓ,hℓ⟩:=margin_eventually hη
  let nice:=max (max d L) (max (max ℓ q) (max p s))
  let level:=p+1+p
  filter_upwards [docket.purse s level (level+4) hs (by omega) (by omega),eventually_ge_atTop (R.t nice)]
    with k money cutoff
  intro N n hN
  obtain ⟨⟨S,scene⟩,budget⟩:=money N n hN
  refine ⟨S,scene,?_⟩
  intro j kj jN F v A y a part b z hz o near i hi
  let H:=R.family.path.levels.params j
  let H':=R.family.path.levels.params (j+1)
  let x:=R.family.path.levels.clock.hatBeta j
  have high:nice ≤ H.order:=(Nat.le_succ nice).trans (((R.makes.stages nice).2 j (cutoff.trans kj)).1)
  dsimp only [nice] at high
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch J N n j jN simple (invoice.1 growth).sees
    (fun k'=>invoice.2.1 _ _ (R.alloy.B.valid.pays k') _ (step_paid R.alloy.B.a k'))
  have branch:A.S.patch.Branches A.S.kernel G:=season.bends.1
  have cover:fieldGate I J clear simple H H' A.S.patch A.S.kernel a part p s ℓ ≤ x:=
    (fieldMenu_le I J clear simple _ _ _ _ a part (by omega) (by omega) (by omega)).trans (threshold j n)
  rw [fieldGate,dif_pos branch] at cover
  have take:=(eventually_atTop.mp (physical_field_rows (I a) J clear (chart G) (chart_ok G) simple
    H H' A.S.patch A.S.kernel branch p s H.order H.order part (Nat.cast_nonneg H.order) (margin_pos ℓ))).choose_spec x cover
  have g0:0 ≤ A.fClock:=by change 0 ≤ (Real.sqrt _)⁻¹; positivity
  have widen:=hz.trans (mul_le_mul_of_nonneg_left (hd.trans (Nat.cast_le.mpr (by omega : d ≤ H.order))) g0)
  have block:tip G A.S.patch.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  have use:=take A b rfl rfl season
  dsimp only at use
  rw [block] at use
  have j₁:=kj.trans (Nat.le_succ j)
  have trend:=(scene.budget (j+1) jN j₁).1
  have wedge:=(budget S scene).2.2 (j+1) j₁ jN
  have out:=use trend.bond trend.plane wedge z widen o
    (fun t=>(near t).trans (Nat.mul_le_mul_right _ (by omega : L ≤ H.order))) i hi
  change R.metals.O=chart G at hchart
  rw [hchart]
  exact Quote.widen out (Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed (j+1)).le hℓ) (by omega)

end YM.Integration.FVA1Physical.Wilson
