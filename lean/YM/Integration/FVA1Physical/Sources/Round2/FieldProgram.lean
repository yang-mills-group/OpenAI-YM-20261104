import YM.Integration.FVA1Physical.Sources.Round2.PurchasedFieldTaylor
import YM.Integration.FVA1Physical.Sources.Round2.DistributedFields

/-! The physical field Taylor replacement and the matching independent distributed
coefficient estimates are paid on one and the same physical RG trajectory.
A single fixed mixed stencil template admits moving placements at every stage. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Bakery MSbar.Bakery.Portal
open Push.Uniform Next.SectorChange YM.Integration.FVA1Physical.Wilson
open PhysicalNext.Repeat.Legato Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost
open Next.Foundations MSbar.Midpoint
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

def FieldPrices (A : Mosaic.Issue G) (V : Voice G) (χ : ChartRatio G) (y D η : ℝ)
    (p q L : ℕ) (part : Bool) : Prop :=
  let X:=boxX y;let Y:=boxY y
  ∀ (z : Positions (Primary A.c G)) (b : Site A.f), ‖z‖ ≤ A.fClock*D →
    let idx:=includeX (G:=G) A.F (X b)
    let O:=represent (tint G (Exterior.Body 1 A.c) z);let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
    let HM:=mold A.pre A.F A.v;let area:=hotel A.F (X b) (Y b) V O ν (pillow y) (room y)
    ∀ (o : ι→Site A.f), (∀ l:Slice J, separation b (legs J o l).1 ≤ L*closeN y) →
    ∃ live : ∀ i,slotEdge J A.S A.F o i∈board A.F (X b),
    (∀ (U : Config G A.f) (B : Positions (Primary A.f G)→ℝ),
      let m:=him V A.F (Y b) O ν HM (X b) (linCash A.F z) U ∘ idx
      let E:=interiorEnergy A.S O A.v (chambers A.F (Y b) V O ν) A.pre.beta A.fClock B
      |schurOrbit A V χ y z b B (fun Z=>look part (tally J o Z)) U -
        tiltedTaylor J A.S A.F o (X b) live (Y b) area χ m (pinch idx HM)⁻¹ A.fClock E U part p| ≤ A.fClock^((p:ℝ)+1-η)) ∧
      ∀ U∈area,∀ i ≤ p, |PowerSeries.coeff i (bulkColumn A χ z (jointFieldBank J A o part) p) -
        PowerSeries.coeff i (innerColumn A χ V y z b U (jointFieldBank J A o part) p)| ≤ y^(-(q:ℝ))

theorem field_prices (V : Voice G) (cle : Clear G V) (simple:G.Simple) (H H' : RG.Stage)
    (P : Patch) (K : KernelChoices) (hp:P.Branches K G) (p s q L i : ℕ) (part : Bool) :
    ∀ᶠ x:ℝ in atTop, ∀ A : Mosaic.Issue G, A.S.patch=P → A.S.kernel=K →
      Season V H H' x A.pre A.post A.S (courage G P.L x) → let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      FieldPrices J A V (chart G) y H.order (Wilson.margin i) p q L part := by
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [purchased_field_taylor J V cle (chart G) (chart_ok G) simple H H' P K hp part p
    (Nat.cast_nonneg (α:=ℝ) H.order) (Wilson.margin_pos i) (sub_pos.mp (Wilson.margin_fits p i)),
    distributed_fields J V cle (chart G) (chart_ok G) simple H H' P K hp p s q L part
    (Nat.cast_nonneg (α:=ℝ) H.order),rise.eventually (Work.E01.radiusB_tendsto.eventually_ge_atTop (2*L))]
    with x actual formal wide
  intro A patch kernel season y kind expanse wedge z b hz idx O ν HM area o near
  have inside (l:Slice J) : 2*separation b (legs J o l).1 ≤ spotN y:= by
    have heavy:2*L ≤ radiusB y:=wide
    exact (Nat.mul_le_mul_left 2 (near l)).trans (by
      unfold closeN spotN;rw [pow_succ' (radiusB y) 3,←Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ heavy)
  exact ⟨wires_inside J A.S A.F o y b inside,actual A z b patch kernel season hz o inside,
    formal A z b patch kernel season hz kind expanse wedge o near⟩

private def fieldGate (V : Voice G) (cle : Clear G V) (hG:G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) (p s L i : ℕ) (part : Bool) : ℝ :=
  if ok:P.Branches K G then (eventually_atTop.mp (field_prices J V cle hG H H' P K ok p s H.order L i part)).choose else 0

private abbrev RowIndex (n:ℕ):= Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1) × Bool

private def fieldMenu (V : Voice G) (cle : Clear G V) (hG:G.Simple)
    (H H' : RG.Stage) (P : Patch) (K : KernelChoices) : ℝ :=
  ∑ k:RowIndex H.order,|fieldGate J V cle hG H H' P K k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2|

/-- Single-trajectory, all-fixed-order mixed-field endpoint. The actual and formal
legs refer to the identical forest and scene and to the canonical chart. -/
theorem all_field_prices {goal : Qlocal.Schedule.Goal G} (extra : Qlocal.Schedule.Obtainable goal)
    (hG:G.Simple) (penalty:ℝ) (pos:0<penalty) :
    ∃ (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex) (V : Voice G),
      R.family.path.levels.clock.kernel.penalty=penalty ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ Clear G V ∧ Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      OPE.Therm.Poetry R.family.path.levels ∧
      ∀ (p s q L : ℕ), 6 ≤ s → ∀ (D η : ℝ), 0 ≤ D → 0<η →
      ∀ᶠ k:ℕ in atTop, ∀ N n, k ≤ N → ∃ S:Scene R.family.path.levels n p,
        Realized R.alloy.B.kin N n k p (Lis.sun G u) S ∧
        ∀ j,k ≤ j → j<N → ∀ (F:Forest (R.family.path.levels.clock.op j n).ratio)
          (v:(R.family.path.levels.clock.op j n).Choices) (part:Bool),
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          FieldPrices J A V R.metals.O y D η p q L part := by
  haveI:=hG.nontrivial_color
  have degree : 0<G.lieDim := by rw [Gauge.lieDim,←G.colorIso.finrank_eq]; exact Module.finrank_pos
  let u:G.ColorIndex:=⟨0,degree⟩
  obtain ⟨V,cle⟩:=MSbar.Heath.vocals G
  let offer:=((extra.also Qlocal.Schedule.fixedWilsonChart_obtainable).also
    (Qlocal.Schedule.selectedThreshold_obtainable (G:=G) (fieldMenu J V cle hG))).also
    (Qlocal.Schedule.vacuumInvoice_obtainable hG u V cle)
  obtain ⟨R,pen,⟨⟨grant,frame⟩,threshold⟩,invoice⟩:=PhysicalNext.Repeat.Legato.Run.rampK hG offer penalty pos
  obtain ⟨docket,poetry⟩:=Qlocal.Schedule.docket_of_invoice hG R u V invoice
  have growth : Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hi
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hi).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  refine ⟨R,u,V,pen,grant,frame,cle,docket,poetry,?_⟩
  intro p s q L hs D η hD hη
  obtain ⟨d,hd⟩:=exists_nat_ge D
  obtain ⟨i,hi⟩:=Wilson.margin_eventually hη
  let demand:=d+q+p+s+L+i
  filter_upwards [docket.purse s p (p+4) hs (by omega) (by omega),eventually_ge_atTop (R.t demand),
    actual_clock_small R.family.path (q:=1) zero_lt_one zero_lt_one hG R.T.choice]
    with k funded menu unit
  intro N n kn
  obtain ⟨⟨S,scene⟩,budget⟩:=funded N n kn
  refine ⟨S,scene,?_⟩
  intro j kj jN F v part A y
  let H:=R.family.path.levels.params j;let H':=R.family.path.levels.params (j+1)
  let x:=R.family.path.levels.clock.hatBeta j
  have order : demand ≤ H.order := (Nat.le_succ demand).trans (((R.makes.stages demand).2 j (menu.trans kj)).1)
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN hG (invoice.1 growth).sees
    (fun k'=>invoice.2.1 _ _ (R.alloy.B.valid.pays k') _ (step_paid R.alloy.B.a k'))
  have branch : A.S.patch.Branches A.S.kernel G:=season.bends.1
  dsimp only [demand] at order
  let row:RowIndex H.order:=(⟨p,by omega⟩,⟨s,by omega⟩,⟨L,by omega⟩,⟨i,by omega⟩,part)
  let price:=fun r:RowIndex H.order => fieldGate J V cle hG H H' A.S.patch A.S.kernel r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
  have gate : fieldGate J V cle hG H H' A.S.patch A.S.kernel p s L i part ≤ x:=
    (le_abs_self (price row)).trans ((single_le_sum (fun r _=>abs_nonneg (price r)) (mem_univ row)).trans (threshold j n))
  rw [fieldGate,dif_pos branch] at gate
  have take:=(eventually_atTop.mp (field_prices J V cle hG H H' A.S.patch A.S.kernel branch p s H.order L i part)).choose_spec x gate A rfl rfl season
  have height:tip G A.S.patch.L x=y := (Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  rw [height] at take
  have j₁:=kj.trans (Nat.le_succ j)
  have trend:=(scene.budget (j+1) jN j₁).1
  have wedge:=(budget S scene).2.2 (j+1) j₁ jN
  have clock0:0<A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos
    (zero_lt_one.trans (R.family.path.levels.fits.delayed (j+1)))).trans_le (R.T.choice.represents N n (j+1) jN).band.1))
  have small:=unit (j+1) j₁ N n jN
  change A.fClock^(1:ℝ) ≤ 1 at small
  rw [Real.rpow_one] at small
  have physicalPrice:=Real.rpow_le_rpow_of_exponent_ge clock0 small (sub_le_sub_left hi ((p:ℝ)+1))
  have qq : q ≤ H.order:=by omega
  have formalPrice:=Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed (j+1)).le
    (neg_le_neg (Nat.cast_le.mpr qq : (q:ℝ) ≤ H.order))
  change R.metals.O=chart G at frame
  rw [frame]
  intro z b hz idx O ν HM area o near
  obtain ⟨live,physical,formal⟩:=take trend.bond trend.plane wedge z b
    (hz.trans (mul_le_mul_of_nonneg_left (hd.trans (Nat.cast_le.mpr (by omega:d ≤ H.order))) clock0.le)) o near
  exact ⟨live,fun U B=>(physical U B).trans physicalPrice,fun U hU t ht=>(formal U hU t ht).trans formalPrice⟩

end YM.Integration.FVA1Physical.Round2.Curvature
