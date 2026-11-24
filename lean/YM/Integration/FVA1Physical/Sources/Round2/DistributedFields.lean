import YM.Integration.FVA1Physical.Sources.Round2.FieldVault
import YM.Integration.FVA1Physical.Wilson.DistributedSchedule

/-! Volume-independent removal of the exterior for every formal coefficient of
the actual mixed physical stencil bank under the distributed Wilson action. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set Finset Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open FVA2.CityHistory PertExtension.Chart FormalOPE.RG10.MultiGauge
open MSbar MSbar.Whisk MSbar.Bout MSbar.Cacao MSbar.Lis MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Bakery
open Push.Uniform Next.SectorChange YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

def jointSlot {c f : Side} (S : StepData c f) (F : Forest S.ratio) (o : ι→Site f)
    (j : Wire G ↥(activeSlots J S F o)) : Joint F G := Sum.inr (slotEdge J S F o j.1,j.2)

def jointFieldBank (A : Mosaic.Issue G) (o : ι→Site A.f) (part : Bool) : PowerSeries (Pot (Joint A.F G)) :=
  PowerSeries.mk fun i=>MvPolynomial.rename (jointSlot J A.S A.F o)
    (lampRow J part (activeSlots J A.S A.F o) i)

/-- All mixed source rows are those of the independently constructed FVA2 source.
The formal coefficient argument takes its coarse/free coordinates in the native joint
indexing (coarse coordinates do not enter a top physical stencil). -/
theorem joint_seed (A : Mosaic.Issue G) (o : ι→Site A.f) (part : Bool) (n : ℕ)
    (v : FVA2.CityHistory.Future G A.S A.F × FVA2.CityHistory.Pins G A.c) (coarse : Primary A.c G→ℝ) :
    PowerSeries.coeff n (Stack.read v
      (Stack.rise (stencilSignal A.S A.F J o part))) =
      MvPolynomial.eval (fun i:Joint A.F G => Sum.elim coarse (fun e=>v.1 e.1 e.2) i)
        (PowerSeries.coeff n (jointFieldBank J A o part)) := by
  rw [jointFieldBank,PowerSeries.coeff_mk,MvPolynomial.eval_rename]
  exact read_seed_row J A.S A.F o part n v

/-- Every actual physical field bank has subpower rooted complete polynomial price.
The high-coupling cutoff precedes the torus, native forest, field positions and the
mode of the derivative. The finite shape may contain coincident or repeated slots. -/
theorem field_vault_subpower (p s m L : ℕ) (part : Bool) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ y:ℝ in atTop, ∀ (A : Mosaic.Issue G) (o : ι→Site A.f) (b : Site A.f),
      (∀ j:Slice J, separation b (legs J o j).1≤L*closeN y) → ∀ n≤p,
      Vault (address A.F G) {b} (αm y) s m 0 (PowerSeries.coeff n (jointFieldBank J A o part)) (y^ε) ∧
      (PowerSeries.coeff n (jointFieldBank J A o part)).totalDegree≤n := by
  have rise : Tendsto (fun y:ℝ=>y) atTop atTop:=tendsto_id
  let weight:=fun y:ℝ=>liftW (αm y) s (L*closeN y)
  have rate : Mosaic.Run atTop (fun y:ℝ=>y) weight 0 := by
    simpa only [one_mul] using (Mosaic.Issue.nearB rise 1 zero_lt_one s L).2
  choose B e pos native using fun (u : Finset (Slice J)) (i : Fin (p+1))=>
    fixed_polynomial_vault (lampRow J part u i.val) m
  have scheduled (u : Finset (Slice J)) (i : Fin (p+1)):
      ∀ᶠ y:ℝ in atTop, B u i*(weight y)^(e u i) ≤ y^ε := by
    have h:=(rate.Ypow rise (e u i)).mulK rise (B u i)
    filter_upwards [h ε hε] with y bound
    exact (le_abs_self _).trans bound
  filter_upwards [eventually_all.mpr (fun u:Finset (Slice J)=> eventually_all.mpr (scheduled u))] with y bank
  intro A o b near n hn
  let j:Fin (p+1):=⟨n,by omega⟩
  let u:=activeSlots J A.S A.F o
  have a0 : 0≤αm y:=by unfold αm hatW Alto.flurry;positivity
  have hw:1≤weight y:=w_start a0 s _
  have nr (k : Wire G (↑u)) : liftW (αm y) s (separation b (address A.F G (jointSlot J A.S A.F o k)))≤weight y :=
    w_more (near k.1.val) a0 _
  have vault:=native u j (address A.F G) b (jointSlot J A.S A.F o) s (αm y) (weight y) a0 hw nr
  rw [jointFieldBank,PowerSeries.coeff_mk]
  exact ⟨Quote.widen vault (bank u j) le_rfl, (MvPolynomial.totalDegree_rename_le ..).trans (lampRow_degree J part u n)⟩

/-- Full action and full formal vacuum, including the inherited distributed action
and the Haar/penalty factor. Fixed mixed physical stencil, moving root and marks in
the growing L*closeN collar. No source-vault assumption. -/
theorem distributed_fields (V : Voice G) (clear : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' : RG.Stage) (P : Patch)
    (K : KernelChoices) (branch : P.Branches K G) (p s q L : ℕ) (part : Bool)
    {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season V H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ (o : ι→Site A.f), (∀ j:Slice J, separation b (legs J o j).1 ≤ L*closeN y) →
      let src:=jointFieldBank J A o part
      ∀ U∈hotel A.F (boxX y b) (boxY y b) V (represent (tint G (Exterior.Body 1 A.c) z))
        (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y),
      ∀ i ≤ p, |PowerSeries.coeff i (bulkColumn A χ z src p) -
        PowerSeries.coeff i (innerColumn A χ V y z b U src p)| ≤ y^(-(q:ℝ)) := by
  have rise:=Work.E09.betaF_growth G P.L
  filter_upwards [distributed_columns V clear χ hχ simple H H' P K branch p s (p+2) q le_rfl hD,
    rise.eventually (field_vault_subpower J p s (p+2) L part (ε:=1) zero_lt_one)] with x offer bank
  intro A z b patch kernel season hz y kind plane wedge o near src U live i hi
  apply offer A z b patch kernel season hz kind plane wedge src _ U live i hi
  intro n hn
  obtain ⟨v,deg⟩:=bank A o b near n hn
  simpa only [Real.rpow_one] using And.intro v (deg.trans (by omega : n≤p+2))

end YM.Integration.FVA1Physical.Round2.Curvature
