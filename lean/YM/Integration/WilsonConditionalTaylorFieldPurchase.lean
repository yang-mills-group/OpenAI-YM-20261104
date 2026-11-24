import YM.Integration.WilsonConditionalTaylorCalendar
import YM.Integration.WilsonWindowBookPurchase
import YM.Integration.FVA1Physical.Sources.Round2.FieldInvoice

/-! Purchase every finite original source roster on one physical trajectory.
The true field supplier is charged for the first finitely many templates at
each attained block scale, before the period or any translation has been chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorFieldPurchase

open Function Filter Set Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open FVA1Physical.Round2.Curvature RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open Push WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology BigOperators

variable {G : Gauge} {I : ℕ → Type} [∀ t, Fintype (I t)]

/-- Exactly the original `AllFieldLoad.pay` at or after the indicated code.
No one physical clock entry must pay all unbounded source lists at once. -/
def Due (J : ∀ t, I t → Lamp G) (u : G.ColorIndex) (V : Voice G) : Prediction G := fun {M} {_} {A} _ =>
  ∀ (t j n s p m L : ℕ), let g := A.B.a.clock.J (j+1)
  t ≤ g → L ≤ g → 6 ≤ s → s ≤ g → 4 ≤ m → m ≤ g → p+2 ≤ m →
    (A.B.a.clock.op j n).patch.Branches M.p.kernel G →
    ∃ (B : Uniform.Before G (A.B.a.params (j+1)).width (A.B.a.params (j+1)).paths g M.p.kernel (p+3)),
      FieldSent M.O M.K p s m g (A.B.a.clock.J j) (A.B.a.params j) (A.B.a.params (j+1))
        (A.B.a.clock.op j n).patch M.p.kernel B u V (J t) L (A.B.a.clock.hatBeta j)

theorem prepaid (J : ∀ t, I t → Lamp G) (hG : G.Simple) (u : G.ColorIndex) (V : Voice G)
    (cle : Clear G V) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Due G I _ J u V) s price := by
  intro C E flags programs wages baton
  obtain ⟨p,hb⟩ := MSbar.Ballet.paymentP (G:=G) price
  refine ⟨p,?_⟩
  intro l hl rolls w ν Z post scouts pocket θ records cost menu start quarter
  let M := WilsonWindowBookPurchase.raised s price l
  have ready := fun i => hb i (rolls.L i) ((hl i).trans (rolls.large i).need)
  let limits (n : ℕ) := (Finset.range (n+1)).eventually_all.mpr (fun t (_ : t ∈ Finset.range (n+1)) =>
    (Finset.range (n+1)).eventually_all.mpr (fun L (_ : L ∈ Finset.range (n+1)) =>
      field_tenor M.O M.K u V (J t) L hG (chart_ok G) ready cle n))
  choose f hf using fun n => eventually_atTop.mp (limits n)
  let W : Delays θ := {start with betaEntry:=fun i => max (start.betaEntry i) (f i)}
  refine ⟨W,⟨fun _ => le_max_left ..,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro W' hW bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides t j n s' p' m L g t₀ hL hS hv hm hz hP hk
  let op := B.a.clock.op j n
  have profiles (i : ℕ) : B.a.params i = M.p.profile (B.a.clock.J i) := by
    unfold Levels.params Calendar.params
    rw [B.valid.stage]
  rw [profiles j,profiles (j+1)]
  refine hf g _ ((le_max_right (start.betaEntry g) _).trans ((hW.beta g).trans (B.valid.pays j)))
    t (mem_range.mpr (Nat.lt_succ_of_le t₀)) L (mem_range.mpr (Nat.lt_succ_of_le hL))
    s' hv m hz p' (by omega) (B.a.clock.J j) (B.a.fits.mono (Nat.le_succ j)) hS hm hP op.patch rfl ?_ hk
  change B.a.S.block j = rolls.L g
  rw [←B.a.fits.sameFactor,B.valid.lengths]

end YM.Integration.WilsonConditionalTaylorFieldPurchase
end

