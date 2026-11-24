import YM.Integration.FVA1Physical.Round2.FieldEmissionSeason
import YM.Integration.FVA1Physical.Sources.Round2.FieldReadingOn

/-! A common purchase of rooted coefficient bounds before the period, the
forest, the physical placements and independent evaluation points are chosen. -/
set_option autoImplicit false
set_option maxHeartbeats 950000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Next.Foundations
open Function Filter Finset Lattice RG Wilson Precision Exterior Tree
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Lis MSbar.Whisk MSbar.Cacao MSbar.Rolling
open MSbar.CrossH MSbar.Bakery.Film MSbar.Bulk MSbar.Kelvin MSbar.Mosaic
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool
open PhysicalNext.Repeat.Legato Qlocal.Schedule Push.Uniform
open scoped Classical Topology BigOperators
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι→Lamp G)

def emissionGate (V:Voice G) (cle:Clear G V) (hs:G.Simple) (M:MapPrices)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) (p s L h:ℕ) (part:Bool) : ℝ :=
  if ok:P.Branches K G then (eventually_atTop.mp (field_emission_season J V cle (chart G) (chart_ok G)
    hs M H H' P K ok p s H.order L part (Nat.cast_nonneg H.order) (margin_pos h))).choose else 0

def emissionMenu (V:Voice G) (cle:Clear G V) (hs:G.Simple) (M:MapPrices)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) : ℝ :=
  ∑ i:ReadingInputs H.order, |emissionGate J V cle hs M H H' P K i.1 i.2.1 i.2.2.1 i.2.2.2.1 i.2.2.2.2|

abbrev emissionInvoice (V:Voice G) (cle:Clear G V) (hs:G.Simple) : Goal G :=
  mapThreshold (emissionMenu J V cle hs)

theorem emission_bought (V:Voice G) (cle:Clear G V) (hs:G.Simple) (M:MapPrices)
    (H H':RG.Stage) {A:Mosaic.Issue G} (p s q L h:ℕ) (part:Bool)
    (hp:p≤H.order) (hS:s≤H.order) (hq:q≤H.order) (hl:L≤H.order) (hh:h≤H.order)
    {x:ℝ} (receipt:emissionMenu J V cle hs M H H' A.S.patch A.S.kernel ≤ x)
    (season:Season V H H' x A.pre A.post A.S (courage G A.S.patch.L x)) :
    let y:=tip G A.S.patch.L x
    MSbar.Cacao.Kind A.T → MSbar.Cacao.Expanse A.T 1 p →
    MSbar.Alto.Wedge A.T MSbar.Alto.Dean (hatW y) (MSbar.Alto.cWidth y) s p →
    Premier (main A.f A.pre.clip A.pre.path) →
    Critical A.F A.pre.clip A.pre.path A.ρ →
    (MSbar.Bakery.Film.mold A.pre A.F A.v).PosDef →
    (0≤αm y → αm y≤railWidth M A.S.patch →
      MSbar.CrossH.Syrup (address A.F G) (MSbar.Tramp.path A.S.ratio G)
        (αm y) s (poring A.F A.ρ) (railFee G M A.S.patch s)) →
    ∀ (b:Site A.c) (z:Positions (Primary A.c G)), ‖z‖≤H.order →
      ∀ o:ι→Site A.f, (∀ t:Slice J,separation (A.S.ratio.embed b) (legs J o t).1 ≤ L*closeN y) →
      ∀ i≤p, Vault (MSbar.Measuring.chart A.c G) {b} (αm x) s q z
        (PowerSeries.coeff i (emittedRows A (chart G) (jointFieldBank J A o part) p)) (x^(margin h)) := by
  let row:ReadingInputs H.order:=(⟨p,by omega⟩,⟨s,by omega⟩,⟨L,by omega⟩,⟨h,by omega⟩,part)
  let cost:=fun r:ReadingInputs H.order=>emissionGate J V cle hs M H H' A.S.patch A.S.kernel
    r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
  have gate:cost row≤x:=(le_abs_self (cost row)).trans
    ((single_le_sum (fun i _=>abs_nonneg (cost i)) (mem_univ row)).trans receipt)
  have hb:=season.bends.1
  change emissionGate J V cle hs M H H' A.S.patch A.S.kernel p s L h part ≤ x at gate
  rw [emissionGate,dif_pos hb] at gate
  have use:=(eventually_atTop.mp (field_emission_season J V cle (chart G) (chart_ok G) hs M
    H H' A.S.patch A.S.kernel hb p s H.order L part (Nat.cast_nonneg H.order) (margin_pos h))).choose_spec x gate A rfl rfl season
  intro y kind plane wedge prem crit pd rail b z hz o near i hi
  exact Quote.widen (use kind plane wedge prem crit pd rail b z hz o near i hi) le_rfl hq

end YM.Integration.FVA1Physical.Round2.Curvature
