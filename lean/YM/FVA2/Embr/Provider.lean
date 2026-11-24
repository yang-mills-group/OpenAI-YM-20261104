import YM.FVA2.Embr.Packet
import YM.FVA2.Inked.Combined
/-!
# The Fk interface realization and conditional bookkeeping

The constructor uses the same prescription as the formal-to-formal comparison.
The `Steady` instance, obtained via `Habitat`, applies to this finite inversion
prescription. Physical histories, estimates in weighted regional norms and
bounds uniform in size require additional analytic hypotheses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Sync Route Gists Marker Extra.Trajectories
open scoped Classical Topology BigOperators ContDiff
open Arrival RGComparison.Core16 Lumen
variable {G:Gauge} (N:Register.WilsonPrescription G) (i:ℕ)
set_option quotPrecheck false
local notation "E"=> N.chooses i
local notation "N₀"=> (N.run.step i).p.side
local notation "GK"=> (N.chooses i).clock
local notation "T"=> (N.chooses i).T
local notation "q"=> (N.chooses i).clock.loops
local notation "Π"=> Facade.headquarters q
local notation "J"=> N.chart
local notation "c₀"=> (N.chooses i).clock.priced
local notation "Y"=> N.scheme
local notation "F!"=> collared T q N.analyticChart c₀
local notation "F"=> (N.chooses i).F
abbrev FabricOf := (N.chooses i).F

namespace Provision

/-- A compatible Fk construction at the full retained field, with all the needed
`Steady` etc. data. Companion task can fix these once (finite order `V` -- this doesn't
mean new choices of `N`) or state results for any appropriate `Habitat`. -/
structure Puffs (s:G.ColorIndex) (y: Flats G (Bottom (FabricOf N i)))
        (V:ℕ) (Ω:Shelf G Unit (Warm T)) : Prop where
    audit : Habitat T (Gear.sheets GK V) y s Ω
    marks {I:Type} [Fintype I] [DecidableEq I] (R:Census I) (φ:I→Folio G) (U:ℕ)
        (j:Warm T→Site N₀) (ht:∀ u:R.Mode, Folio.asset (Embr.mark R φ u)+ U≤V) (u:Multi.Hot R) :
        let e := fkFrame T J (Gear.sheets GK V) y s Ω j Y R φ
        Through U (FormalOPE.RG10.Word.see u.val (FormalOPE.RG10.Word.logWord e))
          (run (Sync.tint (natural (Bottom F) G) y) (logway R T (q ∘ some) Π (beginOn Y R φ N₀) J F! u))
    points (l:List (Folio G)) (u:ℕ) (ht:Folio.asset l+u ≤ V) (j:Warm T→Site N₀) :
        let P0 := home T (Gear.sheets GK V) y s Ω j
        let H₁ := Fk.read P0 J (tease T s) (lens T y s (Hearth.rad T (Folio.scenario Y N₀ l)))
                            (Folio.asset l)
        Aspiration (Fk.baron P0 (scroll (Folio.scenario Y N₀ l) T y) (Folio.asset l)) H₁ ∧
          H₁ u = PowerSeries.coeff u (Stack.read y (Facade.drive T (q∘some) Π (markValue Y l N₀) J F!).2)
    income (j:Warm T→ Site N₀) (x:Ticket (Flats G N₀)) :
        Through V (PowerSeries.mk (Fk.birth (home T (Gear.sheets GK V) y s Ω j) J))
          (PowerSeries.C (overheadC T q c₀ y J) * Stack.read y (Facade.drive T (q∘some) Π x J F!).1.W)
variable (s:G.ColorIndex)(y:Flats G (Bottom (FabricOf N i)))
lemma ready (V:ℕ)(Ω)(F₀: Habitat T (Gear.sheets GK V) y s Ω): Puffs N i s y V Ω:= by
 let H₀:= N.analyticChart; let hn:= Gear.charges GK V; let h:= Gear.warm GK V
 refine ⟨ F₀,fun {I} _ _ R φ U j hu u=> Embr.genuine_readout («T»:=T) («J»:=J) («Y»:=Y) (s:=s) (Ω:=Ω) (j:=j) (x:=y) (w:=Gear.sheets GK V) q c₀ hn h H₀ R φ F₀ U hu _, fun l u hu j=> ⟨reckons F₀ Y l H₀, Embr.posts F₀ Y l H₀ q c₀ V hn h u hu⟩,fun j x=> ?_⟩
 rw [ ← Facade.avowed (hj:=H₀), Facade.avowed (A:= markValue Y [] N₀) (hj:=H₀)]; exact Embr.income F₀ Y [] H₀ q c₀ V hn h
lemma issues (V:ℕ):∃ Ω,Puffs N i s y V Ω:= by obtain ⟨Ω,h⟩:= Embr.enroll T _ y s c₀ (Gear.charges GK V) ( Gear.warm GK V ); exact ⟨Ω,ready N i s y V Ω h⟩
-- epoch-level converters. symbolic reads support arbitrary other truncation choices Pell
end Provision
end YM.FVA2.Embr
