import YM.Integration.WilsonPhysicalThermalWickTail
import YM.Integration.WilsonPhysicalThermalWickFineGain
import YM.Integration.WilsonPhysicalThermalWickPosted

/-! A single charge chosen at fixed raw nominated slots, before the physical
cutoff, period and all original sites and held directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickCalendar
open Lattice Wilson RG Labels Filter Next.Rank Next.Rank.Rise Next.Rank.Perch Next.Rank.Glimmer
open Next.Rank.Common Next.Rank.Normal Next.Rank.Configuration Next.Rank.Atlas
open scoped Classical BigOperators Topology
variable {G:Gauge}{d θ:ℕ}

def Bought (F:Fin 2→Label G d)(L s:ℝ)(θ:ℕ):Prop:=
  ∀S:Finset (Fin 2),
    bill L s*(S.card*bill (-L-2) s*(WilsonPhysicalThermalWickSurplus.cost F+bill (-L-2) s)^S.card*
      priced (bill (fuel θ 2) s) (2*θ))≤bill (-3/2) s ∧
    coin (pot S (fun i=>thawKey (F i)))*
      (WilsonPhysicalThermalWickGain.error θ s*priced (bill (fuel θ 2) s+WilsonPhysicalThermalWickGain.error θ s) (2*d))+
        bill (-3/2) s≤bill (-127/128) s

theorem original (F:Fin 2→Label G d)(L:ℝ)(hL:0≤L)(shelf:100*(d+1)≤θ):
    ∀ᶠ s:ℝ in atTop,Bought F L s θ:=by
  have hc:1≤WilsonPhysicalThermalWickSurplus.cost F:=
    le_add_of_nonneg_left (Finset.sum_nonneg fun i _=>Rise.sign _ _ zero_le_one)
  have all:∀ᶠ s:ℝ in atTop,∀S:Finset (Fin 2),coin (pot S (fun i=>thawKey (F i)))*
      (WilsonPhysicalThermalWickGain.error θ s*priced (bill (fuel θ 2) s+WilsonPhysicalThermalWickGain.error θ s) (2*d))+
        bill (-3/2) s≤bill (-127/128) s:=Filter.eventually_all.2 fun S=>
    WilsonPhysicalThermalWickFineGain.original d θ shelf _ (Rise.sign _ _ zero_le_one)
  filter_upwards [WilsonPhysicalThermalWickTail.original 2 θ _ L hc hL,all] with s tail high
  exact fun S=>⟨tail S.card (by simpa using Finset.card_le_univ S),high S⟩

end YM.Integration.WilsonPhysicalThermalWickCalendar
end
