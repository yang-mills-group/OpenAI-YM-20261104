import YM.Integration.WilsonPhysicalThermalWickSurplus
import YM.TraceExtension.Prom.Front.West.Mooncake

/-! A booking on the given original wire, both its real terminal heating stamps,
and the finite roster of prescribed (unscaled) group polynomials. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalThermalWickBooking
open Lattice Wilson RG Labels Function
open Next.Rank Next.Rank.Atlas Next.Rank.Station Next.Rank.Perch Next.Rank.Glimmer Next.Rank.Particle
open Next.Rank.Prayer Next.Rank.Beamer Next.Rank.Configuration Next.Rank.Common Next.Rank.Normal
open Marker Glyph Exponential Cells
open scoped BigOperators Classical
variable {G:Gauge}{C:Family G}{d k N p θ:ℕ}{d0:Fin 2→ℕ}(v:(i:Fin 2)→C.label (d0 i))
    (hY:∀i,d0 i≤d){b:ℝ}{Z:(i:Fin 2)→Heater C k (d0 i)}{T:(i:Fin 2)→Module.End ℂ (C.label (d0 i))}
local notation "A"=>C.path.levels
local notation "s"=>clim A k

theorem original (hN:k≤N)(ink:∀i,Heating C k N p (d0 i) θ (Z i) (T i))
    (H:passingX hY v k θ b)(u:(i:Fin 2)→C.label (d0 i))
    (solved:∀i,Price.Solves C (mag A b k) (d0 i) k N p (T i) (v i) (u i))
    (L:ℝ)(fees:∀i,saves C (d0 i)+L+3≤b):
    let I:trimV (lengthW s) G→Address G:=Subtype.val
    let F:=fun i=>raiseLabel G (hY i) ((C.labels.level (d0 i)).coords.symm (v i))
    let M:=fun _:Fin 2=>features d I (mag A b k)
    let B:=bill (fuel θ 2) s
    ∃ U:Spend 2 θ,U.base=WilsonPhysicalThermalWickSurplus.cost F ∧ U.ξ=bill (-L-2) s ∧ U.B=B ∧
      TollsX U d0 M (fun i=>Z i (u i)) F (mag A b k) (fun i=>bill (b*d0 i+saves C (d0 i)) s) B:=by
  intro I F M B
  obtain ⟨X,_,_,_,h₁⟩:=H N p hN Z T ink u solved
  have e:TollsX X d0 M (fun i=>Z i (u i)) F (bill b s)
      (fun i=>bill (b*d0 i+saves C (d0 i)) s) B:=by rw [←Atlas.mag_bill];exact h₁
  have paid:=WilsonPhysicalThermalWickSurplus.retained (M:=M) B b L s (fun i=>saves C (d0 i)) e fees
  rwa [←Atlas.mag_bill A b k] at paid

end YM.Integration.WilsonPhysicalThermalWickBooking
end
