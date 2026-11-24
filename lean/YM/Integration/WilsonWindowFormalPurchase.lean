import YM.Integration.WilsonFundedWindowMenu
import YM.FormalBulk08.Borough.Purchase
import YM.FormalBulk08.First.Dollars
import YM.FormalBulk08.Delphi.Merge
import YM.FormalBulk08.Spigot.Sidelight

/-! Purchase the uniform finite-to-cover estimates of the formal graph at
the length and delay of the physical model. The formal order budget U is
announced before choosing the physical continuum run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonWindowFormalPurchase

open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch Next.Foundations Push.PriceCompiler
open FormalBulk08 WilsonLimitConstruction.FundedCompanySelection

variable {G : Gauge}

def Canonical (U : ℕ → ℕ) : Prediction G := fun {M} {_} {A} _ =>
  let K := M.p.kernel
  let W := Borough.windowBasis G K
  M.O = chart G ∧
  Borough.Evergreens K Spigot.herald (Labels.frames G).level (hol G) (chart G) W A.B.a ∧
  First.Dahlia A.B.a W.width ∧
  Delphi.Jolt K U (Labels.frames G).level (hol G) (fun i => (A.B.a.clock.factor i).val) ∧
  Delphi.Dominoes A.B.a U (Labels.frames G).level (hol G) K

theorem prepaid (U : ℕ → ℕ) (s : Sheet G) (price : MapPrices) :
    WilsonFundedWindowMenu.Prepared (@Canonical G U) s price := by
  intro C E flags programs wages baton
  let K := s.kernel
  let window := Borough.windowBasis G K
  obtain ⟨e,_,old⟩ := Borough.funded_before K window (chart G) (Labels.frames G).level (hol G) (fun _ => 0)
  obtain ⟨n,hen,soil⟩ := Delphi.jolt_raises (Labels.frames G).level (hol G) K U e
  refine ⟨n,?_⟩
  intro l hl D w u Z post scouts pocket θ stages P menu V quarter
  have fine (i : ℕ) : e i ≤ (D.L i).val := (hen i).trans ((hl i).trans (D.large i).need)
  obtain ⟨V₁,h₁,_,counter⟩ := Borough.counter_day K Spigot.herald (Labels.frames G).level
    (hol G) (chart G) window V
  obtain ⟨V₂,h₂,front⟩ := First.till_boost V₁ window.width
  obtain ⟨V₃,h₃,grain⟩ := Delphi.daydom K U (Labels.frames G).level (hol G) V₂
  refine ⟨V₃,h₁.trans (h₂.trans h₃),?_⟩
  intro Y hY bar wait priced B archive origins rank
  dsimp only
  intro η q exchange aux rider booth sheltered works divides
  have grow (i : ℕ) : n i ≤ (B.a.clock.factor i).val := by
    rw [B.valid.lengths]
    exact (hl i).trans (D.large i).need
  exact ⟨rfl,Borough.launch old fine (counter Y (h₂.trans (h₃.trans hY))) B.valid,
    front Y (h₃.trans hY) bar wait B.a B.valid, Delphi.jolt_more soil grow,
    grain Y hY bar wait B.a B.valid⟩

end YM.Integration.WilsonWindowFormalPurchase
end

