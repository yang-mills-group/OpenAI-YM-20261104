import YM.Integration.WilsonVacuumPreResetFiniteLogBudget

/-! The complete original finite vacuum and folded cover are compared inside one real Wilson step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteWindingBudget
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Wick
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}

variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun j:ℕ=>(R.family.path.levels.blocks j 0).branches)

/-- The signed incoming change is charged once under the authentic Gaussian. -/
theorem original (simple:G.Simple) (N j:ℕ)(live:j<N)(n:Side)
    (tag:(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices) (e:ℕ) (B:wire G n→ℝ) (M:ℝ) (one:1≤M):
    let P:=destination V N j
    let F:=Reef.floor (V).clock.kernel P (wood j) n
    let H:=Reef.ferry P (b j) (wood j) n
    let upper:=WilsonVacuumPreResetFiniteIntegral.read R N (j+1) (n*P.patch.L)
    let cover:=Mesa.stone (Dove.model V wood b R.metals.O u N (j+1)) (n*P.patch.L)
    let W:=expan (positive H (Reef.flush F tag R.metals.O upper))
    let U:=expan (positive H (Reef.flush F tag R.metals.O cover))
    let A:=1+∑i∈Finset.range (e+1),(WilsonVacuumPreResetFiniteLogBudget.fee M B W i+WilsonVacuumPreResetFiniteLogBudget.fee M B U i)
    let D:=∑i∈Finset.range (e+1),WilsonVacuumPreResetFiniteLogBudget.fee M B (W-U) i
    (∀x y,|H.saddle.q x y|≤M) →
      |MvPolynomial.eval B (coeff e (WilsonVacuumPreResetFiniteIntegral.posted R N j n tag upper-
          WilsonVacuumPreResetFiniteIntegral.posted R N j n tag cover))|≤
        (∑k∈Finset.range (e+1),|coeff k (stem ℝ)| * ((e+1:ℝ)*(1+A))^k)*D:=by
  intro P F H upper cover W U A D paid
  have yes:coeff 0 upper=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing _):=
    WilsonVacuumPreResetFiniteIntegral.head R simple live _
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨s,C,hs,hc,hv,-⟩:=colors G (V).clock.kernel.penalty (V).clock.kernel.penalty_pos P.legal
  have free:coeff 0 cover=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing _):=
    Mesa.stoned_main hs.le hc.le (hv _).1 dossier.toVivid dossier.ink _
  exact WilsonVacuumPreResetFiniteLogBudget.compared H _ _
    (Reef.consolidate P R.metals.O (b j) (wood j) n R.alloy.B.ratio tag cover free ((V).clock.adm j))
    (Reef.consolidate P R.metals.O (b j) (wood j) n R.alloy.B.ratio tag upper yes ((V).clock.adm j))
    M one paid B e

end YM.Integration.WilsonVacuumPreResetFiniteWindingBudget
end
