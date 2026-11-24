import YM.Integration.WilsonVacuumPreResetFiniteActionIncome
import YM.Integration.WilsonVacuumPreResetFiniteCovarianceIncome

/-! The complete original finite vacuum and folded cover are compared inside one real Wilson step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMeasuredWindingSlope
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Wick
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Rank Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G:Gauge}

variable (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
set_option quotPrecheck false in
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)
set_option quotPrecheck false in
local notation "b" => (fun j:ℕ=>(R.family.path.levels.blocks j 0).branches)

theorem original (simple:G.Simple) (N j:ℕ)(live:j<N)(n:Side)
    (tag:(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices) (e:ℕ) (B:wire G n→ℝ) (cash:Usage V R.metals.O j):
    let P:=destination V N j
    let F:=Reef.floor (V).clock.kernel P (wood j) n
    let H:=Reef.ferry P (b j) (wood j) n
    let upper:=WilsonVacuumPreResetFiniteIntegral.read R N (j+1) (n*P.patch.L)
    let cover:=Mesa.stone (Dove.model V wood b R.metals.O u N (j+1)) (n*P.patch.L)
    let T:=positive H (Reef.flush F tag R.metals.O upper)
    let C:=positive H (Reef.flush F tag R.metals.O cover)
    let L:=Orb.toInk H (WilsonVacuumPreResetFiniteTilt.lifted F (upper-cover))
    let M:=nimbus cash.gear
    let A:=1+∑i∈Finset.range (e+1),(WilsonVacuumPreResetFiniteLogBudget.fee M B (expan T) i+
      WilsonVacuumPreResetFiniteLogBudget.fee M B (expan C) i)
    let W:=∑k∈Finset.range (e+1),|coeff k (stem ℝ)| * ((e+1:ℝ)*(1+A))^k
    let K:=WilsonVacuumPreResetFiniteActionIncome.cofactor M B
      (WilsonVacuumPreResetFiniteActionIncome.gross B C T e) (expan T-expan C) e
    |MvPolynomial.eval B (coeff e (WilsonVacuumPreResetFiniteIntegral.posted R N j n tag upper-
      WilsonVacuumPreResetFiniteIntegral.posted R N j n tag cover))|≤
        W*K*WilsonVacuumPreResetFiniteActionIncome.changed B L e:=by
  intro P F H upper cover T C L M A W K
  have yes:coeff 0 upper=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing _):=
    WilsonVacuumPreResetFiniteIntegral.head R simple live _
  have dossier:=(Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (i:=j+1) (N:=N) live).toStory
  obtain ⟨s,primitivePrice,hs,hc,hv,-⟩:=colors G (V).clock.kernel.penalty (V).clock.kernel.penalty_pos P.legal
  have free:coeff 0 cover=Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty P.wing _):=
    Mesa.stoned_main hs.le hc.le (hv _).1 dossier.toVivid dossier.ink _
  have yesU:=Reef.consolidate P R.metals.O (b j) (wood j) n R.alloy.B.ratio tag upper yes ((V).clock.adm j)
  have yesC:=Reef.consolidate P R.metals.O (b j) (wood j) n R.alloy.B.ratio tag cover free ((V).clock.adm j)
  have one:1≤M:=le_max_of_le_left (le_max_left ..)
  have pay:=WilsonVacuumPreResetFiniteActionIncome.weight M one B C T (plur H _ yesC) (plur H _ yesU) e
  have move:T-C=L:=by
    change positive H _-positive H _=Orb.toInk H (WilsonVacuumPreResetFiniteTilt.lifted F (upper-cover))
    rw [←WilsonVacuumPreResetFiniteTilt.moved F tag R.metals.O cover upper,map_sub]
    unfold positive
    abel
  rw [move] at pay
  have rated:=WilsonVacuumPreResetFiniteWindingBudget.original R u simple N j live n tag e B M one
    (WilsonVacuumPreResetFiniteCovarianceIncome.original R N j live cash n)
  have hA:0≤A:=by
    have term (Y:Orb.Ink (Pine G _ F) (wire G n))(i:ℕ):0≤WilsonVacuumPreResetFiniteLogBudget.fee M B Y i:=
      mul_nonneg (Rise.sign _ _ zero_le_one) (by unfold Next.Rank.Common.priced;positivity)
    exact add_nonneg zero_le_one (Finset.sum_nonneg fun i _=>add_nonneg (term _ i) (term _ i))
  have pos:0≤W:=Finset.sum_nonneg fun k _=>mul_nonneg (abs_nonneg _) (pow_nonneg (mul_nonneg (by positivity) (by linarith)) _)
  exact rated.trans ((mul_le_mul_of_nonneg_left pay pos).trans_eq (mul_assoc W K _).symm)

end YM.Integration.WilsonVacuumPreResetMeasuredWindingSlope
end
