import YM.Integration.WilsonConditionalTaylorWheelRawVacuum

/-! The original two conventions for the full zeroth-order kinetic
matrix agree on every torus, without choosing a preferred colour. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelClassicalHead
open Function Filter Matrix Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Matrix
variable {G:Gauge}

theorem matrix {c f:Side} {r s:ℕ} (M:Matrix (Body r c) (Body s f) ℝ):
    FreeResolvent.tensor G M=Stationary.patron G M:=by
  apply Stationary.testers
  intro x y
  rw [Stationary.patron_fee]
  apply congrArg (dotProduct x)
  funext z
  exact congrFun (FreeResolvent.component_mul M y z.2.2) (z.1,z.2.1)

theorem algebra {U:Type} [Fintype U] (M:Matrix U U ℝ):
    -Blue.paint 2 (Blue.orbQ M)=Reef.crunch M:=by
  apply MvPolynomial.funext
  intro x
  have h:=Reef.crunch_value M x
  rw [traceP,MvPolynomial.aeval_eq_eval] at h
  rw [map_neg,Blue.orb_eval,h,neg_div]

theorem kernel (R:Run G) (N j:ℕ) (n:Side):
    -Blue.paint 2 (Blue.orbQ (precisionC G n (freeForms R.family.path.levels N j)))=
      Reef.crunch (Reef.kernelP G R.family.path.levels.clock.kernel.penalty (location R.family.path.levels N j) n):=by
  rw [algebra]
  exact congrArg Reef.crunch (matrix (G:=G) _)

theorem recorded (R:Run G) (N j per:ℕ)
    (F:Forest (R.family.path.levels.clock.op j per).ratio)
    (P:PChart G (R.family.side (j+1) per)):
    let V:=R.family.path.levels
    let S:=V.clock.op j per
    let M:=installed S.ratio (predictionA V N j)
    coeff 0 (-flash (winter S F (freeForms V N (j+1)) (freeForms V N j) M R.metals.O P))=
      Reef.crunch (Reef.kernelP G V.clock.kernel.penalty (location V N j) (R.family.side j per)):=by
  intro V S M
  rw [map_neg,Blue.flash,coeff_mk,winter_calm S F _ _ M R.alloy.B.ratio,visible_shine]
  exact kernel R N j (R.family.side j per)

end YM.Integration.WilsonConditionalTaylorWheelClassicalHead
end
