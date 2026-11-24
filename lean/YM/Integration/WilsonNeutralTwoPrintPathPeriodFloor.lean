import YM.Integration.WilsonNeutralTwoPrintPathHeldRead
import YM.Integration.WilsonNeutralTwoPrintPathDatedReprint

/-! All proper faces, Laurent degrees and angular ranks of one finite register share a period floor before the original ultraviolet cutoff. -/
noncomputable section
namespace YM.Integration.WilsonNeutralTwoPrintPathPeriodFloor
open Function Filter Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Embroider
open WilsonCoeffUV.Winding WilsonNeutralTwoPrintPathRankFare Precision Laurent
open Stationary AllOrder AllOrder.Floe QuadraticLocal Exterior
open Next.Foundations PhysicalNext.Repeat.Legato FormalBulk08 Tree Bloch Exterior
open scoped BigOperators Classical Topology

variable {G:Gauge}(R:Run G)(j:ℕ)

private theorem grows:Tendsto (fun p:ℕ=>(R.family.side j p).val) atTop atTop:=
  (show StrictMono (fun p:ℕ=>(R.family.side j p).val) from fun _ _ h=>
    Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos).tendsto_atTop

theorem shrinks (α A:ℝ)(ha:0<α):
    Tendsto (fun p:ℕ=>A*catchW (α/512) (R.family.side j p)) atTop (𝓝 0):=by
  have step:Tendsto (fun p:ℕ=>(α/512)*((R.family.side j p).val:ℝ)) atTop atTop:=
    (tendsto_natCast_atTop_atTop.comp (grows R j)).const_mul_atTop (by positivity)
  have wash:=Real.tendsto_exp_neg_atTop_nhds_zero.comp step
  simpa only [catchW,Function.comp_apply,neg_mul,mul_zero] using
    (tendsto_const_nhds (x:=A)).mul wash

theorem original {I:Type}[Fintype I](cap:I→ℕ)(weight:I→ℝ)(α W:I→ℕ→ℝ)
    (hs:∀u r,r≤cap u → 0<α u r){tol:ℝ}(positive:0<tol):
    ∃p₀:ℕ,∀p,p₀≤p → ∀u,
       ((cap u).factorial:ℝ)*weight u*
        ∑r∈range (cap u+1),tariff (Loc G 1) r (α u r) (W u r)*catchW (α u r/512) (R.family.side j p)
        ≤tol:=by
  apply eventually_atTop.1
  apply Filter.eventually_all.2
  intro u
  have vanish:=tendsto_finsetSum (range (cap u+1)) (fun r hr=>
    shrinks R j (α u r) (tariff (Loc G 1) r (α u r) (W u r)) (hs u r (by simpa using hr)))
  simp only [sum_const_zero] at vanish
  have total:=(tendsto_const_nhds (x:=((cap u).factorial:ℝ)*weight u)).mul vanish
  simp only [mul_zero] at total
  exact (total.eventually_lt_const positive).mono fun _ h=>le_of_lt h

end YM.Integration.WilsonNeutralTwoPrintPathPeriodFloor
end
