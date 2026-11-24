import YM.Integration.WilsonVacuumPreResetDatedCourse

/-! The exact original bare top in the funded unmarked layout. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDatedBirth
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 FreeResolvent WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Winding WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Mosaic
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedRay
open WilsonVacuumPreResetOriginalOutput Marker Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G:Gauge}(R:Run G)

open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (MassCall)
open AllOrder.Floe.Step
open AllOrder.Ker Primitives.TwoWave.RealSlice

open WilsonVacuumPreResetDatedDeposit (Issued)
open FVA1Physical.TwoReset (AffineMass)
open PertExtension.Series PowerSeries
open AllOrder AllOrder.Floe

open WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonVacuumPreResetTorusGrade (evaluated)
open FVA1Physical.TwoReset (massJets)

private theorem neutral : pace (1:Cost)=1:=by
  have u:constantCoeff (1:Cost)=1:=map_one _
  have sq:(pace (1:Cost))^2=1:=by simpa only [one_mul] using pace_tax u
  rcases sq_eq_one_iff.mp sq with h|h
  · exact h
  · have cc:=pace_cc u
    rw [h,map_neg,map_one] at cc
    norm_num at cc

private theorem mix_neutral {n:Side}(P:PChart G n):mix (1:Cost) P=P:=by
  classical
  funext j r
  rw [mix,Finset.sum_eq_single j]
  · simp [coeff_one]
  · intro b hb ne
    have ht:b≤j:=by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hb
    have diff:j-b≠0:=by omega
    simp [coeff_one,diff]
  · simp

theorem whole {N e:ℕ}{Z:SeriesA G}{σ C:ℝ}(D:Issued R N N e Z σ C)
    (n:Side){t:ℕ}(ht:t≤e+2):
    (front (R.alloy.B.kin.path N N) ((levels R).params N).clip n+sands Z n) t=
      sprig (eWilson (G:=G) (c:=n)) 2 t:=by
  classical
  funext q
  cases q with
  | zero=>
    let P:=R.family.path.rep N 0 N
    have bought:=front_full (R.makes.wilson.represents N 0 N (Nat.le_refl N)).good.paths n
    have hp:P.path=R.alloy.B.kin.path N N:=(RunFormalChain.fromRun R).selected N 0 N (Nat.le_refl N)
    have hc:P.clip=((levels R).params N).clip:=(RunFormalChain.fromRun R).clips N 0 N (Nat.le_refl N)
    change front P.path P.clip n=_ at bought
    rw [hp,hc] at bought
    simp only [Pi.add_apply,bought,Pi.smul_apply,sands_zero_v,sprig,shine_dark (k:=2+t) (n:=0) (by omega),add_zero,smul_zero]
  | succ q=>
    rw [D.periodic t (by omega) n q]
    unfold actionW
    rw [story_top]
    change lagoon ((lop (moon G)) t (q+1)) n=_
    simpa only [lop,Nat.succ_ne_zero,if_false] using (moon_wrap G t q n).symm

theorem original {N e:ℕ}{Z:SeriesA G}{σ C:ℝ}(D:Issued R N N e Z σ C)
    {t:ℕ}(ht:t≤e+2)(n:Side):
    massJets R N N e (bank Z) t n=PertExtension.Series.Radial.jet (Wilson.energy ∘ Stationary.input G n) (t+2):=by
  funext x
  let K:=R.alloy.B.kin.path N N
  let B:=((levels R).params N).clip
  have decl:=WilsonVacuumPreResetTorusRegradedAction.original (1:Cost) (map_one _) K B Z
    D.positive D.purchase D.lower ht x
  have coin:Tested.term ((1:Cost)-1)=(0:Pace.Coin):=by
    funext l
    simp [Tested.term]
  rw [coin,neutral,mix_neutral] at decl
  change Pace.grouping 0 (bank Z) (Step.tape (e+2)) B K t n x=_
  rw [decl]
  have same:evaluated (front K B n+sands Z n) t x=evaluated (sprig (eWilson (G:=G) (c:=n)) 2) t x:=by
    simp only [evaluated,Blue.flash,PowerSeries.coeff_mk,whole R D n ht,K,B]
  rw [same,WilsonVacuumPreResetTorusDepositJet.sprouted]
  have native:eWilson (G:=G) (c:=n)=Wilson.energy ∘ Stationary.input G n:=by
    funext b
    simp only [eWilson,Function.comp_apply,mantle_input]
  rw [native,Nat.add_comm]

end YM.Integration.WilsonVacuumPreResetDatedBirth
