import YM.Integration.WilsonMarkedFiniteIndependentHistory
import YM.Integration.WilsonMarkedCoverIndependentHistory
import YM.Integration.WilsonConditionalTaylorWheelConnectedReadout

/-! Connected coefficients of both independently filed marked histories, including all proper faces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentConnectedHistory
open Function Filter Lattice Laurent RG Wilson Precision Tree Bloch Exterior
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Mesa Next.Free Stationary Work.F03 Work.F05 Work.F08
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonConditionalTaylorWheelConnectedReadout (read finiteRead logged)
open scoped Classical Topology BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}

private theorem supported {U:Type} (M T:Finset I→Pal ℝ U)(S:Finset I):
    (∀J⊆S,M J=T J)→logged M S=logged T S:=by
  induction S using Finset.strongInductionOn
  case _ S ih=>
    intro face
    by_cases h:S=∅
    · subst S
      rw [logged,dif_pos rfl,logged,dif_pos rfl]
    rw [logged,dif_neg h,logged,dif_neg h,face S (fun _ z=>z)]
    congr 2
    apply Finset.sum_congr rfl
    intro J _
    by_cases w:J⊆S∧J≠S
    · rw [dif_pos w,dif_pos w,ih J (lt_of_le_of_ne w.1 w.2) (fun X sub=>face X (sub.trans w.1)),
        face (S\J) Finset.sdiff_subset]
    · rw [dif_neg w,dif_neg w]

variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀i n,(primary (R.family.path.levels.clock.op i 0).patch R.family.path.levels.clock.kernel n).Choices)

def finite (N b j:ℕ)(K:I→ℕ)(seed:Outerm G D)(x:I → Cover)(A:Case D)(S:Finset I)(n:Side):PChart G n:=
  logged (fun J=>WilsonMarkedFiniteIndependentHistory.moments R u tags N K seed (b-j) j x J (touch A J) n) S

def cover (N b j cap:ℕ)(K:I→ℕ)(seed:Outerm G D)(x:I → Cover)(A:Case D)(S:Finset I):Pot G:=
  logged (fun J=>WilsonMarkedCoverIndependentHistory.moments R u N cap K seed (b-j) j x J (touch A J)) S

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N b j:ℕ}(live:j≤b)(upper:b≤N)(K k:I→ℕ)(seed:Outerm G D)(well:Wellness k seed)(a:Loc G 1)
    (x:I → Cover)(A:Case D)(S:Finset I)(n:Side)(cap:ℕ)(cost:mass k S≤cap):
    let T:=Gears V R.metals.O K k N b j seed x
    finiteRead A S n (T S)=finite R u tags N b j K seed x A S n ∧
    read A S (T S)=cover R u N b j cap K seed x A S:=by
  intro T
  have health:Wellness k (Gears V R.metals.O K k N b j seed):=
    Cog V R.metals.O upper seed well simple R.alloy.B.ratio live
  constructor
  · refine (WilsonConditionalTaylorWheelConnectedReadout.finite T k (health.level' x) (health.quiet' x) A S n).trans ?_
    apply supported
    intro J _
    exact WilsonMarkedFiniteIndependentHistory.original R u tags simple v funded live upper K k seed well x J (touch A J) n
  · refine (WilsonConditionalTaylorWheelConnectedReadout.original T k (health.level' x) (health.quiet' x) A S).trans ?_
    apply supported
    intro J sub
    have fee:mass k J ≤ mass k S:=Finset.sum_le_sum_of_subset sub
    exact WilsonMarkedCoverIndependentHistory.original R u tags simple v funded live upper K k seed well a x J cap (fee.trans cost) (touch A J)

end YM.Integration.WilsonMarkedIndependentConnectedHistory
end
