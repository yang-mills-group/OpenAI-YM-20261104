import YM.Integration.WilsonPositionProgramTrialPublicSticker
import YM.Integration.WilsonOriginalPublicNodalTestedRoster
import YM.Integration.WilsonIndependentMatchedOpeningComposite

/-! The fitted original salary and its actual test are paid once per occupied vertex.
The received ordinary word keeps its genuine subface and arbitrary deleted coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicPaidFace
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil PertExtension RegulatorIR RegulatorIR.Cluster XSpace XSpace.Rose
open PhysicalNext.Repeat.Legato IndependentSourcePathFamily
open WilsonIndependentMatchedOpeningRoster (field)
open WilsonIndependentMatchedOpeningPayment (affiled)
open WilsonIndependentRawPhysicalFaces (ordered)
open WilsonReceivedDepositedVerseCensus (ordinary)
open WilsonOriginalPublicNodalTestedRoster (cash)
open scoped Classical BigOperators

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(W:Initialize G)
    (D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(o:I → Cover)
local notation "F" i:max => R.family.labels.level (d i)
variable (S:Finset I)(fill:∀i,(F i).Index)(v:∀i,(F i).Coeff)(φ:I→ℂ→L[ℝ]ℝ)

def key (S:Finset I)(fill:∀i,(F i).Index)(b:∀i:S,(F i).Index)(i:I):(F i).Index:=
  if h:i∈S then b ⟨i,h⟩ else fill i

def amount (v:∀i,(F i).Coeff)(φ:I→ℂ→L[ℝ]ℝ)(i:I)(j:(F i).Index):ℝ:=φ i (v i j)
def cost (κ:(i:I)→Knob (D i))(pt:I→Chamber)(v:∀i,(F i).Coeff)(φ:I→ℂ→L[ℝ]ℝ)
    (A:Case D)(i:I)(j:(F i).Index):Cost:=
  PowerSeries.C (amount R d v φ i j)*(PowerSeries.C (claim (D i) (κ i) (pt i) (A i))*
    (PowerSeries.X:Cost)^((F i).grades j).2)

def originalRow (D d:I→ℕ)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(o:I → Cover)
    (S:Finset I)(fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)(φ:I→ℂ→L[ℝ]ℝ)(A:Case D):Era G ℝ:=
  ∑b:((i:S)→(R.family.labels.level (d i)).Index),(∏i:S,amount R d v φ i (b i)) •
    ordinary (WilsonOlderFreshSoftFigures.stencil R D d (key R d S fill b) κ pt o) A S

def columns (D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)(κ:(i:I)→Knob (D i))
    (pt:I→Chamber)(o:I → Cover)(S:Finset I)[Nonempty S](v:∀i,(R.family.labels.level (d i)).Coeff)(φ:I→ℂ→L[ℝ]ℝ)
    (A:Case D):Era G ℝ:=
  ∑b:((i:S)→(R.family.labels.level (d i)).Index), affiled (∏i:S,cost R D d κ pt v φ A i (b i))
    (field R W (fun _:S=>false) (fun i:S=>d i) b (fun i:S=>cut i) (fun i:S=>o i) ordered)

theorem entry (R:Run G)(W:Initialize G)(D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(o:I → Cover)(S:Finset I)[Nonempty S]
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(A:Case D)
    (b:∀i:S,(R.family.labels.level (d i)).Index):
    (∏i:S,amount R d v φ i (b i)) • ordinary
      (WilsonOlderFreshSoftFigures.stencil R D d (key R d S fill b) κ pt o) A S=
    affiled (∏i:S,cost R D d κ pt v φ A i (b i))
      (field R W (fun _:S=>false) (fun i:S=>d i) b (fun i:S=>cut i) (fun i:S=>o i) ordered):=by
  rw [WilsonOriginalPublicNodalTestedRoster.original R W D d (key R d S fill b) κ pt cut o A S,
    WilsonIndependentMatchedOpeningComposite.money,map_prod,←Finset.prod_mul_distrib]
  simp [cash,cost,key]

theorem original (R:Run G)(W:Initialize G)(D d:I→ℕ){stamps:I→ℕ}(cut:∀i,d i<stamps i)
    (κ:(i:I)→Knob (D i))(pt:I→Chamber)(o:I → Cover)(S:Finset I)[Nonempty S]
    (fill:∀i,(R.family.labels.level (d i)).Index)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (φ:I→ℂ→L[ℝ]ℝ)(A:Case D):
    originalRow R D d κ pt o S fill v φ A=columns R W D d cut κ pt o S v φ A:=
  Finset.sum_congr rfl (fun b _=>entry R W D d cut κ pt o S fill v φ A b)

end YM.Integration.WilsonPositionProgramTrialPublicPaidFace
end
