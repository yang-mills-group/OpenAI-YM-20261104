import YM.Integration.WilsonIndependentGroupedInversionMesh
import YM.Price.Intent
import YM.FormalOPE.RG10.OpenSlots.Passenger
import YM.RegulatorIR.Geometry.Guess
import YM.FVA2.BareOrb

/-! Actual centered Wilson stages on the regrouped even inversion board and the original Haar ratio before tree gauge. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentGroupedOrbit
open Lattice RG RG.Supply XSpace Wilson PertExtension FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension.Series.Tested
open WilsonIndependentGroupedInversionMesh (block younger later terminal)
open scoped Classical BigOperators
variable {G:Gauge}

def side (p:Period)(P:Patch)(m:ℕ):Side :=
  ⟨p.side.val*P.L.val^m,Nat.mul_pos p.side.pos (pow_pos P.L.pos _)⟩

theorem even (p:Period)(P:Patch)(m:ℕ) : Even (side p P m).val :=
  even_iff_two_dvd.mpr (dvd_mul_of_dvd_left p.even _)

def step (p:Period)(P:Patch)(K:KernelChoices)(m:ℕ) :
    StepData (side p P m) (side p P (m+1)) :=
  ⟨P,K,by change p.side.val*P.L.val^(m+1)=p.side.val*P.L.val^m*P.L.val; rw [pow_succ,mul_assoc]⟩

def course (p:Period)(P:Patch)(K:KernelChoices)(authorized:P.Branches K G) :
    (m:ℕ) → Fabric G (side p P m)
  | 0 => .endcap _ (even p P 0)
  | m+1 => .layer (step p P K m) authorized (RegulatorIR.Geometry.directive _)
      (even p P (m+1)) (course p P K authorized m)

theorem centered (p:Period)(P:Patch)(K:KernelChoices)(m:ℕ)(x:Site (side p P m)) :
    let S:=step p P K m
    S.withinChoice RegulatorIR.Geometry.invS x (RegulatorIR.Geometry.directive S)=RegulatorIR.Geometry.directive S :=
  RegulatorIR.Geometry.directs _ _

variable (V:XSpace.Run)(u i:ℕ)(hu:0<u)(p:Sheet G)(j:ℕ)(hj:p.first≤j)

def pattern : Patch :=
  ⟨⟨block V u,pow_pos ((by have:=V.large;omega):0<V.ratio) _⟩,j,p.cut.trans hj,
    (WilsonIndependentGroupedInversionMesh.first V u i hu).2.1,
    (WilsonIndependentGroupedInversionMesh.first V u i hu).1⟩

def board : Fabric G (V.step i).p.side := by
  let P:=pattern V u i hu p j hj
  let b:=terminal V u i
  let m:=i/u+(later V i+younger u i)/u
  have exactSide : (V.step i).p.side=side b P m :=
    Subtype.ext (WilsonIndependentGroupedInversionMesh.top V u i)
  exact exactSide.symm ▸ course b P p.kernel (p.has P) m

variable {Y:Period}{F:Fabric G Y.side}(T:Fabric.Cloth F)
    (z:F.Accounts→PowerSeries ℝ)(hz:∀ a,0<PowerSeries.coeff 0 (z a))(unit:z none=1)
    (O:Config G Y.side→ℝ)(valid:Orb.PreTest O)

def paid := OpenSlots.purchase T z hz (Bare.chart_ratio G) (OpenSlots.imprintRoot O)

include unit valid in
/-- The entire normalized response on the conventional tree for every positive intermediate kernel tuning. -/
theorem original (W:Initialize G) : Bare.normalized (W.tree Y) G (FVA2.BareOrb.stencil (W.tree Y) O)=
    FVA2.TaylorWick.into (paid T z hz O) := by
  rw [paid,OpenSlots.diagram T z hz (Bare.chart_ratio G) unit valid,FVA2.BareOrb.diagram_eq _ valid]

include unit valid in
theorem before : Aspiration (Orb.preExpectation O) (fun k=>PowerSeries.coeff k (paid T z hz O)) := by
  rw [paid,OpenSlots.diagram T z hz (Bare.chart_ratio G) unit valid]
  simp only [PowerSeries.coeff_mk]
  exact Orb.before_tree_formula (even_iff_two_dvd.mpr Y.even) (Orb.traySpec G) valid

theorem selected (W:Initialize G) (O:Config G (V.step i).p.side→ℝ)(honest:Orb.PreTest O)
    (z:(board V u i hu p j hj).Accounts→PowerSeries ℝ)(pos:∀ j,0<PowerSeries.coeff 0 (z j))(first:z none=1) :
    let F:=board V u i hu p j hj
    let f:=paid (Fabric.localTruss F) z pos O
    Bare.normalized (W.tree (V.step i).p) G (FVA2.BareOrb.stencil (W.tree (V.step i).p) O)=FVA2.TaylorWick.into f ∧
    Aspiration (Orb.preExpectation O) (fun k=>PowerSeries.coeff k f) :=
  ⟨original _ z pos first O honest W,before _ z pos first O honest⟩

end YM.Integration.WilsonIndependentGroupedOrbit
