import YM.Integration.WilsonReceivedChronologicalRosterRanks
import YM.Integration.WilsonIndependentCapturedPages

/-! Before the moving stop is elected, choose the individual finite orders so
that every participating registrar asks for precisely the same infrared depth. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterJointDepth
open Function Finset Lattice RG Wilson Source Labels
open RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open WilsonReceivedChronologicalRosterRanks (infrared restored)
open scoped Classical BigOperators
variable {I : Type*} [Fintype I]

def offset {n : ℕ} (d : Fin n → ℕ) (b : ℕ) : ℕ :=
  restored n b 0 + WilsonOriginalTwoFlatIRHalo.power n ((∑ i,d i)+1+2+(2+2*n*1))+2

theorem grade {n : ℕ} (d : Fin n → ℕ) (b t : ℕ) :
    infrared d (restored n b t)=4*(t+offset d b):=by
  simp only [infrared,offset,restored]
  omega

variable (n : I→ℕ) (d : (i:I)→Fin (n i)→ℕ) (b want : I→ℕ)

def level : ℕ := Finset.univ.sup (fun i=>want i + offset (d i) (b i))

def precision (i:I) : ℕ := level n d b want - offset (d i) (b i)

theorem original (i:I) :
    want i ≤ precision n d b want i ∧
    infrared (d i) (restored (n i) (b i) (precision n d b want i)) = 4*level n d b want:=by
  have fits:want i+offset (d i) (b i) ≤ level n d b want:=
    Finset.le_sup (f:=fun j=>want j+offset (d j) (b j)) (Finset.mem_univ i)
  rw [grade]
  unfold precision
  omega

def sameStop {G:Gauge}{R:Run G}{D:XSpace.Run}{stage u a c:ℕ}
    {band:WilsonPositionProgramReporterBand.Band R D stage}
    (eqn:a=c)(v:WilsonIndependentCapturedPages.Stop R D band u a):
    WilsonIndependentCapturedPages.Stop R D band u c where
  date:=v.date
  lower:=v.lower
  upper:=v.upper
  heard:=by simpa only [←eqn] using v.heard

theorem date {G:Gauge}{R:Run G}{D:XSpace.Run}{stage u a c:ℕ}
    {band:WilsonPositionProgramReporterBand.Band R D stage}
    (eqn:a=c)(v:WilsonIndependentCapturedPages.Stop R D band u a)(w:ℕ):
    (sameStop eqn v).date w=v.date w:=rfl

end YM.Integration.WilsonReceivedChronologicalRosterJointDepth
end
