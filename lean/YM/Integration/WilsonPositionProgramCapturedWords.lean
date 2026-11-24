import YM.Integration.WilsonPositionProgramCapturedAngular

/-! Recover the angular packet from its whole group-valued insertion on the
original signed clock, then lift it on the chronological cover at capture. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramCapturedWords
open Function Filter Finset Lattice Wilson Exterior Precision Marker Comparison.RG02
open Comparison.RG02.Adjacent Comparison.RG02.Moving Comparison.RG02.Moving.Path
open RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.FVAAlt2
open RegulatorIR.Budget RegulatorIR.Diagram RegulatorIR.Budget.FVAAlt2.Wind RegulatorIR.Budget.FVAAlt2.Wind.Pine
open RegulatorIR.FVAAlt2.Period.Field RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Sound
open scoped Topology BigOperators ENNReal Classical
variable {G:Gauge} {n:Side}
abbrev Slots (G:Gauge) (n:Side) := FreeResolvent.Slot G n 1

def represents (k:ℕ) (f:fieldDir G n 1→ℂ) (B:Ranked (Slots G n)) : Prop :=
  (∀r,(B r).IsSym) ∧ Within k B ∧ ∀A, f A=((MvPolynomial.eval (FreeResolvent.flatten A) (packed B k):ℝ):ℂ)

def recover (k:ℕ)(f:fieldDir G n 1→ℂ) : Ranked (Slots G n) :=
  if h:∃B,represents k f B then h.choose else 0

private theorem unique {k:ℕ} {f:fieldDir G n 1→ℂ} {B D:Ranked (Slots G n)}
    (left:represents k f B) (right:represents k f D) : B=D := by
  have equal:packed B k=packed D k := by
    apply MvPolynomial.funext
    intro z
    let A:fieldDir G n 1:=fun w=>WithLp.toLp 2 (fun a=>z (w.1,w.2,a))
    have coordinates:FreeResolvent.flatten A=z:=by ext1 w; rfl
    have h:((MvPolynomial.eval z (packed B k):ℝ):ℂ)=↑(MvPolynomial.eval z (packed D k)) := by
      rw [←coordinates,←left.2.2 A,←right.2.2 A]
    exact Complex.ofReal_injective h
  funext r
  by_cases inside:r≤k
  · have included:r∈range (k+1):=mem_range.mpr (by omega)
    apply identified _ _ (left.1 r) (right.1 r)
    rw [←isolate B included,←isolate D included]
    exact congrArg (MvPolynomial.homogeneousComponent r) equal
  · rw [not_ne_iff.mp (mt (left.2.1 r) inside),not_ne_iff.mp (mt (right.2.1 r) inside)]

theorem reads {k:ℕ} {f:fieldDir G n 1→ℂ}{B:Ranked (Slots G n)}
    (law:represents k f B) : recover k f=B := by
  have available:∃B,represents k f B:=⟨_,law⟩
  rw [recover,dif_pos available]
  exact unique available.choose_spec law

variable {A:Type} [DecidableEq A] (mask:Marker.Census A)(u:A)(m e:ℕ)
    (clock:UnitCost)(V:Bulk.Colors mask G n)
def groupRows := recover (e+m) (See.noseC mask u clock V e)
theorem heard (W:Orders (Slots G n)) (symm:gradedSymmetric W) (bound:Within (e+m) (W e))
    (read:∀x,See.noseC mask u clock V e x=Booth.Uniforms.cuff W m e x) :
    groupRows mask u m e clock V=W e := by
  apply reads
  refine ⟨symm e,bound,?_⟩
  intro x
  rw [read,Booth.Uniforms.cuff,Binding.flavor_lo]

theorem single (W:Orders (Slots G n)) {p:ℕ} (he:e≤p) (receipt:Booth.Arm.Single clock V W u p m) :
    groupRows mask u m e clock V=W e :=
  heard mask u m e clock V W receipt.symmetricW (receipt.grade e) (receipt.earned e he)

end YM.Integration.WilsonPositionProgramCapturedWords
end
