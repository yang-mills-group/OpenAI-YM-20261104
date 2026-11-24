import YM.Integration.WilsonVacuumPreResetCurvatureRack

/-! The actual path action on the simultaneous filtered curvature source.
The omitted regular source retains its signed covariance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvatureMoves
open Lattice RG Wilson PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open Push Push.AbsoluteSums Collection Quotes Song Meadow RG01Estimate RG01Estimate.Precise
open WilsonVacuumPreResetCurvatureField WilsonVacuumPreResetCurvatureRegister WilsonVacuumPreResetCurvatureRack
open scoped Classical
variable {G:Gauge}{n:Side}

theorem original (A:Listing G n)(B:BudgetPoint)(K:PathData G)(c:Clip)(σ C γ β:ℝ)(t q:ℕ)(s:Signed)(b:Site n):
    let M:=model A B K c σ C γ β t q
    Nonempty (Caddy.Mirrors M.listing.reg s b M.trunk) ∧
    Nonempty (Caddy.Mirrors M.listing.reg s b M.pioneers) ∧
    Nonempty (Caddy.Mirrors M.listing.reg s b (-(M.trunk-M.pioneers))):=by
  intro M
  let w:=walk s b
  have h i:=WilsonVacuumPreResetCurvatureRegister.moves B K c γ β s b (number n i)
  have addr i:(M.listing.reg (w i)).site=affine s b (M.listing.reg i).site ∧
      (M.listing.reg (w i)).support=(M.listing.reg i).support.image (affine s b):=by
    change (strings K B (slot (number n (walk s b i)))).site=_ ∧ (strings K B (slot (number n (walk s b i)))).support=_
    rw [atWalk]
    exact ⟨(h i).1,(h i).2.1⟩
  have full i:M.trunk (w i)=M.trunk i ∘ pull s b:=by
    change source K c γ β (number n (walk s b i))=_
    rw [atWalk]
    exact (h i).2.2
  have finite i:M.pioneers (w i)=M.pioneers i ∘ pull s b:=by
    change held K c γ β (cut n K t q) (walk s b i)=held K c γ β (cut n K t q) i ∘ pull s b
    simp only [WilsonVacuumPreResetCurvatureRack.held,WilsonVacuumPreResetCurvatureRack.invariant]
    by_cases live:i∈cut n K t q
    · simp only [if_pos live,atWalk]
      exact (h i).2.2
    · simp [live]
  have one:=fun i=>(addr i).1
  have two:=fun i=>(addr i).2
  refine ⟨⟨w,one,two,full⟩,⟨w,one,two,finite⟩,⟨w,one,two,?_⟩⟩
  intro i
  funext U
  change -(M.trunk (w i) U-M.pioneers (w i) U)=_
  rw [full,finite]
  rfl

end YM.Integration.WilsonVacuumPreResetCurvatureMoves
