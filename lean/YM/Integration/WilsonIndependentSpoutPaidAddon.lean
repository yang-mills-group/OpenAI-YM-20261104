import YM.Integration.WilsonIndependentSpoutPhysicalAddon
import YM.Integration.WilsonIndependentPublicFreeTrain
import YM.Integration.WilsonIndependentPublicSpringKernel
import YM.RegulatorIR.Older.Trunk

/-! The particular additive tensors of the selected circuit act on every
ordinary torus used to determine the old Wilson bulk coefficients. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPaidAddon
open Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle RegulatorIR.Profiles RegulatorIR.Binding
open RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Diagram
open RegulatorIR.Diagram.Formal RegulatorIR.Older RegulatorIR.Ward RegulatorIR.Clocks
open RegulatorIR.Clocks.Warp RegulatorIR.Calibration RegulatorIR.Halo Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentSpoutOrdinarySpring WilsonIndependentPublicFreeTrain
open scoped Classical BigOperators Matrix
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)

theorem transported {c n:Side}(S:StepData c n)(patch:S.patch=C.pactP f)(ker:S.kernel=K):
    Sphere S (repeatF S) (sheet D f.prev) (C.bore G Z (sheet D) f):=by
  rw [WilsonIndependentPublicSpringKernel.forest]
  have id:=neverP (G:=G) S (C.rail K f) patch ker (sheet D f.prev)
  intro b
  rw [show Prim.prism S (bios S) (sheet D f.prev) b=Prim.prism (C.rail K f) (bios _) (sheet D f.prev) b
    from congr_fun id b]
  exact C.wheeled G Z (sheet D) f b

theorem original (Y:Program K)(A:Levels G)(s:ℕ)(inc:Matches A C K s f.volW)
    (c:Side)(e:ℕ)(pos:0<e):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1))
    let S:=mStep A c m;let F:=repeatF S;let Q:=roam A N m c
    let H:=freeForms A N (m+1);let H':=freeForms A N m
    let α:=tale (D f.prev).dine;let Ñ:=XSpace.Bare.chart G
    let rows:=C.bore G Z (sheet D) f;let V:=(story A Ñ N (m+1)).1 (c*(loose A m).L)
    ((C.dialect Y G Z (sheet D)).frames f).addon=many rows ∧
      ∀x:Lawn (Active G F⊕Woods G c),
        let z:=overM G S F *ᵥ x;let u:=camber G (extractV G S F Q) *ᵥ z
        let b:=rightArm z;let X:=joined u b
        MvPolynomial.eval x (coeff e (WilsonIndependentSpoutSchurFrame.field S F H H' Q α Ñ V))=
          MvPolynomial.eval u (coeff e (orbC (precisionC G _ H)-flash (mix α V)))+
          (∑p:Edge (Site (c*(loose A m).L)),drums (rows (.inl (peg p)) e) e X)+
          ∑p:Edge (Site c),drums (rows (.inr (peg p)) e) (e+2) X:=by
  intro N m S F Q H H' α Ñ rows V
  refine ⟨rfl,?_⟩
  have sale:=transported C Z D f S (inc.patches f rfl) inc.kinetic
  have branch:S.patch.Branches S.kernel G:=by
    have hp:S.patch=C.pactP f:=inc.patches f rfl
    have hk:S.kernel=K:=inc.kinetic
    rw [hp,hk];exact Z _
  have sq:Square F:=by
    dsimp only [F]
    rw [WilsonIndependentPublicSpringKernel.forest]
    exact Square.proper _ S.patch.odd_side
  intro x
  exact WilsonIndependentSpoutPhysicalAddon.original S F H H' Q branch sq (D f.prev) sale V x e pos

end YM.Integration.WilsonIndependentSpoutPaidAddon
