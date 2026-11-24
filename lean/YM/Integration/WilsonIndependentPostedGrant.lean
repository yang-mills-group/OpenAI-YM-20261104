import YM.Integration.WilsonIndependentPrimitivePure
import YM.Integration.WilsonIndependentSpoutReportedQuiet

/-! The Wilson Haar/spring and the incoming voted nonquadratic story on their joint raw axes. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPostedGrant
open Function Filter Matrix Lattice Laurent Bloch RG Wilson RegulatorIR RegulatorIR.Oracle RegulatorIR.Profiles
open RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Ledger RegulatorIR.Diagram RegulatorIR.Budget
open RegulatorIR.Budget.Packet RegulatorIR.Halo RegulatorIR.Binding RegulatorIR.Calibration
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open PertExtension Tree FreeResolvent Metric Precision Exterior Next.Free Wilson WilsonCoeffUV.Power
open WilsonIndependentConditionalNativeLinks (joint)
open WilsonIndependentPrimitiveCoordinates (printed)
open scoped BigOperators Classical Topology

def insert (U:Type)[DecidableEq U](a b:Type)[DecidableEq a]:ropes U a (a⊕b):=upper 1 0

theorem pilots (a b:Type)[DecidableEq a]:
    Pilots (fun n=>insert (Site n) a b) (insert Cover a b):=by
  apply Pilots.one.deck
  exact ⟨fun _ _=>tendsto_const_nhds,Eventually.of_forall (fun _ _ _ _=>rfl),
    1,0,one_pos,Eventually.of_forall fun _=>dragCup.zero⟩

variable {G:Gauge}
def oldFinite (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)(L:Side)(n:Side)(e:ℕ):Gen ℝ (Co n (Hinge G L)):=
  fade (insert (Site n) (Larvae G L) (Hooks G))
    (bend (weaveFine (ratioN L n) G) (fun r=>WilsonIndependentSpoutReportedQuiet.finite A Ñ N m α e r (n*L)))

def oldCover (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)(L:Side)(e:ℕ):Gen ℝ (Cloth (Hinge G L)):=
  prism (insert Cover (Larvae G L) (Hooks G))
    (plants L (fun r=>WilsonIndependentSpoutReportedQuiet.cover A Ñ N m α e r))

theorem quiet (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)(N m:ℕ)(age:m≤N)
    (α:Cost)(L:Side)(e r:ℕ):
    Yields (fun n=>oldFinite A Ñ N m α L n e r) (oldCover A Ñ N m α L e r):=by
  unfold oldFinite oldCover
  apply prism_fold (pilots (Larvae G L) (Hooks G))
  apply bend_yields (L:=L) (α:=Hooks G) (P:=fun v r=>WilsonIndependentSpoutReportedQuiet.finite A Ñ N m α e r v)
  exact WilsonIndependentSpoutReportedQuiet.earned A Ñ simple ratio N m age α e r

theorem old_pure (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)(N m:ℕ)(age:m≤N)
    (α:Cost)(L:Side)(n:Side)(e:ℕ):Pure (oldFinite A Ñ N m α L n e):=by
  unfold oldFinite
  apply fade_pure
  intro r s x
  change WilsonIndependentSpoutReportedQuiet.finite A Ñ N m α e r (n*L) ((weaveFine (ratioN L n) G).symm∘(x∘s))=
    WilsonIndependentSpoutReportedQuiet.finite A Ñ N m α e r (n*L) ((weaveFine (ratioN L n) G).symm∘x)
  by_cases z:e=0
  · simp only [WilsonIndependentSpoutReportedQuiet.finite,if_pos z,Pi.zero_apply]
  simp only [WilsonIndependentSpoutReportedQuiet.finite,if_neg z,Pi.neg_apply]
  apply congr_arg Neg.neg
  exact mix_pure (A:=α) (P:=(story A Ñ N m).1 (n*L)) (fun i=>((old A Ñ simple ratio N m age).basis (n*L)).shape i) e r s ((weaveFine (ratioN L n) G).symm∘x)

variable {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)(N m:ℕ)(age:m≤N)(α:Cost)

def finite (n:Side)(e:ℕ):Gen ℝ (Co n (Hinge G (C.pactP f).L)):=
  fun r=>oldFinite A Ñ N m α (C.pactP f).L n e r+printed (C.pactP f) (C.bore G Z (sheet D) f) e r n

def cover (e:ℕ):Gen ℝ (Cloth (Hinge G (C.pactP f).L)):=
  fun r x=>oldCover A Ñ N m α (C.pactP f).L e r x+
    ((C.dialect Y G Z (sheet D)).frames f).addon e r ((joint G (C.pactP f)).symm∘x)

include simple ratio age in
theorem original (e r:ℕ)(pin:Fin r):
    Yields (fun n=>finite C Z D f A Ñ N m α n e r) (cover C Y Z D f A Ñ N m α e r):=
  (quiet A Ñ simple ratio N m age α (C.pactP f).L e r).add
    (WilsonIndependentPrimitiveGranted.original C Y Z D f e r pin)

include simple ratio age in
theorem pure (n:Side)(e:ℕ):Pure (finite C Z D f A Ñ N m α n e):=fun r=>
  (old_pure A Ñ simple ratio N m age α (C.pactP f).L n e r).add
    (WilsonIndependentPrimitivePure.original C Z (sheet D) f n e r)

end YM.Integration.WilsonIndependentPostedGrant
