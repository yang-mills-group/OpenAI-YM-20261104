import YM.Integration.WilsonIndependentPostedFrame

/-! Simultaneous finite and cover enrollment on the actual common patch. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPostedInlet
open Function Matrix Lattice Laurent Bloch RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Oracle RegulatorIR.Profiles RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Halo
open RegulatorIR.Ledger RegulatorIR.Calibration WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentConditionalCoordinateHeat (row)
open WilsonIndependentConditionalNativeLinks (joint)
open scoped Classical BigOperators Matrix
variable {G:Gauge}{W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
    (C:Circuit M ss)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(Ñ:ChartRatio G)(N m:ℕ)(α:Cost)

def incoming (P:Patch)(n:Side)(e:ℕ):Gen ℝ (Co n (Hinge G P.L)):=
  bend (weaveH (ratioN P.L n) G) (WilsonIndependentSpoutUnshiftedPost.bank P n
    (C.bore G Z (sheet D) f) α ((story A Ñ N m).1 (n*P.L)) e)

def quiet (P:Patch)(e:ℕ)(r:ℕ):Ten ℝ (Cloth (Hinge G P.L)) r:=
  WilsonIndependentConditionalCoordinateHeat.row (joint G P).symm
    ((C.devices Y G Z (sheet D) f).jVac (WilsonIndependentSpoutReportedQuiet.port A Ñ N m α) e r)

theorem head (P:Patch):∀e r,(C.devices Y G Z (sheet D) f).jVac
      (WilsonIndependentSpoutReportedQuiet.port A Ñ N m α) e r=
      WilsonIndependentConditionalCoordinateHeat.row (joint G P) (quiet C Y Z D f A Ñ N m α P e r):=by
  intro e r;funext q
  change _=(C.devices Y G Z (sheet D) f).jVac _ e r ((joint G P).symm∘(joint G P)∘q)
  congr 1;funext i;exact ((joint G P).symm_apply_apply (q i)).symm

theorem registered (P:Patch)(same:P=C.pactP f)(n:Side)(i:ℕ):
    HEq (incoming C Z D f A Ñ N m α P n i) (WilsonIndependentPostedBoard.posted C Z D f A Ñ N m α n i):=by
  subst P;apply heq_of_eq;funext r q
  let E:=weaveH (ratioN (C.pactP f).L n) G
  change WilsonIndependentSpoutUnshiftedPost.bank (C.pactP f) n (C.bore G Z (sheet D) f) α ((story A Ñ N m).1 (n*(C.pactP f).L)) i r (E.symm∘q)=_
  rw [←WilsonIndependentPostedBoard.original C Z D f A Ñ N m α n i r (E.symm∘q)]
  congr 1;funext j;exact E.apply_symm_apply (q j)

theorem earned (P:Patch)(same:P=C.pactP f)(simple:G.Simple)(ratio:LocalRatio Ñ)(age:m≤N)(e r:ℕ)(hr:0<r):
    Yields (fun n=>incoming C Z D f A Ñ N m α P n e r) (quiet C Y Z D f A Ñ N m α P e r):=by
  subst P
  have h:=WilsonIndependentPostedBoard.earned C Y Z D f A Ñ N m α simple ratio age e r hr
  convert h using 1
  · funext n;rw [eq_of_heq (registered C Z D f A Ñ N m α _ rfl n e)]
  · funext q
    have eq:=congrFun (WilsonIndependentPostedFrame.original C Y Z D f A Ñ N m α e r hr) ((joint G (C.pactP f)).symm∘q)
    change _ = _ at eq
    change (C.devices Y G Z (sheet D) f).jVac (WilsonIndependentSpoutReportedQuiet.port A Ñ N m α) e r ((joint G (C.pactP f)).symm∘q)=_
    rw [←eq]
    unfold WilsonIndependentConditionalCoordinateHeat.row
    congr 1;funext j;exact (joint G (C.pactP f)).apply_symm_apply (q j)

theorem pure (P:Patch)(same:P=C.pactP f)(simple:G.Simple)(ratio:LocalRatio Ñ)(age:m≤N)(n:Side)(i:ℕ):
    Pure (incoming C Z D f A Ñ N m α P n i):=by
  subst P
  rw [eq_of_heq (registered C Z D f A Ñ N m α _ rfl n i)]
  exact WilsonIndependentPostedBoard.pure C Z D f A Ñ N m α simple ratio age n i

end YM.Integration.WilsonIndependentPostedInlet
