import YM.Integration.WilsonIndependentSpoutFinitePrinting
import YM.Integration.WilsonIndependentSpoutMeasuredCourse

/-! The genuine unshifted finite parent/retained board before its Gaussian
hearing. Its two summands retain the inherited quiet and the charged primitives. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutUnshiftedPost
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Halo RegulatorIR.Diagram RegulatorIR.Oracle RegulatorIR.Ledger
open RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentSpoutFiniteStencil (Raw)
open WilsonIndependentSpoutOrdinaryPrimitives (board)
open WilsonIndependentSpoutAtomicPolar (seats)
open scoped Classical BigOperators Matrix
variable {G:Gauge}

def coordinates (P:Patch)(n:Side): (Raw G (n*P.L)⊕Raw G n)≃Joint G (n*P.L) n:=
  (seats (n*P.L)).sumCongr (seats n)

def stamp (P:Patch)(n:Side)(T:Branchix→Orders (KFoot G)):Pal ℝ (Joint G (n*P.L) n):=
  fun e r q=>board P n T e r ((coordinates P n).symm∘q)

def bank (P:Patch)(n:Side)(T:Branchix→Orders (KFoot G))(α:Cost)(V:PChart G (n*P.L)):
    Pal ℝ (Joint G (n*P.L) n):=fun e r=>if e=0 then 0 else
  offer (Function.Embedding.inl (α:=Woods G (n*P.L)) (β:=Woods G n)) (-mix α V e r)+
    stamp P n T e r

theorem budget (P:Patch)(n:Side)(T:Branchix→Orders (KFoot G))(cost:∀v e,Within (e+2) (T v e))
    (e:ℕ):Within (e+2) (board P n T e):=by
  intro r nz;by_contra! hr;apply nz
  apply Finset.sum_eq_zero;intro u _
  have zero:T (WilsonIndependentSpoutOrdinaryPrimitives.liftKey u) e r=0:=
    Classical.not_not.mp fun ne=>not_le_of_gt hr (cost _ e r ne)
  ext1 q;simp [zero,Stalk.collect]

variable {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)

theorem invoice (e:ℕ)(P:Patch)(n:Side):Within (e+2) (board P n (C.bore G Z (sheet D) f) e):=by
  apply budget;intro v a r nz
  cases v with
  | inl v=>
    have h:r≤a+0:=(C.wheeled G Z (sheet D) f (.inl v)).scope_ a r nz
    omega
  | inr v=>exact (C.wheeled G Z (sheet D) f (.inr v)).scope_ a r nz

theorem printed (e:ℕ)(P:Patch)(n:Side):
    totalR (stamp P n (C.bore G Z (sheet D) f) e)=
      WilsonIndependentSpoutPostedAction.print P n (C.bore G Z (sheet D) f) e:=
  WilsonIndependentSpoutFinitePrinting.move (coordinates P n) (invoice C Z D f e P n)

end YM.Integration.WilsonIndependentSpoutUnshiftedPost
