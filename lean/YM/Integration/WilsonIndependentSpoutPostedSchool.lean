import YM.Integration.WilsonIndependentSpoutPostedBank

/-! Angular degree, symmetry and the genuinely cleared order zero on the exact
premean finite joint input used for the paid Gaussian hearing. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPostedSchool
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Halo RegulatorIR.Diagram RegulatorIR.Oracle RegulatorIR.Ledger
open RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentSpoutUnshiftedPost (bank stamp coordinates invoice)
open WilsonIndependentSpoutAtomicPolar (symmetric)
open WilsonIndependentSpoutOrdinaryPrimitives (board liftKey)
open WilsonIndependentSpoutFiniteStencil (fold)
open scoped Classical BigOperators Matrix
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)

theorem original (P:Patch)(n:Side)(α:Cost)(V:PChart G (n*P.L))(shape:shellK 2 V)
    (v:∀ e,Pure (V e)):
    let A:=bank P n (C.bore G Z (sheet D) f) α V
    A 0=0 ∧ shellK 2 A ∧ ∀e,Pure (A e):=by
  intro A
  have initial:A 0=0:=by funext r;simp only [A,bank];rfl
  refine ⟨initial,?_,?_⟩
  · intro e r far
    by_cases zero:e=0
    · rw [zero,initial];rfl
    have pzero:board P n (C.bore G Z (sheet D) f) e r=0:=
      Classical.not_not.mp fun nz=>not_le_of_gt (by omega) (invoice C Z D f e P n r nz)
    have old:mix α V e r=0:=mix_length shape e r far
    ext1 q
    simp [A,bank,zero,old,stamp,pzero,offer,Stalk.collect]
  · intro e r ω y
    by_cases zero:e=0
    · rw [zero,initial];rfl
    have orig (j:WilsonIndependentSpoutFiniteStencil.Keys P n):IsSym (C.bore G Z (sheet D) f (liftKey j) e r):=
      (C.wheeled G Z (sheet D) f (liftKey j)).smooth e r
    have paid:IsSym (board P n (C.bore G Z (sheet D) f) e r):=by
      intro ρ t
      simp only [WilsonIndependentSpoutOrdinaryPrimitives.board,Finset.sum_apply]
      apply Finset.sum_congr rfl;intro j _
      exact symmetric (fold P n) (orig j) ρ t
    have loan:IsSym (-mix α V e r):=by
      intro ρ t
      simp only [Pi.neg_apply];exact congrArg Neg.neg (mix_pure v e r ρ t)
    change (bank P n (C.bore G Z (sheet D) f) α V e r) (y∘ω)=_
    simp only [A,bank,if_neg zero,Pi.add_apply,stamp]
    apply congrArg₂ Add.add
    · exact symmetric (Sum.inl:Woods G (n*P.L)→Joint G (n*P.L) n) loan ω y
    · exact paid ω ((coordinates P n).symm∘y)

end YM.Integration.WilsonIndependentSpoutPostedSchool
