import YM.Integration.WilsonIndependentSpoutUnshiftedPost

/-! Evaluation of the full unshifted raw ledger after the actual tree
inclusion and affine Schur mean, before any Wick integration. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutPostedBank
open Function PowerSeries Matrix Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Budget RegulatorIR.Budget.Packet
open RegulatorIR.Halo RegulatorIR.Diagram RegulatorIR.Oracle RegulatorIR.Ledger
open RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration
open PertExtension Tree FreeResolvent Metric Precision Exterior Wilson WilsonCoeffUV.Power
open WilsonIndependentSpoutUnshiftedPost (bank stamp coordinates invoice printed)
open scoped Classical BigOperators Matrix
variable {G:Gauge}{I J:Type}

theorem finite {T:Ranked I}{k:ℕ}(cost:Within k T):FiniteGen T:=
  ⟨k+1,fun r hr=>Classical.not_not.mp fun nz=>not_le_of_gt hr (cost r nz)⟩

theorem nested {T:Ranked I}{k:ℕ}(cost:Within k T):
    Within k (fun r=>offer (Function.Embedding.inl (α:=I) (β:=J)) (T r)):=by
  intro r hn;apply cost r;intro hz;apply hn;ext1 q;simp [offer,Stalk.collect,hz]

theorem fine {f c:Side}(S:StepData c f)(F:Forest S.ratio)(U:Matrix (Woods G f) (Woods G c) ℝ)
    (P:POL (Woods G f)):cord (panSlice G S F U) (MvPolynomial.rename
      (Sum.inl:Woods G f→Joint G f c) P)=cord (camSlice G S F U) P:=by
  apply MvPolynomial.funext;intro y
  simp only [cord_apply,MvPolynomial.eval_rename]
  apply congrArg (fun z=>MvPolynomial.eval z P)
  rw [camSlice,panSlice,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
  funext j;exact congr_fun (camIn G U (overM G S F *ᵥ y)).1 j

variable {W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)

theorem landed (A:Levels G)(N m:ℕ)(n:Side)(α:Cost)(V:PChart G (n*(loose A m).L))(scope:shellK 2 V):
    let P:=loose A m;let S:=mStep A n m;let F:=repeatF S
    let Q:=extractV G S F (roam A N m n);let T:=C.bore G Z (sheet D) f
    loom (panSlice G S F Q) (flash (bank P n T α V))=
      WilsonIndependentSpoutPostedHearing.posted A N m n T α V:=by
  intro P S F Q T;apply PowerSeries.ext;intro e
  simp only [loom,PowerSeries.coeff_map,Blue.flash,coeff_mk,WilsonIndependentSpoutPostedHearing.posted]
  by_cases zero:e=0
  · subst e
    have empty: bank P n T α V 0=0:=by funext r;simp only [bank];rfl
    rw [if_pos rfl,empty];simp [totalR]
  rw [if_neg zero]
  let U:=mix α V e
  let F0:Ranked (Woods G (n*P.L)):= -U
  have cap:Within (e+2) U:=by intro r nz;by_contra! hr;exact nz (mix_length (A:=α) scope e r (by omega))
  have cap0:Within (e+2) F0:=by intro r nz;apply cap;intro hz;apply nz;change -U r=0;rw [hz,neg_zero]
  let E:=stamp P n T e
  have caps:Within (e+2) E:=by
    intro r neq;apply invoice C Z D f e P n r;intro hz;apply neq;ext1 q
    change WilsonIndependentSpoutOrdinaryPrimitives.board P n T e r _=0;rw [hz];rfl
  let E0:Ranked (Joint G (n*P.L) n):=fun r=>offer Function.Embedding.inl (F0 r)
  change cord (panSlice G S F Q) (totalR (bank P n T α V e))=_
  have identity:bank P n T α V e=E0+E:=by funext r;simp only [bank,if_neg zero];rfl
  rw [identity,visible_add (finite (nested cap0)) (finite caps),map_add]
  change cord (panSlice G S F Q) (totalR (fun r=>offer Function.Embedding.inl (F0 r)))+
    cord (panSlice G S F Q) (totalR (stamp P n T e))=_
  rw [WilsonIndependentSpoutFinitePrinting.left F0 cap0, fine, printed C Z D f e P n]
  apply congrArg (fun z=>z+_)
  have minus:totalR F0= -totalR U:=by simpa only [neg_one_smul] using visible_μ (finite cap) (-1)
  rw [minus]
  simp only [map_sub,orbC,coeff_C,if_neg zero,zero_sub,Blue.flash,coeff_mk]
  rfl

end YM.Integration.WilsonIndependentSpoutPostedBank
