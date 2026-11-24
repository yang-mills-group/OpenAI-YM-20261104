import YM.Integration.WilsonIndependentSpoutMarkedTensorExit

/-! The actual normalized one-flap marked Wilson response on every ordinary finite board, including rank zero. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutRealMarkRows
open Function Matrix PowerSeries Lattice RG WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank
open WilsonCoeffUV.Power WilsonCoeffUV.Mer WilsonCoeffUV.Soil RegulatorIR RegulatorIR.Geometry
open RegulatorIR.Prim RegulatorIR.Oracle RegulatorIR.Calibration RegulatorIR.Clocks
open RegulatorIR.Ledger
open PertExtension Tree FreeResolvent Metric Precision Exterior
open WilsonIndependentSpoutUnshiftedPost (bank)
open WilsonIndependentSpoutFiniteExitRows (pulled)
open WilsonIndependentConditionalRawSpout (finite)
open scoped BigOperators Classical Matrix
variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(A:Levels G)(s:ℕ)

theorem original (simple:G.Simple)(p:ℕ)(n:Side)(paid:WilsonIndependentSpoutMeasuredHearing.Hearing C Z D f A s p n)
    {k:ℕ}(E:Era G ℝ)(admitted:Auth k E):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let P:=loose A m
    let S:=mStep A n m;let F:=repeatF S;let H:=freeForms A N (m+1)
    let Ñ:=XSpace.Bare.chart G;let b:=n*P.L;let V:=(story A Ñ N (m+1)).1 b
    let α:=tale (D f.prev).dine;let β:=relativeC A Ñ N m (N-m)
    let T:=bank P n (C.bore G Z (sheet D) f) α V;let U:=panSlice G S F (extractV G S F (roam A N m n))
    let mark:=srCold (mix α (E.1 b)) (0:Matrix (Woods G b) (Woods G n) ℝ)
    ∀e≤p,pulled U (finite (fillSlots (Woods G n) (FreeResolvent.covariance G S F H)) T mark k) e =
      mix β ((verseI A Ñ m N k E).1 n) e:=by
  intro N m P S F H Ñ b V α β T U mark
  have age:m<N:=by dsimp only [N,m];have:=f.ok;omega
  have basis:Interlace H V:=(old A Ñ simple (XSpace.Bare.chart_ratio G) N (m+1) age).basis b
  have stored:=WilsonIndependentSpoutPostedSchool.original C Z D f P n α V basis.lamp basis.shape
  dsimp only at stored
  have adj:(treeInverse G S F H 0).transpose=treeInverse G S F H 0:=by
    unfold treeInverse FreeResolvent.resolve
    rw [zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,full_symmetric _ (age_sym A N (m+1) b)]
  have one:constantCoeff α=1:=by rw [←coeff_zero_eq_constantCoeff_apply];simpa [α] using (D f.prev).origin
  have shape:shellK k mark:=fade_shell _ (mix_length (A:=α) (admitted.span b))
  have smooth (e:ℕ):Pure (mark e):=fade_pure (mix_pure (admitted.pale b) e) _
  have bottom:Auth k (verseI A Ñ m N k E):=Auth.verse A age simple (XSpace.Bare.chart_ratio G) admitted
  have verdict:=paid.2 k E admitted
  change Equal (p+1) (Wick (Woods G n) (treeInverse G S F H 0)
      (raiseE (WilsonIndependentSpoutPostedHearing.posted A N m n (C.bore G Z (sheet D) f) α V)*
        redo α (loom (camSlice G S F (extractV G S F (roam A N m n))) (flash (E.1 b)))))
    (Wick (Woods G n) (treeInverse G S F H 0)
      (raiseE (WilsonIndependentSpoutPostedHearing.posted A N m n (C.bore G Z (sheet D) f) α V))*
      redo β (flash ((verseI A Ñ m N k E).1 n))) at verdict
  rw [←WilsonIndependentSpoutPostedBank.landed C Z D f A N m n α V basis.lamp,
    ←WilsonIndependentSpoutPostedMarkLaw.inlet S F (extractV G S F (roam A N m n)) (admitted.span b) α one] at verdict
  have take:=WilsonIndependentSpoutMarkedTensorExit.measured U (treeInverse G S F H 0) adj
    stored.2.1 stored.1 stored.2.2 shape smooth (bottom.span n) (bottom.pale n) β verdict
  rw [show U*fillSlots (Woods G n) (treeInverse G S F H 0)*U.transpose =
    fillSlots (Woods G n) (FreeResolvent.covariance G S F H) from WilsonIndependentSpoutTrueFiniteVacuum.covariance ..] at take
  exact take

end YM.Integration.WilsonIndependentSpoutRealMarkRows
