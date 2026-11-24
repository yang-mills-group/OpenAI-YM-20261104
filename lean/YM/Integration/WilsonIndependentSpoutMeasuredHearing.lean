import YM.Integration.WilsonIndependentSpoutPostedHearing
import YM.Integration.WilsonIndependentSpoutClockedPrint
import YM.Integration.WilsonIndependentSpoutSchurStory

/-! At the bought common order the same posted Gaussian numerator gives
both the centered unmarked action and the full independently measured mark
on the authentic next date, including its unit coordinate. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutMeasuredHearing
open Matrix PowerSeries Function Lattice RG Wilson WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Bank
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Prim RegulatorIR.Budget.Packet RegulatorIR.Oracle
open RegulatorIR.Ledger RegulatorIR.Clocks RegulatorIR.Clocks.Warp RegulatorIR.Calibration RegulatorIR.Ward
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested
open Tree FreeResolvent Metric Precision Exterior Next.Free
open WilsonIndependentPublicFreeTrain WilsonIndependentConditionalPositiveVacuum
open WilsonIndependentSpoutSchurVacuum
open WilsonIndependentSpoutPostedHearing (posted)
open scoped Classical BigOperators Matrix MatrixOrder

variable {G:Gauge}{W:Type}{M:W→ℕ}{sides:Page M→Side}{K:KernelChoices}
    (C:Circuit M sides)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)
    (A:Levels G)(s:ℕ)(inc:Matches A C K s f.volW)

def Hearing (p:ℕ)(n:Side):Prop:=
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let S:=mStep A n m;let F:=repeatF S
    let Q:=roam A N m n;let H:=freeForms A N (m+1);let H':=freeForms A N m
    let Ñ:=XSpace.Bare.chart G;let b:=n*(loose A m).L;let V:=(story A Ñ N (m+1)).1 b
    let α:=tale (D f.prev).dine;let β:=relativeC A Ñ N m (N-m)
    let T:=posted A N m n (C.bore G Z (sheet D) f) α V
    let heat:=Wick (Woods G n) (treeInverse G S F H 0)
    (∀e≤p,∀y:TreeVars G n,value (logOf (heat (raiseE T))) e y=
      value (orbC (precisionC G n H')) e y-value (redo β (flash ((story A Ñ N m).1 n))) e y)∧
    ∀k (U:Era G ℝ),Auth k U→
      Equal (p+1) (heat (raiseE T*redo α (loom (camSlice G S F (extractV G S F Q)) (flash (U.1 b)))))
        (heat (raiseE T)*redo β (flash ((verseI A Ñ m N k U).1 n)))

include Y inc in
theorem given (simple:G.Simple)(p:ℕ)
    (book:Squares p (tale (D f.prev).dine) (relativeC A (XSpace.Bare.chart G)
      (s+M f.volW) ((s+(M f.volW-(f.offset+1)))+1) ((s+M f.volW)-((s+(M f.volW-(f.offset+1)))+1))))
    (n:Side):Hearing C Z D f A s p n:=by
  let Ñ:=XSpace.Bare.chart G;let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1))
  have finer:m<N:=by dsimp only [m,N];have:=f.ok;omega
  let b:=n*(loose A m).L;let S:=mStep A n m;let F:=repeatF S;let Q:=roam A N m n
  let H:=freeForms A N (m+1);let H':=freeForms A N m;let V:=(story A Ñ N (m+1)).1 b
  let α:=tale (D f.prev).dine;let δ:=relativeC A Ñ N (m+1) (N-(m+1));let β:=relativeC A Ñ N m (N-m)
  let heat:=Wick (Woods G n) (treeInverse G S F H 0);let T:=posted A N m n (C.bore G Z (sheet D) f) α V
  have unit:constantCoeff α=1:=by rw [←coeff_zero_eq_constantCoeff_apply];simpa [α] using (D f.prev).origin
  have uδ:constantCoeff δ=1:=angularC simple (XSpace.Bare.chart_ratio G) (by omega)
  have hV:Interlace H V:=(old A Ñ simple (XSpace.Bare.chart_ratio G) N (m+1) finer).basis _
  have field:T=WilsonIndependentSpoutSchurFrame.field S F H H' Q α Ñ V:=
    WilsonIndependentSpoutPostedHearing.frame C Y Z D f A s inc simple n
  constructor
  · intro e he y
    change value (logOf (heat (raiseE T))) e y=_
    rw [field]
    have h (θ:Cost)(one:constantCoeff θ=1):=
      WilsonIndependentSpoutSchurVacuum.held S F H H' Q θ one hV.lamp hV.stem (A.blocks m 0).branches
        (horizon_step A m N finer n _ rfl) (age_sym A ..) (XSpace.Bare.chart_ratio G)
          (Convention.tree_pos A m N rfl) hV.shape e y
    have money:=WilsonIndependentSpoutSchurStory.original A Ñ simple (XSpace.Bare.chart_ratio G) finer n e y
    change value (logOf (read S F H H' Q δ Ñ V)) e y=_ at money
    change value (logOf (read S F H H' Q α Ñ V)) e y=_
    rw [←money,h α unit,h δ uδ]
    have rows:Blue.mix α (winter S F H H' Q Ñ V) e=Blue.mix δ (winter S F H H' Q Ñ V) e:=
      WilsonIndependentSpoutClockedPrint.source (e:=e) book uδ (winter S F H H' Q Ñ V) he
    dsimp only [Ñ] at rows
    simp only [value,Blue.flash,coeff_mk,rows]
  · intro k U auth
    let L:=reed S F H Q Ñ V k (U.1 b)
    have received:heat (raiseE T*redo α (loom (camSlice G S F (extractV G S F Q)) (flash (U.1 b))))=
        heat (raiseE T)*redo α (flash L):=WilsonIndependentSpoutPostedHearing.original C Y Z D f A s inc simple n k U auth
    change Equal (p+1) (heat (raiseE T*redo α (loom (camSlice G S F (extractV G S F Q)) (flash (U.1 b)))))
      (heat (raiseE T)*redo β (flash ((verseI A Ñ m N k U).1 n)))
    rw [received]
    apply (Equal.refl (heat (raiseE T)) (p+1)).mul
    have span:shellK k L:=reed_band S F H Q k hV.lamp (XSpace.Bare.chart_ratio G) (auth.span _)
    have lower:(verseI A Ñ m N k U).1 n=mix (ratioHigh A Ñ N m) L:=rfl
    rw [lower,←redo_stern _ span]
    have commit:redo β (redo (ratioHigh A Ñ N m) (flash L))=redo δ (flash L):=by
      dsimp only [β,δ]
      rw [show N-m=1+(N-(m+1)) by omega]
      exact WilsonIndependentSpoutChronologicalClock.original A Ñ simple (XSpace.Bare.chart_ratio G) (by omega) _
    rw [commit,redo_stern _ span,redo_stern _ span]
    intro e he
    have rows:Blue.mix α L e=Blue.mix δ L e:=WilsonIndependentSpoutClockedPrint.source (e:=e) book uδ L (by omega)
    simp only [Blue.flash,coeff_mk,rows]

end YM.Integration.WilsonIndependentSpoutMeasuredHearing
