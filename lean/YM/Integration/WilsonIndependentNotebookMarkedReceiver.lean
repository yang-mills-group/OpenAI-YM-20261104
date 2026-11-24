import YM.Integration.WilsonIndependentNotebookMarkHear

/-! The retained marked scalar and all its angular rows on a genuinely dated
finite comparison. The incoming vacuum is used only at its nonconstant ranks. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookMarkedReceiver
open Function Matrix Lattice Laurent RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open RegulatorIR.Oracle RegulatorIR.Prim RegulatorIR.Ledger RegulatorIR.Calibration RegulatorIR.Step
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonIndependentConditionalNativeLinks (coarse)
open WilsonIndependentConditionalCoordinateHeat (orders ranks)
open scoped Classical BigOperators
section comparison
variable {A:ℝ}{I J U V:Type}{F:Deck A I U}{P:Deck A J V}
theorem cutoff (S:GridStep F P){X Y X' Y':Orders I}{d:ℕ}
    (old:∀i≤d,∀r,0<r→X i r=X' i r)(marked:∀i≤d,Y i=Y' i)(k:ℕ){e:ℕ}(he:e≤d)(r:ℕ):
    S.each k X Y e r=S.each k X' Y' e r:=by
  have act(i)(hi:i≤d)(r)(hr:0<r):S.jVac X i r=S.jVac X' i r:=by
    unfold GridStep.jVac;rw [old i hi r hr]
  let I₁:Orders (I⊕J):=fun a r=>offer (firstChannel F P).native (Y a r)
  let I₂:Orders (I⊕J):=fun a r=>offer (firstChannel F P).native (Y' a r)
  have p(i)(hi:i≤d):I₁ i=I₂ i:=by dsimp only [I₁,I₂];rw [marked i hi]
  exact congr_arg S.pullI (congrFun (WilsonIndependentConditionalThermalCap.original S.line act p k he) r)
end comparison

variable {G:Gauge}{W:Type}{M:W→ℕ}{ss:Page M→Side}{K:KernelChoices}
variable (C:Circuit M ss)(Y:Program K)(Z:∀P:Patch,P.Branches K G)(D:Tent M)(f:Flap M)(A:Levels G)(s:ℕ)

theorem issued (R:WilsonIndependentPublicFreeTrain.Matches A C K s f.volW)
    (simple:G.Simple)(k:ℕ)(X:Era G ℝ)(auth:Auth k X)(p e r:ℕ)(he:e≤p):
    let N:=s+M f.volW;let m:=s+(M f.volW-(f.offset+1));let Ñ:=XSpace.Bare.chart G
    let α:=tale (D f.prev).dine;let β:=relativeC A Ñ N m (N-m)
    let V:=verseI A Ñ m N k X
    (∀n,WilsonIndependentNotebookMarkHear.output C Z D f A s k X n e r=mix β (V.1 n) e r)→
    ∀ (Q J:Orders (Foot G)),
      (∀i≤p,∀u,0<u→Q i u=WilsonIndependentSpoutReportedQuiet.port A Ñ N (m+1) α i u)→
      (∀i≤p,J i=ranks (coarse G) (mix α X.2 i))→
      (C.devices Y G Z (sheet D) f).each k Q J e r=orders (coarse G) (mix β V.2) e r:=by
  intro N m Ñ α β V finite Q J old ink
  have age:m<N:=by dsimp only [m,N];have:=f.ok;omega
  have actual:=WilsonIndependentNotebookMarkHear.original C Z D f A s Y R simple k X auth p e r he
  have other:=bend_mixX ((Mer.Auth.verse A age simple (XSpace.Bare.chart_ratio G) auth).wing) β e r
  have exactRows:(fun n=>WilsonIndependentNotebookMarkHear.output C Z D f A s k X n e r)=fun n=>mix β (V.1 n) e r:=
    funext finite
  rw [exactRows] at actual
  have quote:=actual.exten other
  rw [cutoff (C.devices Y G Z (sheet D) f) old (Y':=orders (coarse G) (mix α X.2)) ink k he r]
  funext x
  have atx:=congrFun quote (coarse G∘x)
  change (C.devices Y G Z (sheet D) f).each k (WilsonIndependentSpoutReportedQuiet.port A Ñ N (m+1) α) (orders (coarse G) (mix α X.2)) e r ((coarse G).symm∘(coarse G)∘x)=_ at atx
  rwa [show (coarse G).symm∘(coarse G)∘x=x by funext i;exact (coarse G).symm_apply_apply _] at atx

end YM.Integration.WilsonIndependentNotebookMarkedReceiver
