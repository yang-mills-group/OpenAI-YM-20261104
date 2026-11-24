import YM.Integration.WilsonIndependentSpoutOrdinaryTop
import YM.Integration.WilsonIndependentSpoutOrdinaryHaar

/-! The complete first bare conditional interaction before integrating the
ordinary tree links. The three enrolled families share the actual fine
and coarse fields and the selected center of the spring. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutOpeningPost
open Lattice Exterior RG WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Geometry.Field RegulatorIR.Laplace
open RegulatorIR.Prim RegulatorIR.Binding RegulatorIR.Diagram RegulatorIR.Diagram.Formal
open RegulatorIR.Oracle RegulatorIR.Ledger PowerSeries PertExtension.Series.Radial
open WilsonIndependentSpoutOrdinaryPlate WilsonIndependentSpoutOrdinarySpring
open scoped Classical BigOperators ContDiff Matrix
variable {G:Gauge}{f c:Side}(S:StepData c f)(F:Tree.Forest S.ratio)

private theorem cost {U:Type}[Fintype U](k e:ℕ)(g:Lawn U→ℝ):FiniteGen (sprig g k e) := by
  refine ⟨k+e+1,fun r hr=>?_⟩
  change shine (rye g (k+e)) r=0
  exact shine_dark (by omega)

private theorem scut {U:Type}[Fintype U](P Q:Gen ℝ U)(a:FiniteGen P)(b:FiniteGen Q):
    totalR (P-Q)=totalR P-totalR Q := by
  rw [sub_eq_add_neg,←neg_one_smul ℝ Q,visible_add a (finite_μ b (-1)),
    visible_μ b,neg_one_smul,sub_eq_add_neg]

private theorem fincut {U:Type}(P Q:Gen ℝ U)(a:FiniteGen P)(b:FiniteGen Q):FiniteGen (P-Q):=by
  rw [sub_eq_add_neg,←neg_one_smul ℝ Q];exact finite_add a (finite_μ b (-1))

private theorem inspect {U:Type}[Fintype U](g:Lawn U→ℝ)(hg:ContDiffAt ℝ ∞ g 0)
    (v:Lawn U)(k e:ℕ):MvPolynomial.eval v (totalR (sprig g k e))=
    coeff (k+e) (tale (fun t:ℝ=>g (t • v))) := by
  rw [sprig,visible_shine,←Blue.jet_apply,rayon,lore hg v,inscription,coeff_mk]
  rfl

private theorem linear {U V:Type}[Fintype U][Fintype V](M:Matrix U V ℝ)(v:Lawn V)
    (P:Gen ℝ U)(hp:FiniteGen P):MvPolynomial.eval v (totalR (fade M P))=
    MvPolynomial.eval (M *ᵥ v) (totalR P) :=by rw [fade_visible _ _ hp,cord_apply]

theorem original {X:Type}{D:X→ℕ}(t:Page D→Scale)(w:X)(bare:t (Page.opening D w)=Clocks.flat)
    (h:S.patch.Branches S.kernel G)(sq:Square F)
    {T:Branchix→Orders (KFoot G)}(V:Sphere S F Clocks.flat T)
    (M:Matrix (Woods G f) (Woods G c) ℝ)(z:Lawn (Joint G f c))
    (slice:WilsonIndependentSpoutOrdinaryHaar.Sliced S F (camber G M *ᵥ z))(e:ℕ)(pos:0<e):
    let u:=camber G M *ᵥ z
    let b:=rightArm z
    (∑ p:Edge (Site f),drums (T (.inl (WilsonIndependentSpoutOrdinarySpring.peg p)) e) e (joined u b))+
    (∑ p:Edge (Site c),drums (T (.inr (WilsonIndependentSpoutOrdinarySpring.peg p)) e) (e+2) (joined u b))+
    (∑ p:Face (Per f),drums (Circuit.mural G t w (base p) e) (e+2) (sample u)) =
       MvPolynomial.eval z (totalR (casePW S (XSpace.Bare.chart G) M (topW G f) e)) := by
  dsimp only
  rw [WilsonIndependentSpoutOrdinaryHaar.original S F sq Clocks.flat V _ slice _ e pos,
    WilsonIndependentSpoutOrdinarySpring.original S F h Clocks.flat V _ _ e pos,
    WilsonIndependentSpoutOrdinaryTop.original t w bare _ e pos]
  have af:FiniteGen (topW G f e):=by
    exact ⟨2+e+1,fun j hj=>by
      unfold topW lop;simp [show j≠0 by omega,sprig,shine_dark (by omega:2+e≠j)]⟩
  have a:=cost 0 e (unhaar (n:=f) (XSpace.Bare.chart G))
  have b:=cost 2 e (jointPen G S)
  have g:=fade_finite a (camber G M)
  have h₂:=fade_finite b (groundM G M)
  have ht:=fade_finite af (camber G M)
  unfold casePW
  simp only [Pi.sub_apply,scrub,if_neg pos.ne']
  rw [scut _ _ (fincut _ _ g h₂) ht,scut _ _ g h₂,map_sub,map_sub,
    linear _ _ _ a,linear _ _ _ b,linear _ _ _ af,
    inspect _ ((unhaar_green (XSpace.Bare.chart_ratio G)).of_le (by simp)) _ 0 e,
    inspect _ ((penSmooth G S h).of_le (by simp)) _ 2 e,Nat.zero_add,Nat.add_comm 2]
  have z':groundM G M *ᵥ z=tuple (camber G M *ᵥ z) (rightArm z):=by
    ext j;cases j with
    | inl j=>exact congr_fun (camIn G M z).1 j
    | inr j=>exact congr_fun (camIn G M z).2 j
  rw [z']
  simp only [Clocks.flat,one_mul]
  ring

end YM.Integration.WilsonIndependentSpoutOpeningPost
