import YM.Integration.SignedRegisteredKernelPolynomial
import YM.Integration.SignedJointSourceMoments

/-! Exact full finite marked generator and Wick program for the entire explicitly rendered bank. Every perturbative polynomial has the same chosen Gaussian variables, native vacuum and independent marked input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedRegisteredMarkedProgram
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries Multi Marker
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants Next.SectorChange FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {ι : Type} [DecidableEq ι] [Fintype ι] {G : Gauge} {D : ι→ℕ} (P : SignedJointSourceMoments.Bank G D) (b k : ι→ℕ)
variable {c f : Side} {S : StepData c f} {h : Clip} {path : PathData G} {O : ChartRatio G} (K : Bulk.Kernel S h path O) (F : Forest S.ratio)
variable (M : Matrix (Woods G f) (Woods G c) ℝ) (B : fieldDir G c 1)
local notation "D₀" => fderiv ℝ (K.b F) 0

private def gaussian : (Precision.Key F G→ℝ)→L[ℝ] Lawn (Active G F) :=
  (vcloth S F G).symm.toContinuousLinearMap.comp gaugeCount.toContinuousLinearMap

/-- Actual colored linear substitution, retaining all independent uncontracted Gaussian variables and the chosen external field. -/
def letter : Active G F⊕Woods G c→ MvPolynomial (Precision.Key F G) ℂ
  | .inl a=>∑i,MvPolynomial.C (((gaussian F) (Pi.single i 1) a:ℝ):ℂ)*MvPolynomial.X i
  | .inr a=>MvPolynomial.C (((arm G c 1).symm B a:ℝ):ℂ)

def register : MvPolynomial (Active G F⊕Woods G c) ℝ→+* MvPolynomial (Precision.Key F G) ℂ :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp Complex.ofRealHom) (letter F B)

private theorem reading_letter (y : Precision.Key F G→ℝ) (j) : Cloud.paint y (letter F B j)=(SignedRegisteredKernelPolynomial.focus F B y j:ℝ) := by
  cases j with
  | inr a=>simp [letter,Cloud.paint,SignedRegisteredKernelPolynomial.focus]
  | inl a=>
    have h : (∑i,y i • Pi.single i (1:ℝ))=y := by funext j;simp [Pi.single_apply]
    have he := congrArg (fun g=>gaussian F g a) h
    simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul] at he
    simp only [letter,_root_.map_sum,_root_.map_mul,Cloud.paint,MvPolynomial.aeval_C,MvPolynomial.aeval_X]
    change (∑i:Precision.Key F G,((gaussian F (Pi.single i 1) a:ℝ):ℂ)*(y i:ℂ))=
      ((gaussian F y a:ℝ):ℂ)
    have hp : ∑i:Precision.Key F G,(gaussian F (Pi.single i 1) a)*y i=gaussian F y a := by
      simpa only [mul_comm] using he
    exact_mod_cast hp

theorem reading (y : Precision.Key F G→ℝ) (p : MvPolynomial (Active G F⊕Woods G c) ℝ) :
    Cloud.paint y (register F B p)= (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B y) p:ℝ) := by
  let h : ((Cloud.paint y).toRingHom.comp (register F B))=Complex.ofRealHom.comp (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B y)) := by
    apply MvPolynomial.ringHom_ext
    · intro x;simp [register,Cloud.paint]
    · intro x;simpa [register] using reading_letter F B y x
  exact DFunLike.congr_fun h p

variable (R : Census ι)

def colors (A : Case D) (vac : ℝ→ Config G f→ℝ) : Bulk.Colors R G f where
  vac := vac
  mark z g U := ∑i∈P.keys z.val.val,SignedRegisteredKernelPolynomial.primitive (dip (P.src z.val.val i) (touch A z.val.val)) 0
    (SignedJointSourceMoments.clearing b z.val.val+P.head z.val.val i-P.rank z.val.val i) g U
  power z := SignedJointSourceMoments.clearing b z.val.val

def center (A : Case D) (s : Finset ι) (n : ℕ) := register F B (coeff n (retool (shore S F M (D₀))
  (loom (camSlice G S F M) (readO A (SignedJointSourceMoments.given P s) f))))

/-- The unassumed exact marked input polynomial. The two native polynomials agree before covariance, integration and the connected logarithm. -/
theorem input (hs : ∀s i,i∈P.keys s→shadeStar (P.src s i)) (ha : ∀s i,i∈P.keys s→P.rank s i≤ mass k s+P.head s i)
    (hb : ∀s i,i∈P.keys s→P.rank s i≤SignedJointSourceMoments.clearing b s+P.head s i)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) (A : Case D) (vac : ℝ→ Config G f→ℝ) (z : Hot R) (n : ℕ) :
    let W:=colors P b R A vac
    Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.markFn S F W z) (W.power z+n)=center P K F M B A z.val.val n := by
  intro W
  apply Valence.Enlist.paint_inj
  intro y
  let s := z.val.val
  let u i : ℝ → Config G f → ℂ := SignedRegisteredKernelPolynomial.primitive (dip (P.src s i) (touch A s)) (0:Site f) (SignedJointSourceMoments.clearing b s+P.head s i-P.rank s i)
  have hjet (l : ℕ) : Assembly.jet (Bulk.markFn S F W z) l (Bulk.translated K F B y)=
      ∑i∈P.keys s,Assembly.jet (Bulk.posed S F (u i)) l (Bulk.translated K F B y) := by
    change Assembly.jet (fun v=>∑i∈P.keys s,Bulk.posed S F (u i) v) l _=_
    unfold Assembly.jet
    rw [iteratedFDeriv_fun_sum_apply (fun i _=>(SignedRegisteredKernelPolynomial.green F _ _ _).of_le (le_top (a:=((l:ℕ):WithTop ℕ∞))))]
    simp [smul_sum,u]
  rw [Assembly.reading]
  change Assembly.jet (Bulk.markFn S F W z) (W.power z+n) (Bulk.translated K F B y)=_
  rw [hjet]
  simp only [Bulk.translated]
  simp_rw [←Assembly.reading (Bulk.stage K F B) (Bulk.hinge F) y]
  have hi (i) (h:i∈P.keys s) := SignedRegisteredKernelPolynomial.coefficient K F M (P.src s i) (touch A s) B y (P.head s i)
    (SignedJointSourceMoments.clearing b s) (SignedJointSourceMoments.clearing b s+P.head s i-P.rank s i) n (by have := hb s i h;omega) hM
  rw [center,reading, SignedJointSourceMoments.given,read_Sum A f (fun i h=>aug_auth (P.src s i) (hs s i h) (ha s i h))]
  simp only [map_sum,Complex.ofReal_sum]
  exact sum_congr rfl hi

/-- The unmarked phase is the authentic physical Wilson phase, while every marked vertex comes from the independent source polynomial `center`. -/
def generator (A : Case D) (vac : ℝ→ Config G f→ℝ) (q : S.Choices) (r : ℕ) (s : Hot (Order.Board R r)) :=
  let n := (Join.right s.val).val.card
  (n.factorial:ℂ) • if (Join.left s.val).val.Nonempty then center P K F M B A (Join.left s.val).val n else
    Assembly.naked (Bulk.stage K F B) (Bulk.hinge F) (Bulk.geometric K F q (colors P b R A vac)) n

theorem funded (hs : ∀s i,i∈P.keys s→shadeStar (P.src s i)) (ha : ∀s i,i∈P.keys s→P.rank s i≤ mass k s+P.head s i)
    (hb : ∀s i,i∈P.keys s→P.rank s i≤SignedJointSourceMoments.clearing b s+P.head s i)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) (A : Case D) (vac : ℝ→ Config G f→ℝ) (q : S.Choices) (r : ℕ) :
    let W:=colors P b R A vac
    Order.logMarked (Bulk.Fk K F q W B r)=Order.logMarked (Cloud.prescription (K.covariance F q) (K.symm F q) 0 (generator P b K F M B R A vac q r)) := by
  intro W
  have he : Assembly.generator (Bulk.stage K F B) (Bulk.hinge F) W.power (Bulk.markFn S F W) (Bulk.geometric K F q W) r=
      generator P b K F M B R A vac q r := by
    funext s
    by_cases hc:(Join.left s.val).val.Nonempty
    · simp only [Assembly.generator,generator,dif_pos hc,if_pos hc]
      rw [input P b k K F M B R hs ha hb hM A vac]
    · simp [Assembly.generator,generator,hc,W]
  unfold Bulk.Fk Assembly.prescription
  rw [he]
end YM.Integration.SignedRegisteredMarkedProgram
