import YM.Integration.WilsonMeasuredPointBareWords
import YM.Integration.WilsonIndependentCollarPointBill
import YM.Integration.WilsonOriginalPublicTrialFigure

/-! The unsuspended finite curvature words of the measured public trial, on every genuine side. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftFigures
open Function Finset Lattice Laurent Wilson RG Source Labels Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Winding WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PertExtension ActualRunCurvaturePackets NativeCurvatureTensor
open IndependentSourcePathFamily OriginalMarkedSourceComet
open private comet atom from YM.Integration.IndependentSourcePathFamily
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι] [DecidableEq ι]
variable (R:Run G)(D d:ι→ℕ)
local notation "F" i:max=>R.family.labels.level (d i)

def seed (b:∀i,(F i).Index)(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(i:ι)
    (m:WilsonMeasuredPointBareWords.Term R (d i) (b i)):Seed G (D i):=
  ⟨WilsonMeasuredPointBareWords.rank R (d i) (b i) m,
   WilsonMeasuredPointBareWords.rank R (d i) (b i) m,
   (WilsonMeasuredPointBareWords.atom R (d i) (b i) m).leg,
   fun j=>(word m.val j).2,WilsonMeasuredPointBareWords.weight R (d i) (b i) m,
   Complex.reCLM,κ i,pt i⟩

def stencil (b:∀i,(F i).Index)(κ:(i:ι)→Knob (D i))(pt:ι→Chamber):Outerm G D:=
  independent (seed R D d b κ pt)

private theorem token {r:ℕ}(p:Fin r→RG.Slot)(c:Fin r→G.ColorIndex)(a:ℝ)
    {n:Side}(z:Site n)(U:Config G n):
    a*(WilsonOriginalProjectedCurvatureAtom.atom c p).unmasked U z=
      (colour p c (a:ℂ) Complex.reCLM).unmasked U z:=by
  change a*(WilsonOriginalProjectedCurvatureAtom.atom c p).poly (fun j=>(p j).atSite U z)=
    (colour p c (a:ℂ) Complex.reCLM).poly (fun j=>(p j).atSite U z)
  rw [colour_poly,←WilsonOriginalProjectedCurvatureAtom.read c p]
  simp

private theorem selected {α:Type}[Fintype α]{β:α→Type}[∀i,Fintype (β i)]
    (q:∀i,β i)(f:∀i,β i→ℝ)(hl:∀i b,0≤f i b):
    (∑i,f i (q i))≤∑i,∑b,f i b:=
  sum_le_sum fun i _=>single_le_sum (fun b _=>hl i b) (mem_univ (q i))

omit [Fintype ι] [DecidableEq ι] in
theorem field (b:∀i,(F i).Index)(κ:(i:ι)→Knob (D i))(pt:ι→Chamber)(i:ι)
    {n:Side}(z:Site n)(U:Config G n):
    ((R.family.localSection (d i)).places (Pi.single (b i) 1) z U).re =
      ∑m,(atom (seed R D d b κ pt i m)).unmasked U z:=by
  rw [WilsonMeasuredPointBareWords.placed]
  apply Finset.sum_congr rfl
  intro m _
  exact token (G:=G) _ _ _ z U

def cost (e:ℕ)(w:ℝ)(i:ι)(u:(F i).Index)(m:WilsonMeasuredPointBareWords.Term R (d i) u):ℝ:=
  let a:=WilsonMeasuredPointBareWords.atom R (d i) u m
  let p:=colour a.leg (fun j=>(word m.val j).2)
    (WilsonMeasuredPointBareWords.weight R (d i) u m:ℂ) Complex.reCLM
  ∑l:Fin (d i+e+1),WilsonIndependentCollarPointBill.atoms p w *
    |flour G (steep w) (WilsonMeasuredPointBareWords.rank R (d i) u m) l.val|

omit [Fintype ι] [DecidableEq ι] in
theorem nonnegative (e:ℕ)(w:ℝ)(i:ι)(u:(F i).Index)(m:WilsonMeasuredPointBareWords.Term R (d i) u):
    0≤cost R d e w i u m:=by
  unfold cost WilsonIndependentCollarPointBill.atoms
  exact sum_nonneg fun _ _=>mul_nonneg (sum_nonneg fun _ _=>mul_nonneg (norm_nonneg _) (abs_nonneg _)) (abs_nonneg _)

theorem original (e:ℕ){w:ℝ}(hw:0<w):
    ∃B:ℝ,1≤B ∧ ∀(b:∀i,(F i).Index)(κ:(i:ι)→Knob (D i))(pt:ι→Chamber),
      Wellness d (stencil R D d b κ pt) ∧ ∀y S,shingled y S (stencil R D d b κ pt) e w B:=by
  let B:=1+∑i,∑u:(F i).Index,∑m,cost R d e (4*w) i u m
  have one:1≤B:=by
    apply le_add_of_nonneg_right
    exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun _ _=>nonnegative .. 
  refine ⟨B,one,?_⟩
  intro b κ pt
  let X:=seed R D d b κ pt
  have grade (i m):(X i m).rank≤d i+(X i m).head:=Nat.le_add_left ..
  have pays (i m):IndependentSourcePathFamily.charge X d e (4*w) i m≤cost R d e (4*w) i (b i) m:=by
    unfold IndependentSourcePathFamily.charge cost
    apply sum_le_sum
    intro l _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (WilsonIndependentCollarPointBill.bare
      (atom (X i m)) (κ i) (pt i) (4*w)) (abs_nonneg _)
  have paid:bill X d e (4*w)≤B:=by
    calc
      _ ≤ ∑i,∑m,cost R d e (4*w) i (b i) m:=sum_le_sum fun i _=>sum_le_sum fun m _=>pays i m
      _ ≤ ∑i,∑u:(F i).Index,∑m,cost R d e (4*w) i u m:=
        selected b (fun i u=>∑m,cost R d e (4*w) i u m)
          (fun i u=>sum_nonneg fun m _=>nonnegative R d e (4*w) i u m)
      _ ≤ B:=le_add_of_nonneg_left zero_le_one
  refine ⟨(OriginalCoverReanchoring.deposited X grade).1,?_⟩
  intro y S l hl r
  have pay:=preblock X (k:=d) y univ e (w:=4*w) (by positivity) grade
  have row:=pay.2.2.2 S (Finset.subset_univ _) l hl r
  rw [show steep (4*w)=w by unfold steep;ring] at row
  exact row.more (pow_le_pow_left₀ pay.1 paid _)

end YM.Integration.WilsonOlderFreshSoftFigures
end
