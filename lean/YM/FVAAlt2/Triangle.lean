import YM.FVAAlt2.Linear
/-! Exact field adjustment. Assemble the actual PowerSeries resident stencils
connected inputs from independent inversion quotient tree physics. No per-ray choices
or horizon truncations inside this. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Billing
open MS MS.Koszul MS.Native MS.Native.Wilsonian MS.Native.Studio MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Cylinder.Lab MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom Swirl.Near MS.Fleet
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog Convolve Program
open Function Finset Filter Topology MeasureTheory Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open Precision PertExtension Ends AtomCert
open scoped PowerSeries ContDiff Classical
variable {G:Gauge}{n:Side}{W:Type}[LinearOrder W]
variable {P:ChartRatio G} (R:LocalRatio P)
local notation "N" => Wilson.Config G n
local notation "Z" => PowerSeries ℂ
variable {ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A : Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))
variable (V:W→Actor G)(s:Finset W) (t:Team)(y:ℝ)(c:W→Cover)(o:Cover)
local notation "p"=> isOdd (ι:=ι) (κ:=κ)
local notation "X1" => pullSeries (embeddingM A b) (posEnergy (style G (Stripped t) y) n true)
local notation "pf"=>Program.shift t y
set_option linter.unusedSectionVars false

-- pad for proof when computing expected rows. Always have the selected label as a default.
variable {S:W→Type}[∀ i,Fintype (S i)]
def pad (s:Finset W)(df:∀ i, S i)(u:(i:↥s)→S i.1) (i:W): S i:= if h:i∈s then u ⟨i,h⟩ else df i
lemma fan {R:Type}[CommSemiring R] (F: ∀ i, S i→ R)(df:∀ i,S i): (∏ i∈s,∑ j:S i,F i j)= ∑ u:(i:↥s)→ S i.val, ∏ i∈s,F i (pad s df u i):=by
  rw [← Finset.prod_attach s, ← show (univ:Finset (↥s))=s.attach from rfl,Fintype.prod_sum (f:=fun (i:↥s) (j:S i.val)=> F i.val j)]; refine Finset.sum_congr rfl fun u _=> ?_ ; rw [← Finset.prod_attach s]; refine Finset.prod_congr rfl (fun i _=>?_ ); rw [pad,dif_pos i.property]

variable (F:∀ i:W,S i→Dot G Cover)(d:∀ i:W,S i→ℕ)(Q:∀ i:W,S i→Wilson.Config G n→ℝ)(U:∀ i:W,S i→PowerSeries ℂ)
local notation "H"=>fun j:W=>wrap n (o+c j)
lemma single_stencil (X:W→ℕ→Dot G Cover)(k:W): stencil X H {k}=promote (posMark n (H k)) (X k):=by simp only [stencil,Finset.singleton_nonempty,↓reduceDIte,Finset.card_singleton,↓reduceIte,Finset.min'_singleton]; rfl -- include o c?
variable (h:∀ i (j:S i),AtomCert (wrap n (o+c i)) (F i j) (d i j) (Q i j))
local notation "q!"=> Com.forget p
local notation "E'"=>PowerSeries (Com p)
local notation "L"=> pullSeries (embeddingM A b)
local notation "v"=>propagator (κ:=κ) A
def rowK(i:W)(j:S i): E':= s4 p pf (Bos.upS ((h i j).atomSeries A))
-- avoid S spelling p_ from notations in binders below.
local notation "T1"=>rowK A t y c o F d Q h -- order check
set_option pp.all false
lemma rowSpelling(i:W)(j:S i): L (promote (posMark n (H i)) (substitute pf (Book.levels (d i j) (F i j))))= q! (T1 i j):= by
 rw [show promote (posMark n (H i)) _= _ from comm _ _ (posMark n (H i)),show L (substitute pf _) = _ from comm _ _ (pull (embeddingM A b)), rowK,s4_forget]; congr 1; exact (h i j).ptS A b -- inspect params

lemma font_prices (he: ∀ i, V i y= ∑ j:S i, scalS (U i j) (substitute (shift t y) (Book.levels (d i j) (F i j)))) : L (Font Draft.DotFlip (stencil (fun w=> V w y) H) s)= q! (∏ i∈s, ∑ j:S i,formScale p (U i j) * T1 i j):= by
 rw [← pull_font (embTie A b)]
 refine stencilL s _ ?_ ?_
 · intro i; rw [single_stencil,he i,map_sum,map_sum,map_sum]; refine sum_congr rfl fun j _=>?_
   rw [scal_comm, show L (scalS _ _) = _ from scal_comm (pull (embeddingM A b)) _ _, forget_R]; exact congrArg (scalS (U i j)) (rowSpelling A b t y c o F d Q h i j)
 intro X hX; unfold stencil; split; · simp only [map_zero]
 simp only [map_zero]

def κpoint (P:ChartRatio G) (w:∀ i:W,S i): Z:= PowerSeries.mk (substitute pf (fun k=> (↑(Fixed.treeMom P (∏ i∈s,Q i (w i)) (∑ i∈s,d i (w i)) k):ℂ))) -- explicit lift coefficients
include R in
lemma μruleX (hn:Admissible n)(w:∀ i:W,S i): Endμ v p X1 (q! (∏ i∈s,T1 i (w i))) (unpack (κpoint s t y d Q P w)):= by
 let Ξ i:= F i (w i); let D i:=d i (w i); let X:=Fixed.marks t Ξ D
 -- use Fixed.calibrated then pull as theorem
 obtain ht:=Fixed.calibrated R A b s hn (fun i:W=>h i (w i)) c o t y (fun _=>rfl)

 have hs(i:W)(j:ℕ): Symm Draft.DotFlip (X i y j).val:= by change Symm _ (substitute pf (Book.levels (D i) (Ξ i)) j).val; rw [rules,sum_stack]; apply Symm.sum; intro k _; exact (Fixed.levelsSymm _ (h i (w i)).sym _ _).smul _
 have hp(i:W)(j:ℕ):∃ k:ℤ,Limit (X i y j).val k:=by
    refine ⟨(j:ℤ)+D i,?_⟩; change Limit (substitute pf (Book.levels (D i) (Ξ i)) j).val _; rw [rules,sum_stack]; refine Limit.sum _ (fun k hk=> Limit.smul _ (Limit.up ( Limit.mod (Ξ i).val ((k:ℤ)+(D i:ℤ))) (by simp at hk; omega)))
 rw [slice_end A b t y c o X hs hp s,← pull_font (embTie A b)] at ht; rw [stencilL s (fun i=>T1 i (w i)) ?_ ?_] at ht
 · unfold κpoint unpack; simp only [PowerSeries.coeff_mk]; exact ht
 · intro i; rw [single_stencil c o]; exact rowSpelling A b t y c o F d Q h i (w i)
 intro s hs; unfold stencil; split; · simp only [map_zero]
 simp only [map_zero]

variable (df:∀ i,S i)
def treeReg (P:ChartRatio G) : Z:= ∑ u:(i:↥s)→ S i.val, (∏ i∈s,U i (pad s df u i))*κpoint s t y d Q P (pad s df u)


include R A b h
lemma PayReg (he:∀ i, V i y= ∑ j:S i, scalS (U i j) (substitute (shift t y) (Book.levels (d i j) (F i j)))) (hs:∀ i j, Symm Draft.DotFlip (V i y j).val) (hv: ∀ i j, ∃ k:ℤ,Limit (V i y j).val k)(hn:Admissible n): PhysicalSum G t y n true s c o V (unpack (treeReg s t y d Q U df P)) := by
 rw [slice_end A b t y c o V hs hv, font_prices A b V s t y c o F d Q U h he, fan s _ df,map_sum]; unfold treeReg; refine end_sum _ _ _ (fun g _=> ?_); rw [Finset.prod_mul_distrib,←map_prod,forget_R]; exact end_smul _ (μruleX R A b s t y c o F d Q h hn _) -- ordering
end YM.FVAAlt2.Billing
