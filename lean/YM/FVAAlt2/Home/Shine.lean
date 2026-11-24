import YM.FVAAlt2.Home.Uniform
/-! Real, precise in both shift direction AND interpretation of the bare
PS re-expression. These operations act on formal series. Actual trajectory comparisons
with running over a regulator schedule are separate objects. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Home.Profiles
open Function Set Filter Finset Lattice
open FormalOPE RG10.InversionTop
open PertExtension PertExtension.LatticePT PertExtension.LatticePT.Mixed PertExtension.Position
open Precision
open MeasureTheory MS MS.Koszul MS.Native MS.Menus MS.Book MS.Vista MS.Tide
open PowerSeries (C coeff constantCoeff)
open Book.Program
open scoped BigOperators Topology ContDiff PowerSeries
variable {B:Type}{G:Gauge}
local notation "R"=> PowerSeries ℝ
local notation "E"=> PowerSeries ℂ

def takeReal (p:PowerSeries ℂ): R:=PowerSeries.mk (fun j=> (coeff j p).re)
lemma proper_t (x:R): takeReal (into x)=x:=by ext1 i; rw [takeReal,PowerSeries.coeff_mk,into_coeff];rfl
lemma rein : Injective into:= LeftInverse.injective proper_t
def RSpec (p:PowerSeries ℂ): Prop := into (takeReal p)=p
namespace RSpec
lemma place (x:R): RSpec (into x):= by unfold RSpec; rw [proper_t]
lemma ref t {F:E}(ht:star (coeff t F)=coeff t F): coeff t (into (takeReal F))=coeff t F:=by rw [into_coeff, takeReal,PowerSeries.coeff_mk]; exact Complex.conj_eq_iff_re.mp ht
lemma real_co {F:E}(h:∀ t:ℕ,star (coeff t F)=coeff t F):RSpec F:= PowerSeries.ext (fun t=> ref t (h t))
lemma re_t {F:E}(h:RSpec F)(t): (↑((coeff t F).re):ℂ)= coeff t F:= by unfold RSpec at h; rw [← h]; simp
lemma constants(x:ℝ):RSpec (C (x:ℂ)):= by rw [←RG10.Position.into_C]; exact place _
lemma rooted {Q:E}(hQ:RSpec Q): Program.Rooted Q↔ constantCoeff (takeReal Q)=0:= by unfold Rooted; unfold RSpec at hQ; nth_rw 1 [← hQ]; rw [into_coeff, Complex.ofReal_eq_zero,PowerSeries.coeff_zero_eq_constantCoeff]
lemma shapes (t:Team)(j:ℝ): RSpec (Program.shift t j):= real_co (fun n=>(Program.shiftR t n).starv j) -- Runofs
lemma add {F H:E}(hp:RSpec F)(he:RSpec H): RSpec (F+H):= by unfold RSpec at hp he; rw [← hp,← he,← map_add]; exact place _
lemma mul {F H:E}(hp:RSpec F)(he:RSpec H): RSpec (F*H):= by unfold RSpec at hp he; rw [← hp,← he,← map_mul]; exact place _
lemma finSum {f:B→E}(s:Finset B)(h:∀ i∈s,RSpec (f i)): RSpec (∑ i∈s,f i):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simpa using place 0
 | insert a s ha ih=> rw [Finset.sum_insert ha]; exact add (h _ (by simp)) (ih (fun i hi=> h i (mem_insert_of_mem hi)))
lemma finProd {f:B→E}(s:Finset B)(h:∀ i∈s,RSpec (f i)): RSpec (∏ i∈s,f i):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simpa using place 1
 | insert a s ha ih=> rw [Finset.prod_insert ha]; exact mul (h _ (by simp)) (ih (fun i hi=> h i (mem_insert_of_mem hi)))
end RSpec

def revise (t:Team)(y:ℝ):PowerSeries ℝ:= takeReal (Program.shift t y)
lemma revise_zer(t:Team)(y:ℝ):constantCoeff (revise t y)=0:=(RSpec.shapes t y|>.rooted).mp (share ..)
lemma revise_one(t:Team)(y:ℝ):coeff 1 (revise t y)=1:=by rw [revise,takeReal,PowerSeries.coeff_mk,ann]; rfl
lemma tidy (t:Team)(y:ℝ)(p:R): Lobby.redo t y (into p)=into (PowerSeries.subst (revise t y) p) :=by
 set x:= revise t y; ext1 i; rw [into_coeff, AlignSeries.subst_finite (p:=x) (revise_zer ..), Lobby.redo]; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [PowerSeries.coeff_mk, Program.rules, Complex.ofReal_sum ]; refine Finset.sum_congr (by ext n; simp) fun j _=>?_ ; unfold cut Ends.unpack; rw [show Program.shift t y=into x from Eq.symm (RSpec.shapes t y), ←map_pow,into_coeff, into_coeff,Complex.ofReal_mul]; exact mul_comm ..
variable {W:Type}[LinearOrder W][Fintype W]{B:MS.Local.Physical.Deck G}{L:Labels.Frames G}{H:Source.Hol G}
open Lobby
variable (R':Lobby.Registry L H)(D:ChartRatio G)(p:W→ Rake.Label B) {n: Side}
set_option linter.unusedSectionVars false
lemma specPaid(x:W→Site n)(ε:ℝ): RSpec (Paid D R' x ε p):=by
 unfold Paid; rw [show (ε:ℂ)⁻¹ ^ wt p = ((↑(ε⁻¹ ^ wt p):ℂ)) from by push_cast; rfl ]; apply (RSpec.constants _).mul; refine RSpec.finSum _ fun i _=>?_ ;
 let wK(i:W)(j:JLit L (p i)):=γ R' (p i) j; refine RSpec.mul ?_ ?_
 · have he(i:W)(k:JLit L (p i)): star (wK i k)=wK i k:= Shop.value_real ..
   have hx: (∏ j:W,wK j (i j))= Complex.ofReal ((∏ j:W,wK j (i j)).re) := Eq.symm ( Complex.conj_eq_iff_re.mp (show star (∏ j:W,wK j (i j))=_ from by rw [star_prod]; exact prod_congr rfl fun j _=> he .. )); rw [hx]; exact RSpec.constants _
 exact RSpec.real_co (fun t=>by rw [ΦbaseT,PowerSeries.coeff_mk]; simp)
lemma specPrice {i:W}(ε y:ℝ) (P:MS.Land.Prescription B)(j: Billing.χ p i): RSpec (changePrice P y p ε i j):= by
 unfold changePrice; apply RSpec.mul _ (RSpec.real_co _); · rw [show (ε:ℂ)^((j.size:ℤ) - (p i).h) = ( (↑(ε^( (j.size:ℤ) - (p i).h)):ℂ) ) from by push_cast; rfl ]; exact RSpec.constants _
 intro n; rw [Billing.bore,PowerSeries.coeff_mk, oil]; simp
lemma specRedo(t:Team)(y:ℝ){p:E}(h:RSpec p):RSpec (redo t y p):=by unfold RSpec at h; rw [← h,tidy]; exact RSpec.place _
lemma realP (ε y:ℝ)(P:MS.Land.Prescription B)(x:W→Site n):RSpec (newEra D R' P y p x ε):= by unfold newEra; refine RSpec.finSum _ fun X _=> (RSpec.finProd _ (fun i _=> specPrice p ε y P (X i))).mul (specRedo _ y (specPaid R' D _ _ _))
lemma coinPixel {d:ℕ}(p:Fin d→Rake.Label B)(μ:ℝ)(P:MS.Land.Prescription B)(q:ℕ+)(m k:ℕ)(x:Grid.offsets q d m)(o:LatticePT.Native q m):
    (↑(pixelT μ D R' P q m k p x o).re:ℂ)=pixelT μ D R' P q m k p x o:= (realP R' D p _ _ P _).re_t k
end YM.FVAAlt2.Home.Profiles
