import YM.RG11Proof.Fields.Array
import YM.RG11Proof.Jets.Complex
/-! Rotating profiles and full complex separated predictions. No pointwise
or geometry derivative precision consequences without additional estimates.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Labels Function Set
open YM.PertExtension.Position -- careful names
open YM.Pert.Position (E)
open scoped Classical BigOperators ContDiff

variable {G : Gauge}{F:Frames G}
namespace ShapeReport
variable (A:ShapeReport G F) {e:ℕ}(B:Basis F e)

def fullAt : ArrayAt B.J ℂ form:=fun v=>PowerSeries.mk (fun k=>A.table k e v.1.order v.1.test (B.b ∘ v.2))

@[simp] theorem full_real (i:point B): part Jets.real (A.fullAt B i)=A.realAt B i:=by ext1 l;simp [realAt,fullAt,Function.comp_def,Jets.real]

def twist (x : Place): Place:=⟨x.order,-Complex.I • x.test⟩
def turn (x : point B):point B:=⟨twist x.1,x.2⟩

@[simp] theorem full_imag (i:point B): part Jets.imag (A.fullAt B i)=A.realAt B (turn B i):=by
   ext1 l
   simp only [component,realAt,fullAt,twist,turn,coeff_mk]
   change (A.table l e i.1.order i.1.test (B.b ∘ i.2)).im=
     ((A.table l e i.1.order (-Complex.I • i.1.test)) (B.b ∘ i.2)).re
   rw [map_smul,_root_.smul_apply,smul_eq_mul]; simp

theorem match_full {Q : ShapeReport G F} {p : Change ℝ B.J} (hc : Anchored p.g) {n}
    (h : Formal.ArrayThrough n (A.realAt B) (p.act (Q.realAt B))) :
    Formal.ArrayThrough n (A.fullAt B) ((toComplex p).act (Q.fullAt B)) := by
   apply complex_derives p hc
   · simp_rw [full_real]; exact h
   intro v
   simp_rw [full_imag]
   exact h (turn B v)

local notation "Z"=> E F e
local notation "ps"=> PowerSeries ℂ
/-- The report on the untested-in-fields tuple (still tested in positions). -/
def answers {r : ℕ} (f:Test r) (v:Fin r→Z) := PowerSeries.mk fun k=> A.table k e r f v

def combine {r:ℕ} (Q:(Fin r→B.J)→ps)(v:Fin r→Z): ps :=
    ∑ z: Fin r→B.J, PowerSeries.C (∏ i,B.b.equivFun (v i) (z i))* Q z

/-- Conversion on arbitrary input fields. Equivalently extend the algebra by
series-valued fields, applying `Z(t)` to each input then extended `answers`.
`predictions` is precisely this expression, no independence of growing field
horizons implicit in the use of the l1 sums. -/
def predictions {r:ℕ} (p:Change ℝ B.J) (f:Test r) (v:Fin r→Z): ps:=
  combine B (fun z=> (toComplex p).act (A.fullAt B) ⟨⟨r,f⟩,z⟩) v

theorem decodes {r} (f:Test r)(v:Fin r→Z):
    A.answers f v=combine B (fun z=> A.fullAt B ⟨⟨r,f⟩,z⟩) v := by
  ext1 k; simp only [answers,combine,fullAt,coeff_mk,map_sum,coeff_C_mul]
  conv_lhs=>rw [←funext fun i=>B.b.sum_equivFun (v i)]
  rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ]
  simp only [MultilinearMap.map_smul_univ,smul_eq_mul]; rfl

theorem along_all_fields {Q:ShapeReport G F} {p:Change ℝ B.J} (hp : Anchored p.g){n}
    (h : Formal.ArrayThrough n (A.realAt B) (p.act (Q.realAt B))) {r} (f:Test r)(v:Fin r→Z):
    Through n (A.answers f v) (Q.predictions B p f v):= by
   have he:=match_full A B hp h
   rw [A.decodes B]
   exact Through.sum (fun i _=> (Through.refl _).mul (he _))
end ShapeReport
end YM.RG11.Fields
