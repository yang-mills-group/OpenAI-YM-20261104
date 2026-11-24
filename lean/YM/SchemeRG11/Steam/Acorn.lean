import YM.SchemeRG11.Steam.Cost
/-!
Ordered slots. d4 only, ordinary Lebesgue measure.
-/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.SchemeRG11.Steam
open Hot Maxwell Analysis Set MeasureTheory Metric Function Filter Cluster MSbar
open scoped Topology ContDiff BigOperators Real RealInnerProductSpace
local notation "Tri" => Nodes 4
abbrev Sl := List Axis

def sumBits (U V W : Sl) : List Bit := U.map (Prod.mk 0)++(V.map (Prod.mk 1)++W.map (Prod.mk 2))
lemma own_add (i : Eye) (b c : List Bit) : own i (b++c)=own i b ++ own i c := by
  induction b with
  | nil => simp [own]
  | cons a b ih => simp only [List.cons_append,own,ih]; split <;> rfl
lemma own_mk (i j:Eye)(l:Sl) : own i (l.map (Prod.mk j))=if i=j then l else [] := by
  induction l with
  | nil => simp [own]
  | cons a l ih => simp only [List.map_cons,own,ih]; split <;> rfl

variable (U V W : Sl) (p : Time) (hp : p∈tripod)

def orb (x : Tri) : ℝ := series (trio p) ((sumBits U V W).map atEye) x
def juice (x : Tri) (w : E4) := tint U p.1 (x 0-w) * tint V p.2.1 (x 1-w) * tint W p.2.2 (x 2-w)
lemma brick_eq (x : Tri) : juice U V W p x= vault (sumBits U V W) p x := by
  ext w; simp only [vault,sumBits,brick,own_mk,own_add,ite_true]; norm_num [Eye,Fin.ext_iff]; rfl
include hp
lemma juice_cost (x : Tri) : Integrable (juice U V W p x) volume := by rw [brick_eq]; exact vaults p hp _ _
lemma grape (x : Tri) : orb U V W p x= ∫ w,juice U V W p x w := by rw [brick_eq]; exact ruby p hp _ _
omit hp

def yolk (x : Tri) := ∫ p in tripod,orb U V W p x

lemma yolks (μ : ℝ) (x : Tri) : (yolk U V W x:ℂ) = finale μ ((sumBits U V W).map atEye) x := by
  simp only [yolk,finale,spin_four, orb, Function.comp_apply,Complex.ofRealCLM_apply,integral_complex_ofReal]

variable {x : Tri} (hx : x∈ clearance 4)
include hx
lemma oak : IntegrableOn (fun p=> orb U V W p x) tripod := by
  have e := (Cluster.fades (μ:=1) zero_lt_one ((sumBits U V W).map atEye) hx)
  simp_rw [spin_four] at e
  exact e.re
omit hx

lemma oak_c {Y : Type} [TopologicalSpace Y] {u : Y→Time} {v : Y→Tri} {y : Y} (hu : ContinuousAt u y) (hv : ContinuousAt v y) (h : 0<knot (u y)) : ContinuousAt (fun y=> orb U V W (u y) (v y)) y := by
  have hc:= crew (μ:=1) zero_lt_one ((sumBits U V W).map atEye) h hv hu (e:=fun _=>0) continuousAt_const rfl
  simp_rw [spin_four] at hc; exact Complex.continuous_re.continuousAt.comp hc

abbrev Zen := volume.restrict openZen
lemma tree_m : volume.restrict tripod = Zen.prod (Zen.prod Zen) := by
 rw [Measure.prod_restrict,Measure.prod_restrict]; rfl

/-- Distinct version of clearance. -/
lemma pantry {x y z : E4} (h : x≠y)(e : y≠z)(H : x≠z) : castEye x y z∈ clearance 4 := by
  intro i; fin_cases i <;> first
     | exact div_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h)) _) (by norm_num : (0:ℝ)<4)
     | exact div_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr e)) _) (by norm_num : (0:ℝ)<4)
     | exact div_pos (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr H.symm)) _) (by norm_num : (0:ℝ)<4)
end YM.SchemeRG11.Steam
