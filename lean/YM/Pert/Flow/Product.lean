import YM.Pert.Flow.Prices
/-! `qgr` stability estimates, in both matrix directions on a unit log-length lattice. Real matrices with both measuring and fixed field bases sorted by energy/grade. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Pert.Flow
open Function Filter Topology Price Finset Layer
open scoped Topology Classical
variable {V : Type*} [Fintype V]

def normalizeCols (A : TimeArray V) (e : V→ℝ) : TimeArray V :=
     fun n i j => A n i j * (e j)⁻¹^n
def normalizeRows (A : TimeArray V) (e : V→ℝ) : TimeArray V :=
     fun n j i => (e j)^n * A n j i
def nextRows (A : TimeArray V) : TimeArray V := fun n=>A (n+1)

structure Orientations (e : V→ℝ) (S A T U : TimeArray V) : Prop where
     inverse : stepProduct A S = (fun _=>eye) ∧ stepProduct S A=(fun _=>eye)
     increment : stepProduct T U = (fun _=>eye) ∧ nextRows S=stepProduct T S
     filtered n i j : e j < e i → S n i j=0 ∧ A n i j=0
     rates : StepEstimate e T

lemma normalizeRead {e : V→ℝ} {S T : TimeArray V} (h : nextRows S = stepProduct T S) (n i j) :
   normalizeCols S e (n+1) i j = (∑ k, T n i k * normalizeCols S e n k j)/e j := by
   rw [sum_div]
   have he := congrFun (congrFun (congrFun h n) i) j
   dsimp only [normalizeCols,stepProduct,nextRows] at *
   rw [he, pow_succ, sum_mul]
   exact sum_congr rfl fun k _ => by rw [div_eq_mul_inv];ring

variable {e : V → ℝ} {S A T U : TimeArray V} (h : Orientations e S A T U)
include h
lemma inverseFlow : nextRows A = stepProduct A U := by
    have hA : stepProduct (nextRows A) (stepProduct T S)=(fun _=>eye) := by
       rw [←h.increment.2]; change nextRows (stepProduct A S)=_
       rw [h.inverse.1]; rfl
    have ht:= congr_arg (fun C:TimeArray V=> stepProduct C A) hA
    change stepProduct (stepProduct (nextRows A) (stepProduct T S)) A = _ at ht
    rw [Layer.leftUnit,←stepAssoc,←stepAssoc, h.inverse.2,Layer.rightUnit] at ht
    have hh := congr_arg (fun C:TimeArray V=>stepProduct C U) ht
    change stepProduct (stepProduct (nextRows A) T) U = _ at hh
    rw [←stepAssoc,h.increment.1,Layer.rightUnit] at hh
    exact hh
lemma matrixLaws : Law e (normalizeCols S e) T ∧ Law (dualEnergy e) (Layer.transpose (normalizeRows A e)) (Layer.transpose U) := by
    constructor
    · exact StepEstimate.layers h.rates (normalizeRead h.increment.2) (fun n i j he=> by
         dsimp only [normalizeCols]; rw [(h.filtered n i j he).1,zero_mul])
    refine StepEstimate.layers (inverse_step h.rates h.increment.1) ?_ (fun n i j hij=> by
       have he := h.rates.pos j
       have hf: e i < e j:= (inv_lt_inv₀ he (h.rates.pos i)).1 hij
       dsimp only [Layer.transpose,normalizeRows]; rw [(h.filtered n j i hf).2,mul_zero])
    have hi : Layer.transpose (normalizeRows A e) = normalizeCols (Layer.transpose A) (dualEnergy e) := by
       funext n i j; simp [Layer.transpose,normalizeRows,normalizeCols,dualEnergy,mul_comm]
    rw [hi]
    exact normalizeRead (funext fun n=> funext fun i=> funext fun j=> by
       exact (congrFun (congrFun (congrFun (inverseFlow h) n) j) i).trans (sum_congr rfl fun k _=> mul_comm _ _))

theorem rowPrices (j i : V) :
    tame (fun n=>normalizeCols S e n i j) ∧ tame (fun n=>normalizeRows A e n j i) :=
    ⟨tame_column (matrixLaws h).1 j i,tame_column (matrixLaws h).2 j i⟩
theorem offPrices {j i : V} (he: e i < e j) :
    flat (fun n=>normalizeCols S e n i j) ∧ flat (fun n=>normalizeRows A e n i j) :=
    ⟨gap_decay (matrixLaws h).1 he,gap_decay (matrixLaws h).2 ((inv_lt_inv₀ (h.rates.pos j) (h.rates.pos i)).2 he)⟩
theorem couplingPrices {B:ℝ} (hB:B>0) {u : ℝ → ℝ} (hS : Signature B u) (j i:V) :
     let u' (n:ℕ):=u n
     couplingTame u' (fun n=>normalizeCols S e n i j) ∧ couplingTame u' (fun n=>normalizeRows A e n j i) :=
     ⟨pricedUpon hS (rowPrices h j i).1 hB,pricedUpon hS (rowPrices h j i).2 hB⟩
theorem couplingLax {B:ℝ} (hB:B>0) {u : ℝ → ℝ} (hS : Signature B u) {j i:V} (hij:e i < e j) :
     let u' (n:ℕ):=u n
     couplingFlat u' (fun n=>normalizeCols S e n i j) ∧ couplingFlat u' (fun n=>normalizeRows A e n i j) :=
     ⟨flatUpon hS (offPrices h hij).1 hB,flatUpon hS (offPrices h hij).2 hB⟩
end YM.Pert.Flow
