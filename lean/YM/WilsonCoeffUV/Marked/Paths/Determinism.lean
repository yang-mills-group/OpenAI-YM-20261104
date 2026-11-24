import YM.WilsonCoeffUV.Marked.Paths.RealExtent
import YM.WilsonCoeffUV.Marked.Paths.SpanMeasure
/-!
# Root family permit deterministic common presentation in strong markup sense
 At arity J FIXED retain J passive. Passive slots include weight cost own
 root + one stub. Concrete Awe interpretation by sums, no infinity implicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Rolls
open Gauge Power PowerSeries Matrix Filter Lattice Laurent Exterior Precision Wilson RG Tree Bloch Stationary
open Function Blue Bank Fountain Soil Source Source.Drops Labels Cosmos Planned.PrimaryIntegral295 Place Carrier Bank.Carp Bank.Mosaic Bank.Mosaic.Near
open scoped Topology ContDiff BigOperators Classical
open Wheel Wheel.Mark Wheel.Express Embroider
open MeasureTheory Wheel.Address
variable {G:Gauge}{n:Side}{k h r t i j l e m b:ℕ}{s v u A B:ℝ}
variable {V W I α β ι:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{S J: Finset I}{c:I}{o:Cover}{D:I→ℕ}

def sprigB (P:Comet G V k)(i:Stationary.Ink G k): Atom G k:= ⟨P.sl, picker G k *ᵥ (Pi.single i 1)⟩
omit [NormedSpace ℝ V][NormedAddCommGroup V] in
lemma sprigB_t (P:Comet G V k)(i:Stationary.Ink G k): (sprigB P i).Invariant:=picks _
def monthly (G:Gauge)(k:ℕ):ℝ:= Stationary.reserve (picker G k)
lemma monthly_o (G:Gauge)(k:ℕ):0≤monthly G k:= pay_reserve _
omit [NormedSpace ℝ V][NormedAddCommGroup V] in
lemma sprigB_c (P:Comet G V k)(i j): (sprigB P i).coeff j= picker G k j i:=by change Matrix.mulVec _ _ _=_; unfold Matrix.mulVec; simp
omit [NormedSpace ℝ V][NormedAddCommGroup V] in
lemma sprigB_hi (P:Comet G V k)(i:Stationary.Ink G k): (sprigB P i).magnitude≤ monthly G k:= Finset.sum_le_sum fun j _=> by rw [sprigB_c]; exact Finset.single_le_sum (f:=fun v=>‖picker G k j v‖) (fun _ _=> norm_nonneg _) (Finset.mem_univ i)
omit [NormedSpace ℝ V] in
lemma sprigB_price (P:Comet G V k): ∑ i, ‖P.wage i‖*(sprigB P i).budget s≤ monthly G k*integerP P s:=by
    unfold integerP; rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _; unfold Atom.budget; rw [ray_m,one_mul];
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (sprigB_hi P i) (by positivity)) (norm_nonneg _)).trans_eq ?_
    rw [show (sprigB P i).length=(rayOne P i).length from rfl, mul_left_comm]
lemma dip_reads (P:Comet G V k)(L:V→L[ℝ]ℝ)(p:shadeStar P)(x): (dip P L).poly x=∑ i,L (P.wage i)*(sprigB P i).poly x:=by
   unfold Atom.poly; let C:= dip P L
   have he j: C.coeff j= ∑ i,L (P.wage i)*(sprigB P i).coeff j:=by
      have h:= keeps C.coeff (p L); rw [←h]; unfold Matrix.mulVec dotProduct; apply Finset.sum_congr rfl; intro i _; rw [sprigB_c]; exact mul_comm _ _
   simp_rw [show ∀ j,(dip P L).coeff j = ∑ i,L (P.wage i)*(sprigB P i).coeff j from he, Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro i _; ring
-- explicit Reg sk measures including alias. Pot R.label read threshold use next consumer.

def Barn (P: Comet G (Pen D J) k)(A: Stationary.Ink G k → Measure (Sky D)): Prop:=∀ i,Awe (P.wage i) (A i)
def lease (P: Comet G (Pen D J) k) (A: Stationary.Ink G k→ Measure (Sky D))(s:ℝ) :=∑ i,(A i).real Set.univ *(sprigB P i).budget s
lemma pact (P:Comet G (Pen D J) k):∃ A,Barn P A:= by choose A h using fun i=> showers (P.wage i); exact ⟨A,h⟩
lemma money (P:Comet G (Pen D J) k)(A:Stationary.Ink G k→ Measure (Sky D))(h:Barn P A)(s:ℝ): lease P A s ≤ monthly G k * integerP P s:=by unfold lease; simp_rw [show ∀ i,(A i).real Set.univ=‖P.wage i‖ from fun i=>(h i).2.2.1]; exact sprigB_price P
lemma packet (P:Comet G (Pen D J) k)(x:Case D)(A:Stationary.Ink G k→ Measure (Sky D))(p:shadeStar P)(h:Barn P A)(U:Config G n)(o:Site n): (dip P (touch x J)).unmasked U o=∑ i, (∫ y,mica x J y ∂(A i))*(sprigB P i).unmasked U o:=by
   rw [Atom.unmasked, dip_reads _ _ p]; apply Finset.sum_congr rfl; intro i _; rw [(h i).2.2.2 x]; rfl
-- Poly-admission fee M scales. earlier labels reflect orientation before Probe. reconstruction unmasked.

def BlazeCap (P:Robes G (Pen D J) k) (z:I→ Cover)(c:I) (e:ℕ) (s A:ℝ):Prop:=∀ j<e,∀ r: Fin (k+j+1),∃ L:RadP G r.val→ Stationary.Ink G r.val→ Measure (Sky D),(∀ i,Barn (P j r i) (L i)) ∧ SumBudget (fun i=> Real.exp (s*feeH z c J)*lease (P j r i) (L i) s) A
lemma stripV_n (P:Comet G (Pen D J) k)(x):0≤ lease P x s:=Finset.sum_nonneg (fun i _=>mul_nonneg (by exact ENNReal.toReal_nonneg) (mul_nonneg (Finset.sum_nonneg fun _ _=> abs_nonneg _) (by positivity)))
def glacier (G:Gauge)(k e:ℕ):=∑ i∈Finset.range (k+e+1), monthly G i
lemma gentle (G:Gauge)(k e:ℕ):0≤glacier G k e:=Finset.sum_nonneg (fun _ _=> monthly_o ..)
lemma sparkle (P:Robes G (Pen D J) k) (z:I→Cover)(c:I)(h:tenure P J z c e s A)(he:0 ≤ A): BlazeCap P z c e s (glacier G k e*A):=by
    intro i hi r; choose F f using fun j=> pact (P i r j); let R:= monthly G r.val
    refine ⟨F,f, cap_raise (Work.F08.budget_minor (cap_scale (h _ hi r) (show 0≤R from monthly_o ..)) (fun i'=>mul_nonneg (by positivity) (stripV_n _ _)) (fun j=>?_)) (mul_le_mul_of_nonneg_right ?_ he)⟩
    · exact (mul_le_mul_of_nonneg_left (money _ _ (f _) s) (by positivity)).trans_eq (mul_left_comm ..)
    unfold R glacier; have hz:r.val< k+i+1:= r.isLt; exact Finset.single_le_sum (fun i _=> monthly_o G i) (Finset.mem_range.mpr (show r.val<k+e+1 from by omega))
-- packet legality contracts translation, μ.

end YM.WilsonCoeffUV.Mer.Rolls
