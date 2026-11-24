import YM.SchemeRG11.Sew.Reach
/-! Dressed voyage. rho factors mark three paired fare legs.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.SchemeRG11.Sew
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World Atoll Tree Acorn Outlook Banner
open Labels Long MvPolynomial Air North Wolt
open scoped Classical Pointwise
variable {I J:Type*}{G:Gauge} {T:Align.Itinerary}
local notation "D₁" => Atoll.land G
namespace Gate
variable {S:Subalgebra ℝ (I→ℝ)}{Z:Set (I→ Touch G)}
lemma unitG:Gate (D₁) S Z (fun _=>1):=by convert (Gate.billS (D₁) (Z:=Z) S.one_mem) using 1; funext i; exact (map_one MvPolynomial.C).symm
lemma sumG (p:J→ array I (Shaft G))(s:Finset J)(h:∀i∈s, Gate (D₁) S Z (p i)):Gate (D₁) S Z (fun k=>∑i∈s,p i k):=by induction s using Finset.induction_on with
 | empty=>rw [show (fun k=>∑ i∈(∅:Finset J),p i k)=0 from by simp;rfl]; apply Gate.swell
 | insert i s w ih=> simp_rw [Finset.sum_insert w]; exact Gate.addS _ (h i (by simp)) (ih fun i hi=> h i (by simp [hi]))
lemma unityScale (u:ℝ) {p:array I (Shaft G)}(h:Gate (D₁) S Z p): Gate (D₁) S Z (fun i=>u • p i):= scales (D₁) (S.algebraMap_mem u) h
lemma guest (p:pLabel G)(u:I→ Key G→Touch G)(h:∀i:Key G,∀w∈Z,(fun k=>(D₁).bed (u k i) (w k))∈ S): Gate (D₁) S Z (fun i=>vary (u i) p):=by induction p using MvPolynomial.induction_on with
 | C c=> simp_rw [vary_C]; exact billS _ (S.algebraMap_mem c)
 | add a b ha hb=> simp only [_root_.map_add]; exact addS _ ha hb
 | mul_X a i p=> rw [mul_comm a]; simp_rw [map_mul,vary_X]; exact trunks _ p (h i)

variable (T)(j t:Axis)(m:I→ℕ)(z:I→ Cover)(ρ:I→ℝ)
def Lots := ∀ {n:ℕ}{q:Touch G}, q∈Stepper G n →∀w∈Z,(fun i=>(D₁).bed ((ρ i*T.gap (m i) ^(-(n+1:ℤ))) • flex (z i) q) (w i))∈S
lemma crust {p:array I (Shaft G)}(h:Lots (Z:=Z) (S:=S) T m z ρ)(hp: Gate (D₁) S Z p): Gate (D₁) S Z (fun i=> (ρ i ^ 3 * T.gap (m i)^(-4:ℤ)) • (Tree.cost (z i) j t *p i)):=by
 let B (q:I):=ρ q * T.gap (m q)^(-1:ℤ)
 let E(u:I)(i:Tree.FourSteps)(c:G.ColorIndex):= B u • tongue (z u) j t i c
 let A (q:I):=ρ q * T.gap (m q)^(-2:ℤ)
 let M (u:I)(c:G.ColorIndex):= A u • intake (z u) j t c
 have HE(i:Axis)(g:G.ColorIndex){f:array I (Shaft G)}(hx:Gate (D₁) S Z f):Gate (D₁) S Z (fun q=>leaf (E q i g)*f q):=by
    refine trunks (D₁) hx (fun w hw=>?_); simp_rw [E, show ∀ x, tongue (z x) j t i g=flex (z x) (tongue (0:Cover) j t i g) from fun x=> (speaks ..).symm]; exact h (blank_step _) w hw
 have HM(g:G.ColorIndex){f:array I (Shaft G)}(hx:Gate (D₁) S Z f): Gate (D₁) S Z (fun q=>leaf (M q g)*f q):=by
    refine trunks (D₁) hx (fun w hw=>?_); unfold M; simp_rw [show ∀ x,intake (z x) j t g= flex (z x) (intake (0:Cover) j t g) from fun x=> (protrude ..).symm]; exact h (high_i j t 0 g) w hw -- exponent mismatch casting
 have hz(s v:Axis)(a b:G.ColorIndex):Gate (D₁) S Z (fun i=> (B i*B i) • staple (z i) j t a b s v * p i):=by
    unfold staple; by_cases hu:s<v
    · simp only [hu,↓reduceIte]; convert HE s a (HE v b hp) using 1; funext i; simp only [E,map_smul]; rw [smul_mul_assoc,← smul_smul,smul_mul_assoc,smul_mul_assoc,mul_smul_comm,mul_assoc] -- repair
    simp only [hu,↓reduceIte,smul_zero,zero_mul]; exact swell _ _
 have ht (g:G.ColorIndex):Gate (D₁) S Z (fun i=> (B i * B i) • oreL (z i) j t g * p i):=by
    simp_rw [oreL,stockpile, Finset.smul_sum,Finset.sum_mul]; apply sumG (p:=fun s i=> _ )
    intro s _; apply sumG _ _; intro v _; apply sumG _ _; intro c _; apply sumG _ _; intro a _; convert unityScale (Triangle.colorF c a g) (hz s v c a) using 1; funext i; rw [smul_comm (B i * B i),smul_mul_assoc]
 by_cases H:j<t
 · have hc(i:I):ρ i^3*T.gap (m i)^(-4:ℤ)=A i*(B i*B i):=by unfold A B; rw [← show (-1:ℤ)+ -1=-2 from by decide,zpow_add₀ (T.positive _).ne']; rw [show (-4:ℤ)= (-1+-1)+(-1+-1) by norm_num]; rw [zpow_add₀ (T.positive _).ne',zpow_add₀ (T.positive _).ne']; ring -- fix
   unfold Tree.cost; simp only [if_pos H, hc, smul_mul_assoc]; simp_rw [smul_comm _ (1/2:ℝ) _, Finset.sum_mul, Finset.smul_sum]; -- extract sum
   apply sumG _ _; intro a _; convert unityScale (1/2:ℝ) (HM a (ht a)) using 1; funext i; simp only [M,map_smul]; simp [MvPolynomial.smul_eq_C_mul]; ring -- extends
 rw [show (fun i=> (ρ i ^ 3 * T.gap (m i)^(-4:ℤ)) • (Tree.cost (z i) j t *p i))=0 from by funext i; rw [Tree.cost,if_neg H,zero_mul,smul_zero];rfl]; apply swell
end Gate
end YM.SchemeRG11.Sew
