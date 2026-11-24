import YM.RegulatorIR.Cluster.Poster
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Use distance to the actual indicated support or union of supports. Allow
closed, not necessarily compact; can majorize supports as long as mutual
separation. Natural cost in coarse units disregards diameter of one support
in those units! This is crucial for joint estimates. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Metric Set Function Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Diagram Gradient Train
open scoped BigOperators Topology ENNReal NNReal Classical
variable {X:Type} {l d m:ℝ}{r s:ℕ} {S T:Set Room}

namespace Collapsed
-- tariff seen using distance collapsed to support. Safe even for empty.
def fare (hl:0<l)(u:ℕ)(S:Set Room): Tariff Room where
 road x y:=amount l u (dist (infDist x S) (infDist y S))
 unit _ _:=amount_unit hl u dist_nonneg
 own _:=by simp
 symm _ _:=by rw [dist_comm]
 tri _ _ _:=amount_tri (dist_triangle ..) hl u dist_nonneg dist_nonneg
lemma lip (hl:0<l)(u:ℕ)(S:Set Room)(x y:Room): (fare hl u S).road x y ≤ (native _ hl u).road x y:=by
 apply amount_mono hl
 rw [Real.dist_eq,abs_le]; constructor
 · have ht := infDist_le_infDist_add_dist (x:=y) (y:=x) (s:=S)
   linarith [dist_comm x y]
 have hh:= infDist_le_infDist_add_dist (x:=x) (y:=y) (s:=S); linarith

def realm (hl:0<l)(u:ℕ)(S:Set Room): Premium (fare hl u S) where
 mark x:= amount l u (infDist x S)
 unit _:= amount_unit hl u infDist_nonneg
 travel x y:=by
    apply amount_tri (z:=dist (infDist x S) (infDist y S)) ?_ hl u infDist_nonneg dist_nonneg
    rw [Real.dist_eq]; linarith [le_abs_self (infDist x S-infDist y S)]

lemma highest (hl:0<l)(u:ℕ)(S:Set Room)(x:X→Room)(z:Tuple X r)(c:ℝ≥0∞)(hc:1 ≤ c)(h:∀ i,amount l u (infDist (x (z i)) S) ≤ c): ((realm hl u S).uses x).width z≤c:=by
 apply Premium.width_le _ ?_ h
 apply Tariff.diameter_le _ hc; intro i j
 let a:=infDist (x (z i)) S; let b:=infDist (x (z j)) S
 have ha:0 ≤ a:=infDist_nonneg; have hb:0≤ b:=infDist_nonneg
 change amount l u (dist a b)≤c; rw [Real.dist_eq]; cases le_total a b with
 | inl p=> apply le_trans _ (h j); apply amount_mono hl u; change |a-b| ≤ b;rw [abs_of_nonpos (by linarith)]; linarith
 | inr q=> apply le_trans _ (h i); apply amount_mono hl u; change |a-b| ≤ a;rw [abs_of_nonneg (by linarith)]; linarith
lemma regions (hl:0<l)(u:ℕ)(S T:Set Room)(h:S⊆T)(hs:S.Nonempty)(x:X→Room)(z:Tuple X r): ((realm hl u T).uses x).width z ≤ ((realm hl u S).uses x).width z:=highest hl u T x z _ (Premium.width_unit ..) fun i=>le_trans (amount_mono hl u (infDist_le_infDist_of_subset h hs)) (((realm hl u S).uses x).width_ge z i)
lemma finer {u:ℕ}(hl:0<l)(hv:l≤d)(S:Set Room)(x:X→Room)(z:Tuple X r): ((realm (hl.trans_le hv) u S).uses x).width z≤((realm hl u S).uses x).width z := highest _ u S x z _ (Premium.width_unit ..) fun i=> le_trans (b:=amount l u (infDist (x (z i)) S)) (by unfold amount; gcongr;exact infDist_nonneg) (((realm hl u S).uses x).width_ge z i)
lemma joins (hl:0<l)(u:ℕ)(S:Set Room)(x:X→Room)(p:Tuple X r)(q:Tuple X s) : ((realm hl u S).uses x).width (Fin.append p q) ≤ ((realm hl u S).uses x).width p * ((realm hl u S).uses x).width q:= by
 let F:=(realm hl u S).uses x
 change F.width _ ≤ _
 refine highest _ u S x _ _ (one_le_mul (Premium.width_unit ..) (Premium.width_unit ..)) (fun i=>?_)
 induction i using Fin.addCases <;> rename_i i
 · rw [Fin.append_left]; exact (mul_one _).ge.trans (mul_le_mul' (F.width_ge p i) (F.width_unit q))
 rw [Fin.append_right]; exact (one_mul _).ge.trans (mul_le_mul' (F.width_unit p) (F.width_ge q i))
lemma packet_pair (hl:0<l)(u:ℕ)(S:Set Room)(x:X→Room)(T:Packet X r)(U:Packet X s): let F:= (realm hl u S).uses x; markQ F (joined T U) ≤ markQ F T*markQ F U:=by
 intro F; apply mark_symmetry.trans
 unfold markQ quota;rw [← (Fin.appendEquiv ..).tsum_eq]; rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro p; rw [← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro q
 change ‖untied T U (Fin.append p q)‖ₑ * _ ≤ _; rw [untied,cutleft,cutright, enorm_mul]; exact (mul_le_mul_right (joins ..) _).trans_eq (mul_mul_mul_comm ..)
lemma amount_pow (hl:0<l)(u:ℕ)(S:Set Room)(x:X→Room)(z:Tuple X r) : ((realm hl u S).uses x).width z=((realm hl 1 S).uses x).width z^u:= (Premium.width_pow u _ _ _ _ (fun _ _=>pow_amount ..) (fun _=>pow_amount ..) _).symm
lemma amount_plus (hl:0<l)(u b:ℕ)(S:Set Room)(x:X→Room)(z:Tuple X r): ((realm hl (u+b) S).uses x).width z=((realm hl u S).uses x).width z*((realm hl b S).uses x).width z:=by rw [amount_pow hl (u+b),amount_pow hl u,amount_pow hl b,pow_add]
lemma final_price (hl:0<l)(hv:l≤1)(u:ℕ)(S:Set Room)(w:Room)(hS:S.Nonempty)(hh:IsClosed S)(hd: ∀ y∈S,dist y w≤d)(hx:0≤d)(x:X→Room)(z:Tuple X r): ((Premium.rooted (native 1 (by norm_num) u) w).uses x).width z ≤ ((realm hl (u+u) S).uses x).width z*(amount 1 (u+u) d):=by
 let Q:=native 1 (by norm_num) u; let F:= ((Premium.rooted Q w).uses x); let E:= ((realm hl u S).uses x)
 have ht(i:Fin r) : Q.road w (x (z i))≤ E.width z *amount 1 u d := by
   let a:=x (z i); obtain ⟨y,hy,he⟩:= exists_mem_closure_infDist_eq_dist hS a; rw [hh.closure_eq] at hy
   apply (Q.tri w y a).trans; rw [mul_comm, Q.symm y a]
   apply mul_le_mul' _ (amount_mono (by norm_num) u (by rw [dist_comm];exact hd y hy))
   change amount 1 u (dist a y) ≤ _
   rw [← he]; exact (amount_monoL hl hv u infDist_nonneg).trans (E.width_ge z i)
 rw [amount_plus,amount_add, mul_mul_mul_comm]; apply Premium.width_le
 · apply Tariff.diameter_le _ (one_le_mul (one_le_mul (E.width_unit _) (amount_unit (by norm_num) u hx)) (one_le_mul (E.width_unit _) (amount_unit (by norm_num) u hx)))
   intro i j; apply (Q.tri (x (z i)) w (x (z j))).trans; nth_rw 1 [Q.symm]; exact mul_le_mul' (ht i) (ht j)
 intro i; apply (ht i).trans; exact (mul_one _).ge.trans (mul_le_mul_right (one_le_mul (E.width_unit _) (amount_unit (by norm_num) u hx)) _)
where
 amount_monoL {l d t:ℝ}(h:0<l)(hh:l≤t)(u:ℕ)(hd:0≤d): amount t u d≤amount l u d:=by unfold amount; gcongr

lemma divided (x:Room)(S T:Set Room)(hS:S.Nonempty)(hT:T.Nonempty)(hx:IsClosed S)(hy:IsClosed T)(he:∀ s∈S,∀ t∈T,d≤dist s t): d ≤ infDist x S + infDist x T:=by
 obtain ⟨p,hp,ht⟩:= exists_mem_closure_infDist_eq_dist hS x; obtain ⟨q,hq,h⟩:=exists_mem_closure_infDist_eq_dist hT x
 rw [hx.closure_eq] at hp; rw [hy.closure_eq] at hq; rw [ht,h, dist_comm x p]; exact (he p hp q hq).trans (dist_triangle ..)
end Collapsed
end YM.RegulatorIR.Cluster
