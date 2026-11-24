import YM.FormalOPE.RG10.Wing.Distance
/-!
 # Use familiar elementary Ward statements of bulk MST perturbative charts
 at this step. Mixed-velocity identities through finite order. Domain pure.Unchanged.Links.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Quest
open Function PowerSeries Finset Route Facets HStein Submarine
open scoped Topology BigOperators Classical
variable {X I B J : Type} [Fintype I]
variable (v:I→Channel B)(u:B→Channel B)
variable (A:Finset X)(c:X→Channel B)(D:X→ I→Channel I)

def ship : Channel I →+ Channel B where
 toFun p:= ∑ x∈A,c x * replot v (kick (D x) p)
 map_add' p q:= by simp_rw [map_add,mul_add, Finset.sum_add_distrib]
 map_zero':= by simp
lemma opens (P:Channel I): ship v A c D P= ∑ x∈A,c x* replot v (kick (D x) P):= rfl
local notation "W"=>Channel B
local notation "T"=> replot v
local notation "L"=> kick u
local notation "K"=> ship v A c D
variable (P Q:Channel I)
lemma deriv_ship : ship v A c D (P*Q)= replot v P * ship v A c D Q+ replot v Q * ship v A c D P:= by
 simp_rw [opens,mul_sum,← sum_add_distrib]; apply sum_congr rfl; intro x _; rw [Derivation.leibniz]; simp only [map_add,smul_eq_mul,map_mul]; ring
lemma ship_one (x:ℂ): ship v A c D (algebraMap ℂ _ x)=0:= by simp_rw [opens, Derivation.map_algebraMap]; simp
lemma ship_X (t:ℕ): ship v A c D (PowerSeries.X^t)=0:= by rw [opens]; apply sum_eq_zero; intro x _; rw [Derivation.leibniz_pow,X_charged]; simp
variable {Q} {k:ℕ}
lemma ship_through (h:Through k P Q) : Through k (ship v A c D P) (ship v A c D Q) := by intro i hi; simp_rw [opens,map_sum]; exact sum_congr rfl (fun x _=> Through.mul (Through.refl (c x)) (through v (skew (D x) h)) i hi)
-- choose chart `v` mapping fine into mixed by `mark`; Ward.
variable [Fintype B]
variable (ht: ∀ i:I,Through k (kick u (v i)) (∑ x∈A,c x* replot v (D x i)))
include ht
lemma crew : Through k (kick u (replot v P)) (ship v A c D P):= by
 let H (p:Channel I):= Through k (L (T p)) (K p)
 have ha (p q:Channel I)(hp:H p)(hq:H q): H (p+q):= by unfold H; rw [map_add,map_add,map_add]; exact hp.add hq
 have he (p q:Channel I)(hp:H p)(hq:H q): H (p*q):= by unfold H; rw [map_mul, Derivation.leibniz,deriv_ship]; simp_rw [smul_eq_mul]; exact Through.add (Through.mul (Through.refl _) hq) (Through.mul (Through.refl _) hp)
 have hh (p:Packet I): H (C p):= by
    induction p using MvPolynomial.induction_on with
    | C c'=> unfold H; rw [grain,rules,Derivation.map_algebraMap,ship_one]; exact Through.refl _
    | add a b ha' hb=> rw [map_add]; exact ha _ _ ha' hb
    | mul_X a i ih=> rw [map_mul]; apply he _ _ ih; change Through k (L (T (sprout i))) (K (sprout i)); simp_rw [hangs,opens,sprouting]; exact ht i
 have hf (S:Finset ℕ): H (∑ i∈S, monomial i (coeff i P)):= by
    induction S using Finset.induction_on with
    | empty=> unfold H; rw [sum_empty, map_zero,map_zero,map_zero]; exact Through.refl _
    | insert i S hu ih=> rw [sum_insert hu]; refine ha _ _ ?_ ih; rw [radical]; refine he _ _ ?_ (hh _); unfold H; rw [jag,ship_X,Derivation.leibniz_pow,X_charged]; simp only [smul_zero]; exact Through.refl _
 exact ((skew u (through v (paper P k))).trans (hf (range (k+1)))).trans (ship_through v A c D P (paper P k)).symm

lemma elemental (hz : ∀ x∈A, Through k (kick (D x) P) 0): Through k (kick u (replot v P)) 0 := by
 apply (crew v u A c D P ht).trans; intro i hi; rw [opens,map_sum,map_zero]; apply sum_eq_zero;intro x hx; simpa only [map_zero,mul_zero] using Through.mul (Through.refl (c x)) (through v (hz x hx)) i hi
end YM.FormalOPE.RG10.Wing.Quest
