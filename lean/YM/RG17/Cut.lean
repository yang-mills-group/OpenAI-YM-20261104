import YM.RG17.Price

/-!
Numerical finite-order stagger. Take enough terms before
matrix manipulations; inversion only after basis bounds in
ACTUAL correlations. Mismatch in discarded slots pays Λ power.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Filter Set OPE Extraction
open SharpGram.Allow
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Spec.Final C f S}
    {L:Layout F} (Z:Ledger L) {I : Type*} {K:Scope I}
    {E E':Type*} [NormedAddCommGroup E][NormedSpace ℂ E] [NormedAddCommGroup E'][NormedSpace ℂ E']
abbrev wt (e:ℕ)(r:ℝ):ℂ:=(Z.g r ^ e:ℝ)
lemma wtCharge (e:ℕ) : Bare Z e (wt Z e):=Cost.insert_single 1 0 zero_le_one <| Eventually.of_forall fun r=>by
    rw [one_mul,pow_zero,mul_one,wt,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (Z.positive r).le _)]
variable {T:Type*}[NormedAddCommGroup T][NormedSpace ℂ T]

def accrue (p:ℕ)(v:ℕ→ℝ→T) (r:ℝ):T := ∑ j∈Finset.range (p+1), wt Z j r • v j r
def forecast (p:ℕ)(v:ℕ→ℝ→I→T) (r:ℝ)(x:I):T:= accrue Z p (fun j r=> v j r x) r
variable (b:ℕ→ℝ→ E →L[ℂ] E') (v:ℕ→ℝ→I→E) (j k:ℕ)

def combine (i:ℕ) (r:ℝ)(x:I):E':= ∑ j ∈ Finset.range (i+1), b j r (v (i-j) r x)

namespace Cost
variable {Z v b}
lemma stipend (h:Cost Z K k (v j)) (p:ℕ) : Cost Z K (p+k) (fun r x=> wt Z p r • v j r x):=
    bareProduct (wtCharge Z p) h (Eventually.of_forall fun r _=> norm_smul_le ..)
lemma point {y:ℝ→I→T} (h:Cost Z K 0 y) (p:ℕ) : Cost Z K p (fun r x=> wt Z p r • y r x) :=by
    simpa only [add_zero] using bareProduct (wtCharge Z p) h (z:= fun r x=> wt Z p r • y r x) (Eventually.of_forall fun r _=> norm_smul_le ..)
lemma castCap {y:ℕ→ℝ→I→T} {p:ℕ}(h:∀ j≤p, Cost Z K 0 (y j)) : Cost Z K 0 (forecast Z p y):=
    Cost.sum (H:= Finset.range (p+1)) (fun i hi=> ((h i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).point i).lesser (Nat.zero_le _))

lemma truncSplit {p q:ℕ}(hq:p ≤ q){v:ℕ→ℝ→I→E}
    (hx:∀ i:ℕ,p < i → i ≤ q → Cost Z K 0 (v i)): Cost Z K (p+1) (fun r x=>forecast Z q v r x-forecast Z p v r x):=by
   induction q,hq using Nat.le_induction with
   | base=> simp only [sub_self]; exact Cost.zero Z K (p+1) _
   | succ k hk ih=>
     apply ((ih (fun i hi h=>hx i hi (le_trans h (Nat.le_succ k)))).add (((hx _ (by omega) (Nat.le_refl _)).point (k+1)).lesser (Nat.succ_le_succ hk))).congr
     exact Eventually.of_forall (fun r x=>by unfold forecast accrue; rw [Finset.sum_range_succ _ (k+1)]; abel)

-- k equals or exceeds requested+1 available. The inherited local errors
-- at cost k here still open, not inferred from expensive basis change.
lemma openTerm {v:ℕ→ℝ→I→E}{y:ℝ→I→E} {p q:ℕ}(hq:p<q)
    (hx:∀ i:ℕ,p < i → i ≤ q → Cost Z K 0 (v i))
    (h:Cost Z K q (fun r x=>y r x-forecast Z q v r x)) : Cost Z K (p+1) (fun r x=>y r x-forecast Z p v r x):=by
   refine ((h.lesser (Nat.succ_le.mpr hq)).add (truncSplit (Nat.le_of_lt hq) hx)).congr (Eventually.of_forall fun r x=> ?_)
   abel
lemma combined {p:ℕ} (h:∀ i≤p, Bare Z 0 (b i))(hx:∀ i≤p, Cost Z K 0 (v i)): Cost Z K 0 (combine b v p):=by
   apply Cost.sum (H:=Finset.range (p+1)); intro i hi
   exact Cost.op (h _ (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (hx _ (Nat.sub_le ..))
end Cost

private lemma triangle {T:Type*}[AddCommGroup T](p:ℕ)(f:ℕ→ℕ→T) :
    ∑ i ∈ Finset.range (p+1), ∑ j∈ Finset.range (p+1), f i j
      = ∑ k ∈ Finset.range (p+1), ∑ i∈ Finset.range (k+1), f i (k-i) +
        ∑ i ∈ Finset.range (p+1), ∑ j∈ (Finset.range (p+1)).filter (fun j=>p < i+j), f i j:=by
    let s:=Finset.range (p+1)
    have he (i): (∑ j ∈ s, f i j)= ∑ j∈ s.filter (fun j=>¬p < i+j),f i j + ∑ j∈ s.filter (fun j=>p < i+j), f i j:=by
       rw [add_comm, Finset.sum_filter_add_sum_filter_not ..]
    simp_rw [← show s=Finset.range (p+1) from rfl,he,Finset.sum_add_distrib]; congr 1
    symm
    calc
      _ = ∑ k∈ s, ∑ i∈ s.filter (fun j=>j≤k), f i (k-i):= Finset.sum_congr rfl (fun k hk=>by congr 1; ext j; have hz:=Finset.mem_range.mp hk; simp [s]; omega)
      _ = ∑ i∈ s, ∑ k∈ s.filter (fun j=>i≤j), f i (k-i):=by simp_rw [Finset.sum_filter]; rw [Finset.sum_comm]
      _ = _ := Finset.sum_congr rfl fun i hi=>by
         refine Finset.sum_nbij' (fun k=> k-i) (fun j=>i+j) ?_ ?_ ?_ ?_ ?_
         · rintro k h; simp [s] at *; omega
         · rintro k h; simp [s] at *; omega
         · rintro k h; simp [s] at *; omega
         · rintro k h; simp [s] at *
         rintro k h; rfl

variable {Z v b}
lemma Cost.convolve {p:ℕ}(hx:∀ i≤p, Cost Z K 0 (v i)) (hb:∀ i≤p, Bare Z 0 (b i)) :
    Cost Z K (p+1) (fun r x=> accrue Z p b r (forecast Z p v r x) - forecast Z p (combine b v) r x):=by
    let A i j r x:=wt Z (i+j) r • b i r (v j r x)
    let S:=Finset.range (p+1)
    have h (i j) (hi:i∈S)(hj:j∈S)(hk:p < i+j) : Cost Z K (p+1) (A i j):=by
        have he:=Cost.op (hb i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (hx j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
        exact (he.point (i+j)).lesser (Nat.succ_le.mpr hk)
    apply (Cost.sum (H:=S) (fun i hi=> Cost.sum (H:=S.filter (fun j=>p < i+j)) (fun j hj=>h i j hi (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2))).congr
    apply Eventually.of_forall; intro r x
    have hp: accrue Z p b r (forecast Z p v r x) = ∑ i∈ S,∑ j∈ S,A i j r x:=by
        unfold accrue forecast; rw [ContinuousLinearMap.sum_apply]
        apply Finset.sum_congr rfl; intro i _
        rw [ContinuousLinearMap.smul_apply]; unfold accrue; rw [map_sum, Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _
        rw [map_smul,smul_smul]; congr 1; simp [wt,pow_add] -- congr knows A?
    have he: forecast Z p (combine b v) r x = ∑ k∈ S, ∑ i∈ Finset.range (k+1), A i (k-i) r x:= by
       unfold forecast accrue; refine Finset.sum_congr rfl fun k _=>?_
       unfold combine; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; unfold A; rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    rw [hp,he]; change _= (∑ i∈ S, ∑ j∈ S,A i j r x) - _
    rw [triangle p (fun i j=> A i j r x)]
    unfold S; abel

lemma Cost.payAt {p:ℕ} {M:ℝ→E→L[ℂ] E'}{y:ℝ→I→E}
    (hx:∀ i≤p, Cost Z K 0 (v i)) (hb:∀ i≤p, Bare Z 0 (b i))
    (hy:Cost Z K (p+1) (fun r x=> y r x - forecast Z p v r x)) (h:Bare Z (p+1) (fun r=> M r-accrue Z p b r)) :
    Cost Z K (p+1) (fun r x=> M r (y r x) - forecast Z p (combine b v) r x):=by
    have hB:Bare Z 0 (accrue Z p b):= Cost.castCap (y:=fun i r _=>b i r) hb
    have hw:Bare Z 0 M:=(Cost.add (h.lesser (Nat.zero_le _)) hB).congr (Eventually.of_forall fun r _=> sub_add_cancel ..)
    have he:=Cost.op hw hy; rw [zero_add] at he
    have hv:=Cost.op h (Cost.castCap hx); rw [add_zero] at hv
    refine ((he.add hv).add (Cost.convolve hx hb)).congr (Eventually.of_forall fun r x=> ?_)
    rw [map_sub,ContinuousLinearMap.sub_apply]; abel
end YM.RG17

