import YM.Pert.Flow.Costs
/-! An entrywise price interface on a normalized matrix product. No field approximation hypothesis hidden inside `tame`: to use `Law` one needs the step estimates uniformly at all sufficiently late log lengths, including offgrade costs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace YM.Pert.Flow.Layer
open Function Filter Topology Price Set Finset
open scoped Topology Classical
variable {V : Type*} [Fintype V] {e : V → ℝ} {Z T : ℕ→ V→ V→ ℝ}

def whole (Z : ℕ→V→V→ℝ) (j:V) (n:ℕ) := ∑i:V, |Z n i j|
def gapSupport (e : V→ℝ) (j : V) := univ.filter (fun i:V=>e i < e j)
def portion (e : V→ℝ) (Z : ℕ→V→V→ℝ) (j:V) (n:ℕ) := ∑i∈gapSupport e j, |Z n i j|
@[simp] lemma gapMem (e:V→ℝ) (j i:V) : i∈gapSupport e j ↔ e i < e j := by simp [gapSupport,mem_filter,Finset.mem_univ,true_and]
def correction (e : V→ℝ) (T:ℕ→V→V→ℝ) (n j i k) := (T n i k - if i=k then e k else 0)/ e j

/-- `Z_n` models engineer-divided inverse frame columns on a common horizon:
`H⁻¹` maps fixed fields to UV label coefficients. Forward trajectory
comparison for `Z`. In the cost conventions it has column normalization `exp(-n d)` if `e=exp d`.
-/
structure Law (e : V→ℝ) (Z T : ℕ→V→V→ℝ) : Prop where
   positive i : 0 < e i
   filtered n i j : e j < e i → Z n i j = 0
   evolve n i j : Z (n+1) i j = (∑k, T n i k * Z n k j)/(e j)
   diagonal (j) : ∃ K : ℝ, K ≥ 0 ∧ ∀ᶠ n in atTop, ∀ k, e k ≤ e j →
             (∑ i:V, |correction e T n j i k|) ≤ K/(duration n)
   lower (j) : ∀ q:ℕ, ∃ B : ℝ, B ≥ 0 ∧ ∀ᶠ n in atTop, ∀ k, e k = e j →
             (∑ i ∈ gapSupport e j, |correction e T n j i k|) ≤ B/(duration n)^q

lemma sum_delta (f:V→ℝ) (i) : ∑ k:V, (if i=k then e k else 0)*f k=e i*f i := by simp
variable (h:Law e Z T)
include h

lemma updateLaw n j i : Z (n+1) i j= (e i/e j)*Z n i j + ∑ k:V, correction e T n j i k*Z n k j := by
   have hx (k : V) : T n i k*Z n k j=(if i=k then e k else 0)*Z n k j + (T n i k-(if i=k then e k else 0))*Z n k j:=by ring
   have hp:= h.positive j
   rw [h.evolve]; simp_rw [hx,Finset.sum_add_distrib,sum_delta]
   simp only [add_div,div_mul_eq_mul_div,correction,←sum_div]

lemma roughRead {s:Finset V} (n j) : (∑ i∈s, |Z (n+1) i j|)
  ≤ (∑ i∈s, (e i/e j) * |Z n i j|)+ ∑ k:V, (∑ i∈s, |correction e T n j i k|) * |Z n k j| := by
   let f i k:= correction e T n j i k*Z n k j
   calc
       _ ≤ ∑i∈s, (((e i/e j)* |Z n i j|) + ∑ k:V,|f i k|) := sum_le_sum (fun i hi=> by
            rw [updateLaw h ..]
            calc
               _ ≤ _ + _:=abs_add_le _ _
               _ ≤ |e i/e j * Z n i j| + ∑ k:V,|f i k| := add_le_add_right (Finset.abs_sum_le_sum_abs ..) _
               _ = _:= by rw [abs_mul, abs_of_nonneg (div_nonneg (h.positive _).le (h.positive _).le)])
       _ = _:= by dsimp only [f]; simp only [sum_add_distrib,abs_mul,sum_mul]; rw [Finset.sum_comm (s:=s)]

theorem all_tame (j) : tame (whole Z j) := by
   have he i : 0 ≤ whole Z j i := by unfold whole; exact Finset.sum_nonneg (by intros; positivity)
   obtain ⟨K,hK,h'⟩:= h.diagonal j
   apply rate_barrier he hK (h'.mono fun n hn=> ?_)
   have hd i : e i/e j* |Z n i j| ≤ |Z n i j| := by
       by_cases ht : e i ≤ e j
       · refine (mul_le_mul_of_nonneg_right ((div_le_one (h.positive _)).mpr ht) (abs_nonneg _)).trans (le_of_eq (one_mul _))
       rw [h.filtered _ _ _ (lt_of_not_ge ht),abs_zero,mul_zero]
   have hh k : (∑ i:V,|correction e T n j i k|) * |Z n k j| ≤ K/(duration n)* |Z n k j| := by
       by_cases ht : e k ≤ e j
       · exact mul_le_mul_of_nonneg_right (hn k ht) (abs_nonneg _)
       rw [h.filtered _ _ _ (lt_of_not_ge ht),abs_zero,mul_zero,mul_zero]
   have hy:= roughRead h n j (s:=Finset.univ)
   refine hy.trans ((add_le_add (Finset.sum_le_sum (fun i _=>hd i)) (Finset.sum_le_sum (fun i _=>hh i))).trans_eq ?_)
   rw [←mul_sum]
   dsimp [whole]; ring

lemma tame_column (j i) : tame (fun n=>Z n i j) := tamer (all_tame h j) (fun n=> by
   rw [abs_of_nonneg (show 0≤whole Z j n from Finset.sum_nonneg (fun _ _=>by positivity))]
   exact Finset.single_le_sum (s:=Finset.univ) (fun k _=>abs_nonneg (Z n k j)) (Finset.mem_univ i))

omit h in
private lemma portion_le (g : V→ℝ) (d:V→ℝ) j : ∑ i∈gapSupport d j, |g i| ≤ ∑ i:V, |g i| :=
   Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=>by positivity)

private lemma gap_theta (j : V) : ∀ S:Finset V, ∃ r:ℝ,(0 ≤ r ∧ r < 1) ∧ ∀ i∈S, e i < e j → e i/e j ≤ r := by
    intro S
    induction S using Finset.induction_on with
    | empty=> exact ⟨0,⟨le_rfl,zero_lt_one⟩,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
    | insert i u h' IH=>
       obtain ⟨r,hr,hR⟩:=IH
       by_cases hi : e i < e j
       · refine ⟨max r (e i/e j),⟨hr.1.trans (le_max_left ..), max_lt_iff.mpr ⟨hr.2,(div_lt_one (h.positive _)).mpr hi⟩⟩,fun w hw hm=> ?_⟩
         rcases mem_insert.mp hw with rfl|hw
         · exact le_max_right ..
         exact (hR w hw hm).trans (le_max_left ..)
       refine ⟨r,hr,fun w hw hm=> ?_⟩
       rcases mem_insert.mp hw with rfl|hw
       · exact False.elim (hi hm)
       exact hR w hw hm

lemma gap_read {j : V} (r : ℝ) (hr : ∀ i, e i < e j → e i/e j ≤ r) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {n : ℕ}
    (hp : ∀ k, e k ≤ e j → (∑ i:V, |correction e T n j i k|) ≤ u)
    (hP : ∀ k, e k=e j → (∑ i∈gapSupport e j, |correction e T n j i k|) ≤ v) :
       portion e Z j (n+1) ≤ (r+u)*portion e Z j n + v*whole Z j n := by
   let s:=gapSupport e j
   have hl : (∑ i∈ s, e i/e j * |Z n i j|) ≤ r * portion e Z j n := by
       change _ ≤ r*∑i∈s,_
       rw [mul_sum]
       exact sum_le_sum fun i hi=> mul_le_mul_of_nonneg_right (hr i ((gapMem _ _ _).mp hi)) (abs_nonneg _)
   have ht (k:V) : (∑ i∈s,|correction e T n j i k|)* |Z n k j| ≤
       (if k∈s then u* |Z n k j| else 0) + v* |Z n k j| := by
       by_cases hk : k∈s
       · rw [if_pos hk]
         apply (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)).trans (le_add_of_nonneg_right (mul_nonneg hv (abs_nonneg _)))
         exact (portion_le (fun i=>correction e T n j i k) e j).trans (hp k ((gapMem _ _ _).mp hk).le)
       rw [if_neg hk,zero_add]
       have he := not_lt.mp (fun hx=> hk ((gapMem _ _ _).2 hx))
       rcases lt_or_eq_of_le he with hc|hc
       · rw [h.filtered _ _ _ hc,abs_zero,mul_zero,mul_zero]
       exact mul_le_mul_of_nonneg_right (hP k hc.symm) (abs_nonneg _)
   have hyp:= Finset.sum_le_sum (s:=Finset.univ) (fun k _=>ht k)
   rw [sum_add_distrib,←sum_filter] at hyp
   have he : filter (·∈s) univ = s := by simp
   simp only [he,←mul_sum] at hyp
   refine (roughRead h n j (s:=s)).trans ((add_le_add hl hyp).trans_eq ?_)
   change r*portion e Z j n + (u* portion e Z j n + v*whole Z j n) = _
   ring

theorem gap_decay {i j} (hi : e i < e j) : flat (fun n=>Z n i j) := by
   obtain ⟨r,hr,H⟩:=gap_theta h j univ
   let p:=portion e Z j; let S:=whole Z j
   let c:=r + (1-r)/2
   have hc: r < c := by dsimp only [c];linarith [hr.1,hr.2]
   have hc': c < 1 := by dsimp only [c];linarith [hr.2]
   have hp (n): 0 ≤ p n:= Finset.sum_nonneg fun i _=>abs_nonneg _
   have hs (n): 0 ≤ S n:= Finset.sum_nonneg fun i _=>abs_nonneg _
   obtain ⟨k,A,hA,ha⟩:=all_tame h j
   obtain ⟨K,hK,hL⟩:=h.diagonal j
   have hB:= duration_leads.const_div_atTop K
   have hQ (q:ℕ) : ∃ D:ℝ,0≤D ∧ ∀ᶠ n in atTop, |p (n+1)| ≤ c * |p n| + D/(duration n)^q := by
       obtain ⟨D,hD,hh⟩:=h.lower j (q+k)
       refine ⟨D*A,mul_nonneg hD hA,?_⟩
       filter_upwards [hL,hB.eventually (gt_mem_nhds (sub_pos.mpr hc)),hh] with n hn hi he
       rw [abs_of_nonneg (hp _),abs_of_nonneg (hp _)]
       have hg:= duration_large n
       refine (gap_read h r (fun k=> H k (mem_univ _)) (by positivity) (by positivity) hn he).trans ?_
       apply add_le_add
       · exact mul_le_mul_of_nonneg_right (by linarith only [hi]) (hp _)
       change D/(duration n)^(q+k)*S n ≤ (D*A)/(duration n)^q
       have hL:= ha n
       change |S n| ≤ _ at hL
       rw [abs_of_nonneg (hs _) ] at hL
       calc
           _ ≤ D/duration n^(q+k)*(A*duration n^k) := mul_le_mul_of_nonneg_left hL (by positivity)
           _ = _ := by rw [pow_add];field_simp
   exact flatter (barrier_decay (hr.1.trans hc.le) hc' hQ) (fun n=> (single_le_sum (s:=gapSupport e j) (fun k _=>abs_nonneg (Z n k j)) ((gapMem e j i).mpr hi)).trans (le_abs_self _))
end YM.Pert.Flow.Layer
