import YM.Pert.Flow.Layers
/-! One-step perturbation estimates, including inverse orientation. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Pert.Flow.Layer
open Function Filter Topology Price Finset
open scoped Topology Classical
variable {V : Type*} [Fintype V]
abbrev TimeArray (V : Type*) := ℕ → V → V → ℝ
abbrev Revenue (V : Type*) := ℕ → ℝ → V → V → ℝ

def residual (e : V → ℝ) (T : TimeArray V) (t i k) := T t i k - if i=k then e k else 0
structure StepEstimate (e : V → ℝ) (T : TimeArray V) : Prop where
    pos i : 0 < e i
    close : ∃ K:ℝ, 0 ≤ K ∧ ∀ᶠ n:ℕ in atTop,∀ i k:V,|residual e T n i k| ≤ K/(duration n)
    higher (q : ℕ) : ∀ i k, e i < e k →
        ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop, |T n i k| ≤ D/(duration n)^q

private lemma maximumPick (P : V→V→ℝ→Prop) (h : ∀ i k a b, a ≤ b → P i k a → P i k b) (H : ∀ i k, ∃ a:ℝ, P i k a) :
   ∃ A:ℝ, 0 ≤ A ∧ ∀ i k, P i k A := by
   choose a ha using H
   let A:=∑ i:V,∑ k:V, |a i k|
   have hz i : 0 ≤ ∑ k:V, |a i k|:= sum_nonneg fun k _=> abs_nonneg _
   have ht i k : |a i k| ≤ A := (single_le_sum (s:=univ) (fun k _=>abs_nonneg (a i k)) (mem_univ _)).trans (single_le_sum (fun i _=>hz i) (mem_univ _))
   exact ⟨A,sum_nonneg (fun i _=>hz i),fun i k=>h i k _ _ ((le_abs_self _).trans (ht i k)) (ha i k)⟩

variable {e : V → ℝ} {T : TimeArray V} (h : StepEstimate e T)
include h
lemma higherTogether (q:ℕ) : ∃ D:ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop, ∀ i k, e i < e k → |T n i k| ≤ D/(duration n)^q := by
   suffices H : ∀ i k:V, ∃ D:ℝ, ∀ᶠ n in atTop,e i < e k → |T n i k| ≤ D/(duration n)^q by
       let P i k (D:ℝ) := ∀ᶠ n in atTop,e i < e k → |T n i k| ≤ D / (duration n)^q
       obtain ⟨D,hD,hr⟩:= maximumPick P (fun i k a b h ha=> ha.mono (fun n hn he=>(hn he).trans (div_le_div_of_nonneg_right h ((one_le_pow₀ (duration_large _) : (1:ℝ) ≤ duration n^q).trans' zero_le_one)))) H
       refine ⟨D,hD,(eventually_all.mpr fun i=>eventually_all.mpr fun k=>hr i k)⟩
   intro i k; by_cases he : e i < e k
   · obtain ⟨D,hD,hr⟩:= h.higher q i k he; exact ⟨D, hr.mono (fun _ h _ =>h)⟩
   exact ⟨0,Eventually.of_forall (fun _ h=> False.elim (he h))⟩

private lemma energyLower : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ e i := by
   suffices hf : ∀ s:Finset V, ∃ m : ℝ, 0 < m ∧ ∀ i∈s, m ≤ e i by
       obtain ⟨m,hm,H⟩:=hf univ; exact ⟨m,hm,fun i=>H i (mem_univ _)⟩
   intro s; induction s using Finset.induction_on with
   | empty => exact ⟨1,zero_lt_one,fun i hi=>False.elim (notMem_empty _ hi)⟩
   | insert i s hi IH =>
      obtain ⟨m,hm,hM⟩:=IH
      exact ⟨min m (e i),lt_min hm (h.pos _),fun k hk=> (mem_insert.mp hk).elim (by rintro rfl; exact min_le_right ..) fun hk=>(min_le_left ..).trans (hM k hk)⟩

def eye (i k : V) : ℝ := if i=k then 1 else 0
def stepProduct (T U:TimeArray V) : TimeArray V := fun n i k=> ∑ j, T n i j * U n j k

omit h in
lemma stepAssoc (A T U:TimeArray V) : stepProduct A (stepProduct T U) = stepProduct (stepProduct A T) U := funext fun n=> funext fun i => funext fun k=> by
    dsimp only [stepProduct]; simp only [Finset.sum_mul,Finset.mul_sum,mul_assoc]; rw [Finset.sum_comm]

omit h in
lemma leftUnit (T : TimeArray V) : stepProduct (fun _ i k=>eye i k) T = T := funext fun n=>funext fun i=>funext fun k=>by simp [stepProduct,eye]
omit h in
lemma rightUnit (T : TimeArray V) : stepProduct T (fun _ i k=>eye i k) = T := funext fun n=>funext fun i=>funext fun k=>by simp [stepProduct,eye]

variable {U : TimeArray V} (hU : stepProduct T U = (fun _ i k=>eye i k))
include hU
omit h in
private lemma inverse_identity (n j i) : e i*U n i j + ∑ k, residual e T n i k * U n k j = eye i j := by
   have hu:=congrFun (congrFun (congrFun hU n) i) j
   unfold stepProduct at hu
   rw [←hu]; simp only [residual,sub_mul,Finset.sum_sub_distrib]
   rw [sum_delta]; ring
private lemma inverse_prebound (n j) {K} (H : ∀ i k, |residual e T n i k| ≤ K/(duration n)) :
   (∑ i, e i * |U n i j|) ≤ 1 + (Fintype.card V : ℝ)*K / duration n * whole U j n := by
   have hy i : e i * |U n i j|= |e i * U n i j|:= (by rw [abs_mul,abs_of_nonneg (h.pos i).le])
   have hf i : |(∑ k, residual e T n i k * U n k j)| ≤ K / duration n * whole U j n :=
       (abs_sum_le_sum_abs _ _).trans (by
            simp only [whole,mul_sum]
            exact sum_le_sum (fun k _=> by rw [abs_mul];exact mul_le_mul_of_nonneg_right (H i k) (abs_nonneg _)))
   have he i : e i* |U n i j| = |eye i j-∑ k, residual e T n i k * U n k j| :=
       (hy i).trans (congr_arg abs (eq_sub_of_add_eq (inverse_identity hU ..)))
   simp_rw [he]
   have ht:= sum_le_sum (s:=univ) (fun i _=> (abs_sub _ _).trans (add_le_add_right (hf i) (|eye i j|)))
   exact ht.trans (le_of_eq (by rw [sum_add_distrib];simp [eye,apply_ite abs];ring))

private lemma inverse_global (n) {m K} (hm : 0 < m) (hM : ∀ i, m ≤ e i) (hk : 0 ≤ K) (hm' : (Fintype.card V:ℝ)*K / duration n ≤ m/2)
  (H : ∀ i k, |residual e T n i k| ≤ K/duration n) :
  ∀ j:V, whole U j n ≤ 2/m := by
   intro j
   have hL:= inverse_prebound h hU n j H
   have hf : m * whole U j n ≤ ∑ i, e i* |U n i j| := by
      rw [whole,Finset.mul_sum];exact sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (hM i) (abs_nonneg _))
   have hz : 0 ≤ whole U j n := sum_nonneg fun i _=>abs_nonneg _
   rw [le_div_iff₀ hm]
   linarith only [hf,hL,mul_le_mul_of_nonneg_right hm' hz]

private lemma inverse_error (n j i) {C B : ℝ} (H : ∀ i k, |residual e T n i k| ≤ C) (hC :0≤C)
   (h' : whole U j n ≤ B) : |e i*U n i j-eye i j| ≤ C*B := by
   rw [eq_sub_of_add_eq (inverse_identity hU ..),sub_sub_cancel_left,abs_neg]
   -- no sub_sub_cancel_left with correct expression? test
   refine (abs_sum_le_sum_abs _ _).trans ((le_trans ?_ (mul_le_mul_of_nonneg_left h' hC)))
   rw [whole,mul_sum]
   exact sum_le_sum (fun k _=> by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (H i k) (abs_nonneg _))
private lemma inverse_partial (n j) {B A K}
    (hm : ∀ i k, e i < e k → |T n i k| ≤ B)
    (H : ∀ i k, |residual e T n i k| ≤ K) (hA : whole U j n ≤ A)
    (hB : 0 ≤ B) (hK:0≤K) :
   ∑ i∈gapSupport e j, e i * |U n i j| ≤
   (Fintype.card V:ℝ)*(K*portion e U j n+B*A) := by
   let s:=gapSupport e j
   have ha (i : V) (hk : i∈s) : e i* |U n i j| ≤ K*portion e U j n+B*A := by
       have hi : e i < e j := (gapMem _ _ _).1 hk
       have hh : e i * U n i j = -∑ k, residual e T n i k * U n k j:= by
          have hh := inverse_identity hU (e:=e) n j i
          have he : i ≠ j := fun he => hi.ne (congr_arg e he)
          rw [eye,if_neg he] at hh
          simpa using eq_sub_of_add_eq hh
       rw [← abs_of_nonneg (h.pos i).le,← abs_mul,hh,abs_neg]
       calc
           _ ≤ ∑ k, |residual e T n i k| * |U n k j| := by simpa only [← abs_mul] using Finset.abs_sum_le_sum_abs _ _
           _ ≤ ∑ k, ((if k∈s then K* |U n k j| else 0)+B* |U n k j|) := sum_le_sum fun k _=> by
              by_cases hv : k∈s
              · rw [if_pos hv]
                exact (mul_le_mul_of_nonneg_right (H i k) (abs_nonneg _)).trans (le_add_of_nonneg_right (mul_nonneg hB (abs_nonneg _)))
              rw [gapMem] at hv;rw [if_neg (by intro he; exact hv ((gapMem _ _ _).1 he)),zero_add] -- gapMem only hv?
              have hki : e i < e k := lt_of_lt_of_le hi (le_of_not_gt hv)
              refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
              have hh : i≠k := fun he=> hki.ne (congr_arg e he)
              rw [residual,if_neg hh,sub_zero]
              exact hm i k hki
           _ = K*portion e U j n+B*whole U j n := by
              simp_rw [sum_add_distrib,←sum_filter,portion,whole,s,filter_mem_eq_inter,←mul_sum,univ_inter]
           _ ≤ _:= by gcongr
   rw [show (Fintype.card V:ℝ)*(K*portion e U j n+B*A)=(∑ i:V,(K*portion e U j n+B*A)) from by simp;ring]
   exact (sum_le_sum fun i hi=> ha i hi).trans (sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun _ _ _=> by
      have hw : 0≤portion e U j n:= sum_nonneg (fun _ _=> abs_nonneg _)
      have hz : 0≤whole U j n:= sum_nonneg (fun _ _=> abs_nonneg _)
      exact add_nonneg (mul_nonneg hK hw) (mul_nonneg hB (hz.trans hA)))

def dualEnergy (e:V→ℝ) i := (e i)⁻¹
def transpose (U:TimeArray V) : TimeArray V := fun t i j=> U t j i

theorem inverse_step : StepEstimate (dualEnergy e) (transpose U) := by
   obtain ⟨m,hm,hM⟩:=energyLower h
   have ht i : dualEnergy e i >0 := inv_pos.2 (h.pos i)
   let d:= (Fintype.card V:ℝ)
   obtain ⟨K,hK,hT⟩:= h.close
   have he := duration_leads.const_div_atTop (d*K)
   constructor
   · exact ht
   · refine ⟨K*(2/m)/m,by positivity, ?_⟩
     filter_upwards [hT,he.eventually (gt_mem_nhds (half_pos hm))] with n hn hF i j
     have hG:= inverse_global h hU n hm hM hK hF.le hn
     have hf := duration_large n
     have hQ:= inverse_error h hU n i j hn (by positivity) (hG i)
     have hj:= h.pos j
     have hi:= h.pos i
     have hh : residual (dualEnergy e) (transpose U) n i j =
        (e j * U n j i-eye j i)/e j := by
          dsimp [eye,residual,dualEnergy,transpose]
          by_cases h':i=j
          · rw [h',if_pos rfl]; field_simp;simp
          rw [if_neg h',if_neg (Ne.symm h')];field_simp;ring
     rw [hh, abs_div, abs_of_pos hj]
     calc
         _ ≤ (K/(duration n)*(2/m))/e j:= div_le_div_of_nonneg_right hQ hj.le
         _ ≤ (K/(duration n)*(2/m))/m := div_le_div_of_nonneg_left (by positivity) hm (hM j)
         _ = _:= by ring
   intro q i j hi
   have hji : e j < e i := (inv_lt_inv₀ (h.pos _) (h.pos _)).1 hi
   obtain ⟨B,hB,hT'⟩:= higherTogether h q
   refine ⟨2*d*B*(2/m)/m,by dsimp [d]; positivity,?_⟩
   filter_upwards [hT,hT',he.eventually (gt_mem_nhds (half_pos hm))] with n hn h' hF
   have hG:=inverse_global h hU n hm hM hK hF.le hn
   have hf:=duration_large n
   have hk := hK
   let p:=portion e U i n
   have hl:=inverse_partial h hU n i h' hn (hG i) (by positivity) (by positivity)
   have hP : m*p ≤ ∑ j∈gapSupport e i, e j * |U n j i| := by
      dsimp only [p,portion]; rw [Finset.mul_sum];gcongr;exact hM _
   have hp :0 ≤ p:= sum_nonneg fun _ _=>abs_nonneg _
   have hz:= hP.trans hl
   have hd : 0 < m*(duration n)^q := by positivity
   have hh : m*(duration n)^q*p ≤ 2*d*B*(2/m) := by
       have hm' : m*p≤ d*(K/(duration n)*p+B/(duration n)^q*(2/m)) := hz
       field_simp at hm' hF
       apply le_of_mul_le_mul_right (a:=m*(duration n)) ?_ (by positivity)
       rw [show (2*d*B*(2/m)) * (m * duration n) = (2*d*B)*2*(duration n) from (by field_simp)]
       nlinarith only [hm',mul_le_mul_of_nonneg_left hF.le (show 0 ≤ m*p*(duration n)^q from by positivity)]
   exact (Finset.single_le_sum (s:=gapSupport e i) (fun j _=>abs_nonneg (U n j i)) ((gapMem e i j).mpr hji)).trans (show p ≤ _ from by rw [le_div_iff₀ (by positivity : 0<duration n^q),le_div_iff₀ hm]; linarith only [hh])

omit hU in
theorem StepEstimate.layers {Z : TimeArray V}
     (H : ∀ n i j, Z (n+1) i j=(∑ k, T n i k * Z n k j)/e j)
     (hZ : ∀ n i j,e j < e i → Z n i j = 0) : Law e Z T where
   filtered := hZ
   positive := h.pos
   evolve := H
   diagonal := by
       obtain ⟨K,hK,hT⟩:=h.close
       intro j
       let A:= ((Finset.univ:Finset V).card:ℝ)/e j
       have hp:=h.pos j
       refine ⟨A*K, mul_nonneg (by dsimp [A]; positivity) hK,?_⟩
       refine hT.mono fun n hn k hk => ?_
       simp only [correction,abs_div,abs_of_pos hp,←sum_div]
       have hC:= Finset.sum_le_sum (s:=univ) (fun i _=> hn i k)
       simp_rw [sum_const,nsmul_eq_mul] at hC -- may not sum_const exact?
       exact (div_le_div_of_nonneg_right hC hp.le).trans (le_of_eq (by dsimp only [A]; ring))
   lower := by
       intro j q
       obtain ⟨D,hD,hT⟩:=higherTogether h q
       let A:= ((gapSupport e j).card:ℝ)/e j
       have hp:=h.pos j
       refine ⟨A*D,mul_nonneg (by positivity) hD, hT.mono fun n hn k hk=> ?_⟩
       have heq i (hi : i∈gapSupport e j) : residual e T n i k = T n i k := by
            have hx : i≠k := by rintro rfl; exact (ne_of_lt ((gapMem _ _ _).mp hi)) hk
            simp [residual,hx]
       have he i (hi : i∈ gapSupport e j) : |residual e T n i k| ≤ _ :=
           heq i hi ▸ (hn i k ((gapMem _ _ _).mp hi |>.trans_le (le_of_eq hk.symm)))
       simp only [correction,abs_div,abs_of_pos hp,←sum_div]
       have hC:=Finset.sum_le_sum (s:=gapSupport e j) he
       simp_rw [sum_const,nsmul_eq_mul] at hC
       exact (div_le_div_of_nonneg_right hC hp.le).trans (le_of_eq (by dsimp only [A]; ring))

end YM.Pert.Flow.Layer
