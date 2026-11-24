import YM.Frontier6.Normal.Stripping

/-! Summation across one shell axis. Book **both** estimates from outside at
arbitrary incoming test scale. Keeps rates; also usable for tails. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Filter Set MeasureTheory Metric
open scoped Topology ContDiff BigOperators Classical
variable {Y:Type*}[NormedAddCommGroup Y]
def pitch (n:ℕ):ℝ:=(1/2:ℝ)^n
lemma pitches (i:ℕ): 0 < pitch i := pow_pos (by norm_num) _
lemma pitch_le (i:ℕ) : pitch i ≤ 1:= pow_le_one₀ (by norm_num) (by norm_num)
lemma pitch_even (i:ℕ): pitch (i+1)=pitch i/2:=by unfold pitch; rw [pow_succ]; ring
lemma pitch_mul (i j:ℕ): pitch (i+j)=pitch i*pitch j:= pow_add ..
lemma pitch_anti:Antitone pitch:= fun i j hij=>pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
lemma pitch_down:Tendsto pitch atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

lemma finite_rate (p:ℝ)(hp:0 < p): Summable (fun i:ℕ=> pitch i ^p):=by
    have ht:0 < (1/2:ℝ)^(p):=Real.rpow_pos_of_pos (by norm_num) _
    have he:(1/2:ℝ)^p < 1:=Real.rpow_lt_one (by norm_num) (by norm_num) hp -- check
    have hu(i:ℕ):pitch i ^p=((1/2:ℝ)^p)^i:=by
        unfold pitch; rw [←Real.rpow_natCast, ← Real.rpow_mul (by norm_num:0 ≤ (1/2:ℝ)),mul_comm (i:ℝ),Real.rpow_mul (by norm_num:0 ≤ (1/2:ℝ)),Real.rpow_natCast]
    simp_rw [hu]; exact summable_geometric_of_lt_one ht.le he

def Mass (f:ℕ → Y)(B:ℝ):Prop:= Summable (fun i=> ‖f i‖) ∧ (∑' i, ‖f i‖) ≤ B
lemma Mass.sums {f:ℕ → Y}[CompleteSpace Y]{B:ℝ}(h: Mass f B) : Summable f:=h.1.of_norm
lemma Mass.total {f:ℕ → Y}{B:ℝ}(h:Mass f B): ‖∑' i,f i‖ ≤ B:= (norm_tsum_le_tsum_norm h.1).trans h.2
lemma Mass.mono {f:ℕ → Y}{B P:ℝ}(h:Mass f B)(hp:B ≤ P): Mass f P:=⟨h.1,h.2.trans hp⟩

def Rates (a b s P:ℝ) (f:ℕ → Y):Prop:= (∀ i, pitch i ≤ s → ‖f i‖≤ (pitch i / s)^a * P) ∧
   ∀ i,s ≤ pitch i → ‖f i‖ ≤ (s/pitch i)^b * P

lemma cascade (a b:ℝ)(ha:0 < a)(hb:0 < b):∃ B:ℝ,0 ≤ B∧ ∀ (s P:ℝ), 0 < s → 0 ≤ P→∀ f:ℕ → Y,Rates a b s P f→ Mass f (B*P):=by
    let X:=∑' i,pitch i ^a; let W:=∑' i,pitch i ^b
    have hx:0 ≤ X:= tsum_nonneg fun i=>Real.rpow_nonneg (pitches i).le _; have hw:0 ≤ W:= tsum_nonneg fun i=>Real.rpow_nonneg (pitches i).le _
    refine ⟨W+X,add_nonneg hw hx,fun s P hs hP f hf=>?_⟩
    have he:∃ i:ℕ,pitch i ≤ s:= (pitch_down.eventually (ge_mem_nhds hs)).exists
    let m:=Nat.find he; have hm:pitch m ≤ s:=Nat.find_spec he; have hi(i:ℕ)(h:i<m): s < pitch i:=lt_of_not_ge (Nat.find_min he h)
    let F(i:ℕ):=‖f i‖; let μ(i:ℕ):= pitch i ^ a * P; let v(i:ℕ):=pitch i ^ b * P
    have hu(i:ℕ): F (i+m) ≤ μ i:= by
        have hg:pitch (i+m)≤s:=le_trans (pitch_anti (Nat.le_add_left m i)) hm
        apply (hf.1 (i+m) hg).trans; refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (div_nonneg (pitches _).le hs.le) ?_ ha.le) hP
        exact (div_le_iff₀ hs).2 (by rw [pitch_mul]; exact mul_le_mul_of_nonneg_left hm (pitches _).le)
    have hV(i:ℕ)(h:i<m): F (m-1-i) ≤ v i:=by
        have ht:s < pitch (m-1-i):=hi _ (by omega)
        apply (hf.2 _ ht.le).trans; refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (div_nonneg hs.le (pitches _).le) ?_ hb.le) hP; rw [div_le_iff₀ (pitches _),← pitch_mul, show i+(m-1-i)=m-1 by omega]; exact (hi _ (by omega)).le
    have hμ:Summable μ:=(finite_rate a ha).mul_right P; have hv:Summable v:=(finite_rate b hb).mul_right P
    have ha':Summable (fun i=> F (i+m)):= Summable.of_nonneg_of_le (fun i=> norm_nonneg _) hu hμ
    refine ⟨(summable_nat_add_iff m).mp ha',?_⟩
    rw [add_mul]; change (∑' i,F i) ≤ _; rw [← ((summable_nat_add_iff m).mp ha').sum_add_tsum_nat_add m]
    have hc': (∑' i, μ i)=X*P:=tsum_mul_right; have ht':(∑' i, v i)=W*P:=tsum_mul_right
    rw [← hc', ← ht',← Finset.sum_range_reflect]
    refine add_le_add (le_trans (Finset.sum_le_sum (g:=v) fun i hi=> ?_) (hv.sum_le_tsum _ (fun i _=> mul_nonneg (Real.rpow_nonneg (pitches _).le _) hP))) (ha'.tsum_le_tsum hu hμ)
    have hp: i<m:= Finset.mem_range.mp hi
    specialize hV i hp; convert hV using 1
end YM.Frontier6.Normal
