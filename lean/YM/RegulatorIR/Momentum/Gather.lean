import YM.RegulatorIR.Momentum.Bore

/-! Tariff equivalence. Offsets unbounded. Convert at either endpoint
only for strict transitions, or via announced pre-purchases. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Momentum
open Function Set Filter Finset Lattice RG Gauge Budget Budget.Packet Budget.Tuple Budget.Layer Geometry Uniform YM.RegulatorIR.Ledger Step Taping Precision Laurent Bloch Oracle Quadratic ENNReal
open scoped Topology ENNReal NNReal BigOperators Classical Matrix PowerSeries
variable {X I:Type}{n u:ℕ}{l:ℝ}
section spatial
variable (h:0<l)
def trim (l:ℝ) : Long X→Room:=fun x=> seat l x.1
def path (h:0<l)(X:Type)(u:ℕ):= (Tariff.native l h u).uses (trim (X:=X) l)
include h
lemma plaque_dist (i j:Long X) : dist (trim l i) (trim l j) ≤ l * (1+(size (area i-area j):ℝ)):=by
 let a:= glint l i.1.2;let b:= glint l j.1.2; let v:=area i-area j
 have ht:= add_le_add (shade_lo h i.1.2) (shade_lo h j.1.2)
 have hp: ‖a-b‖≤ l:=(norm_sub_le ..).trans (ht.trans_eq (by ring))
 unfold trim;rw [dist_eq_norm, show seat l i.1-seat l j.1=Motion.slide l v+(a-b) from by unfold seat v; rw [map_sub];change Motion.slide l (area i) + a-(Motion.slide l (area j)+b)=_; abel]
 refine (norm_add_le ..).trans ((add_le_add (show ‖Motion.slide l v‖ ≤ l*(Laurent.size v) from ?_) hp).trans_eq (by unfold v; ring))
 apply (pi_norm_le_iff_of_nonempty _).mpr; intro t; rw [Motion.slide_apply,norm_mul,Real.norm_of_nonneg h.le]; apply mul_le_mul_of_nonneg_left _ h.le;rw [← norm_natAbs,Real.norm_natCast];exact_mod_cast (single_le_sum (s:=Finset.univ) (f:=fun i=>(v i).natAbs) (fun _ _=> Nat.zero_le _) (mem_univ t))
lemma plaqueE (u) (i j:Long X): (path h X u).road i j ≤ (2:ℝ≥0∞)^u *(1+extent (area i-area j))^u:=by
 change Tariff.amount .. ≤ _; apply le_trans (Tariff.amount_mono h _ (plaque_dist h i j));unfold Tariff.amount; rw [mul_div_cancel_left₀ _ h.ne', ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, ENNReal.ofReal_natCast,← mul_pow]; apply pow_le_pow_left'; change 1+ (1+extent _) ≤2*_; rw [two_mul,add_comm];exact add_le_add_right le_self_add _
lemma points_far (i j:Long X) : l*(size (area i-area j):ℝ) ≤ 4*(l+dist (trim l i) (trim l j)):=by
 let v:=area i-area j
 have he:‖Motion.slide l v‖ ≤ l+dist (trim l i) (trim l j):=by
    let a:= glint l i.1.2;let b:=glint l j.1.2
    rw [show Motion.slide l v= b-a+(trim l i-trim l j) from by unfold v; rw [map_sub]; change _= b-a+(Motion.slide l (area i)+a-(Motion.slide l (area j)+b)); abel]
    rw [dist_eq_norm]; apply (norm_add_le ..).trans; apply add_le_add_left; exact (norm_sub_le ..).trans ((add_le_add (shade_lo h j.1.2) (shade_lo h i.1.2)).trans_eq (by ring))
 let f:= l+dist (trim l i) (trim l j)
 change l*(size v:ℝ)≤4*f; unfold size;push_cast;rw [mul_sum]; apply le_trans _ (le_of_eq (show (∑ _:Axis,f)=4*f by simp [Axis]))
 apply sum_le_sum;intro u _; have ht: ‖(Motion.slide l v) u‖ ≤ f := norm_le_pi_norm _ _|>.trans he; rw [Motion.slide_apply,norm_mul,Real.norm_of_nonneg h.le, ←norm_natAbs,Real.norm_natCast] at ht;exact ht
lemma pointsE (u) (i j:Long X) : (1+extent (area i-area j))^u ≤ (5:ℝ≥0∞)^u * (path h X u).road i j:=by
 let s:= size (area i-area j); let d:=dist (trim l i) (trim l j); let v:=d/l; have hv : 0 ≤ v:= div_nonneg dist_nonneg h.le
 change (1+ (s:ℝ≥0∞))^u ≤5^u* ENNReal.ofReal (1+v)^u; rw [← mul_pow]; apply pow_le_pow_left';
 have hp:= points_far h i j; change l*(s:ℝ) ≤ 4*(l+d) at hp
 rw [← ENNReal.ofReal_one,← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add zero_le_one (Nat.cast_nonneg _), ← show ENNReal.ofReal 5=5 from by simp, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
 apply ENNReal.ofReal_le_ofReal
 have hh: (s:ℝ)≤ 4*(1+v):= (mul_le_mul_iff_right₀ h).mp (hp.trans_eq (by unfold v; field_simp))
 linarith
end spatial
section hold
variable (p:Tuple (Long X) n)(i:Long X)(h:0<l)
lemma residence : (path h X u).diameter (Fin.cons i p) ≤ (4:ℝ≥0∞)^u * wall (area i) 1 u p:=by
 let T:= (path h X u); let g:= area ∘ Fin.cons i p; let f(t:Long X):= extent (area i-area t);let P:=∑ v:Fin n,f (p v);
 unfold wall awayZ; simp_rw [award,Nat.cast_one,inv_one,one_smul,one_mul]
 change _ ≤ (4:ℝ≥0∞)^_* (1+P)^_
 rw [← mul_pow]; apply T.diameter_le
 · apply one_le_pow₀;exact one_le_mul_of_one_le_of_one_le (by norm_num) le_self_add
 intro a b; let x: Long X :=(Fin.cons i p: Tuple (Long X) (n+1)) a; let y: Long X :=(Fin.cons i p: Tuple (Long X) (n+1)) b
 have he(v: Fin (n+1)):f ((Fin.cons i p: Tuple (Long X) (n+1)) v) ≤ P := by
    induction v using Fin.cases
    · rw [Fin.cons_zero]; unfold f;rw [sub_self,extent_zero]; exact bot_le
    next t=>
      rw [Fin.cons_succ]; exact Finset.single_le_sum (f:=fun v=>f (p v)) (fun _ _=>zero_le) (mem_univ t)
 have hp:extent (area x-area y)≤ P+P:= by nth_rewrite 1 [show area x-area y= -(area i-area x)+(area i-area y) from by abel]; exact (extent_add ..).trans (by rw [extent_neg];exact add_le_add (he a) (he b))
 apply le_trans (plaqueE h u x y); rw [← mul_pow]; apply pow_le_pow_left';
 calc
    _ ≤ (2:ℝ≥0∞)*(1+(P+P)):= mul_le_mul_right (add_le_add_right hp _) _
    _ ≤ 2*(2+(P+P)):=by gcongr; exact one_le_two
    _ = _:=by ring
private lemma diameter_one (p:Tuple (Long X) n): (path h X u).diameter p=(path h X 1|>.diameter p)^u:=by
 let L:=path h X 1; have H (x y): (path h X u).road x y=L.road x y^u:=by
    change ENNReal.ofReal _ ^u= (ENNReal.ofReal _ ^1)^u; rw [pow_one]
 by_cases hn:n=0
 · subst n; unfold Tariff.diameter;simp
 have _: Nonempty (Fin n):= Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
 let f (x:Fin n× Fin n):= L.road (p x.1) (p x.2)
 obtain ⟨⟨a,b⟩,-,hv⟩:= Finset.exists_max_image Finset.univ f Finset.univ_nonempty
 have hp: L.diameter p ≤ L.road (p a) (p b):= Tariff.diameter_le _ (L.unit ..) (fun i j=> hv (i,j) (mem_univ _))
 apply le_antisymm
 · refine Tariff.diameter_le _ (one_le_pow₀ (Tariff.diameter_unit ..)) (fun i j=>?_);rw [H];exact pow_le_pow_left' (L.diameter_ge ..) _
 apply le_trans (pow_le_pow_left' hp _); rw [← H]; exact Tariff.diameter_ge ..
lemma living : wall (area i) 1 u p ≤ ((1+n*5:ℝ≥0∞))^u * (path h X u).diameter (Fin.cons i p):=by
 let T:= path h X 1; let f(v:Fin n):=extent (area i-area (p v))
 have he(v:Fin n): f v≤5 *(T.diameter (Fin.cons i p)) :=by
   apply le_trans (b:=1+f v) le_add_self; have hp:= pointsE h 1 i (p v); rw [pow_one,pow_one] at hp; apply hp.trans; have ht:= (path h X 1).diameter_ge (Fin.cons i p) 0 v.succ; rw [Fin.cons_zero,Fin.cons_succ] at ht; exact mul_le_mul_right ht _
 unfold wall awayZ; simp_rw [award,Nat.cast_one,inv_one,one_smul,one_mul];rw [diameter_one h _, ← mul_pow]; apply pow_le_pow_left'
 apply le_trans (add_le_add_right (Finset.sum_le_sum (fun v _=>he v)) _);simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,add_mul,one_mul]; rw [mul_assoc (↑n:ℝ≥0∞) 5]; exact add_le_add_left (Tariff.diameter_unit ..) _
end hold
end YM.RegulatorIR.Momentum
