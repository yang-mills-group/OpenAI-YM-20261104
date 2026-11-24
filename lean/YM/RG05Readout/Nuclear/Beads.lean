import YM.PertExtension.WilsonGrid
import YM.RG05Readout.Nuclear.Stalks
/-! Partitions from accepted smooth tent, finite spacing tokens. Works on
 larger boxes, derivative atoms.Retype orientations only at assignment.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse PertExtension.LatticePT.Band Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{V J:Type}[Fintype V][DecidableEq V]
local notation "U"=>Cloud V
local notation "W"=> Wave V
noncomputable def Hood : Body:=⟨hood,hood_smooth⟩
lemma tent_I {t:ℝ}(ht:|t|<1/4): tent t=1:=by unfold tent; rw [rise_zero (by linarith [(abs_lt.mp ht).2]),rise_zero (by linarith [(abs_lt.mp ht).1]),sub_zero,sub_zero]
lemma hood_body {x:E4}(h:‖x‖<1/4): Hood.val x=1:=by
   change (∏ i:Axis, tent (x i))=_; apply Finset.prod_eq_one; intro i _; apply tent_I; exact lt_of_le_of_lt (PiLp.norm_apply_le x i) h
lemma hood_live (x:E4)(hx:x∈ tsupport Hood.val): ‖x‖≤2:=by
   exact closure_minimal (fun (x:E4) (hx:x∈ Function.support Hood.val)=> le_of_not_gt fun h=> hx (hood_away h)) (isClosed_le (f:=Norm.norm) continuous_norm (continuous_const (y:=(2:ℝ)))) hx
noncomputable def pebble (r:ℝ)(x:E4):=patchShift x r Hood
lemma track (r:ℝ)(x y:E4)(v:Body): (patchShift x r v).val y=v.val (r⁻¹ • (y-x)):=by change v.val (-r⁻¹ • x+r⁻¹ • y)=_;rw [smul_sub,neg_smul,sub_eq_neg_add]
lemma pebble_live (r:ℝ)(hr:0<r)(x y:E4)(h:y∈tsupport (pebble r x).val): ‖y-x‖≤2*r:=by
    refine closure_minimal (fun z (hz:z ∈ Function.support (pebble r x).val)=>?_) (isClosed_le (f:=fun z=> ‖z-x‖) ((continuous_id.sub continuous_const).norm) (continuous_const (y:=2*r))) h
    have hi:¬2 < ‖r⁻¹ • (z-x)‖:=fun h=> hz ((track ..).trans (hood_away h))
    rw [norm_smul,Real.norm_of_nonneg (by positivity),mul_comm,←div_eq_mul_inv,not_lt,div_le_iff₀ hr] at hi; exact hi
lemma emblaze (r:ℝ)(hr:0<r)(x y:E4)(h:‖y-x‖<r/4): (pebble r x).val y=1:=by
    unfold pebble; rw [track]; apply hood_body; rw [norm_smul,Real.norm_of_nonneg (by positivity),mul_comm,←div_eq_mul_inv,div_lt_iff₀ hr]; linarith
noncomputable def clue (r:ℝ)(x:Cover):E4:= WithLp.toLp 2 fun i=> r*x i
abbrev room (N:ℕ):Finset ℤ:= Finset.Icc (-(N:ℤ)) (N:ℤ)
noncomputable def fan (N:ℕ):Finset Cover:=Fintype.piFinset (fun _=>room N)
noncomputable def plot (V:Type)[Fintype V][DecidableEq V](N:ℕ):= Fintype.piFinset (fun _ : V=>fan N)
theorem fan_axis_card (N:ℕ): (room N).card=2*N+1:=by unfold room; rw [Int.card_Icc];omega
lemma fan_size (N:ℕ): (fan N).card=(2*N+1)^4:=by unfold fan; rw [Fintype.card_piFinset]; simp only [Finset.prod_const, Finset.card_univ,fan_axis_card];rfl
lemma lead_tol (N:ℕ) (x:ℝ)(hx:|x|+2≤N): ∑ i∈room N,tent (x-i)=1:=by
    let s:=⌊x⌋; have hp:s≤x∧x< (s:ℝ)+1:= ⟨Int.floor_le x,Int.lt_floor_add_one _⟩
    have h': -(N:ℤ)≤s∧ s+1≤ (N:ℤ):= by
        have hz:=abs_le.mp (show |x|≤ N-2 by linarith); constructor
        · exact_mod_cast (show -(N:ℝ)≤(s:ℝ) from by linarith)
        exact_mod_cast (show (s:ℝ)+1≤N from by linarith)
    let T:Finset ℤ:={s,s+1}; have hr : T⊆room N:=by
        intro j h; cases Finset.mem_insert.mp h with
        | inl ht=> rw [ht]; exact Finset.mem_Icc.mpr (by omega)
        | inr ht=> rw [Finset.mem_singleton.mp ht]; exact Finset.mem_Icc.mpr (by omega)
    rw [← Finset.sum_subset hr];
    · unfold T; rw [Finset.sum_pair (by omega)]; push_cast; rw [show x-((s:ℝ)+1)=(x-s)-1 by ring]; exact halves _ (by linarith) (by linarith)
    intro i _ hv; apply tent_small; by_cases he:s ≤ i
    · have ht:s+2 ≤ i:=by have he':i≠s+1:=fun h=>hv (by simp [T,h]); have hl:i ≠ s:=fun h=>hv (by simp [T,h]); omega
      exact le_abs.mpr (Or.inr (by linarith [(show (s:ℝ)+2 ≤ (i:ℝ) from by exact_mod_cast ht)]))
    have ht:(i:ℝ)+1 ≤ s:=by exact_mod_cast (Int.add_one_le_of_lt (lt_of_not_ge he))
    exact le_abs.mpr (Or.inl (by linarith))
noncomputable def rateBlue (s r:ℝ):ℕ:= ⌈s/r+3⌉₊
lemma market (S r:ℝ)(hr:0<r)(x:E4)(h:‖x‖< S):
    ∑ i ∈ fan (rateBlue S r), (pebble r (clue r i)).val x=1:=by
    let g (i:Axis)(j:ℤ):= tent (x i/r-(j:ℝ)); let N:=rateBlue S r; have hp(i):∑ j∈ room N,g i j=1:=by
        refine lead_tol _ _ ?_; have ht:= (show |x i| ≤ ‖x‖ from PiLp.norm_apply_le x i); have he:S/r+3 ≤ N:=Nat.le_ceil _ -- edit
        rw [abs_div,abs_of_nonneg hr.le]; linarith [div_lt_div_of_pos_right (lt_of_le_of_lt ht h) hr]
    calc
       _=∑ i∈ Fintype.piFinset (fun _:Axis=> room N),∏ j:Axis,g j (i j):=by
             apply Finset.sum_congr rfl; intro i _; unfold pebble; rw [track]; change (∏ j:Axis,tent ((r⁻¹ • (x-clue r i)) j))=_; refine Finset.prod_congr rfl fun j _=>?_
             unfold g; apply congr_arg tent; change r⁻¹*(x j-r*(i j))=_; field_simp
       _=1:=by rw [← Finset.prod_univ_sum]; simp_rw [hp,Finset.prod_const_one]
noncomputable def bundle (r:ℝ)(x:U): W:=joint Finset.univ (fun i=> pebble r (x i))
omit [DecidableEq V] in
lemma trifold (x:U)(y:U)(r:ℝ)(hr:0<r)(hp:‖x-y‖< r/4): (bundle r x).val y=1:=by
   unfold bundle; refine Finset.prod_eq_one (fun i _=>?_); rw [emblaze _ hr]; rw [norm_sub_rev]; exact lt_of_le_of_lt (norm_le_pi_norm (x-y) i) hp
omit [DecidableEq V] in
lemma bundle_die (x y:U)(r:ℝ)(hr:0<r)(hy:2*r<‖y-x‖): (bundle r x).val y=0:=by
   unfold bundle; by_contra hx
   have hv(i): (pebble r (x i)).val (y i) ≠ 0:= fun h=>hx (Finset.prod_eq_zero (f:=fun i=>(pebble r (x i)).val (y i)) (Finset.mem_univ i) h)
   have hp:= fun i=> pebble_live r hr _ _ (subset_closure (show _∈ Function.support _ from hv i)); exact (not_le.mpr hy) ((pi_norm_le_iff_of_nonneg (by positivity)).mpr hp)
omit [DecidableEq V] in
lemma bundled (x:U)(r:ℝ)(hr:0<r) (y:U)(h:y∈ tsupport (bundle r x).val): ‖y-x‖ ≤ 2*r:=
    closure_minimal (fun y (h:y ∈ support (bundle r x).val)=>le_of_not_gt fun e => h (bundle_die x y r hr e)) (isClosed_le (f:=fun y=> ‖y-x‖) ((continuous_id.sub continuous_const).norm) (continuous_const (y:=2*r))) h
lemma fair (S r:ℝ)(hr:0<r)(x:U)(h:‖x‖<S): ∑ i ∈ plot V (rateBlue S r), (bundle r (clue r ∘ i)).val x=1:=by
    unfold plot bundle joint; change (∑ i∈Fintype.piFinset (fun _ : V=> fan (rateBlue S r)),∏ j, (pebble r (clue r (i j))).val (x j))=_
    rw [← Finset.prod_univ_sum (fun _ : V => fan (rateBlue S r)) (fun j k =>(pebble r (clue r k)).val (x j))]; apply Finset.prod_eq_one; intro i _; exact market S r hr (x i) (lt_of_le_of_lt (norm_le_pi_norm x i) h)
lemma plot_size (N:ℕ): (plot V N).card = (2*N+1)^(4*Fintype.card V):=by unfold plot; rw [Fintype.card_piFinset]; simp_rw [Finset.prod_const, Finset.card_univ, fan_size,pow_mul]
noncomputable def load (V:Type)[Fintype V](S:ℝ):=(2*S+10)^(4*Fintype.card V)
lemma leaves (S r:ℝ)(hs:0≤S)(hr:0<r)(ht:r≤1): ((plot V (rateBlue S r)).card:ℝ) ≤ load V S*r⁻¹^(4* Fintype.card V):=by
    rw [plot_size]; unfold load; push_cast; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity) _; have he := Nat.ceil_lt_add_one (show 0 ≤ S/r+3 from by positivity); unfold rateBlue; rw [← div_eq_mul_inv]; apply (le_div_iff₀ hr).2
    nlinarith [mul_le_mul_of_nonneg_right he.le hr.le,mul_pos (show (0:ℝ)< 3 by norm_num) hr, div_mul_cancel₀ S hr.ne']
end YM.RG05Readout.Nuclear
