import YM.FVA2.Inking
/-! # Vanishing property of formal frame products through weight N.
 growth of previous coefficients never used. κ and canonicalField converted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Erase
open Set Filter Function Finset MeasureTheory Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Jet PositionX.Ribbon Topology Elegant Verne Counterpart
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}{F:Labels.Frames G}{d n k:ℕ}{X:Type*}[NormedRing X][NormedAlgebra ℝ X] {f g:ℝ→X} {W U:Word X}
lemma inter_links (h:Act n f W)(he:Act n g U): Act n (f*g) ( fun k=> ∑ i∈ Finset.range (k+1), W i * U ( k-i ) ):= by
    refine ⟨ h.nice.mul he.nice,fun j hj=>?_⟩; unfold someJ; rw [iteratedDeriv_mul (h.nice.of_le le_top) (he.nice.of_le le_top), Finset.smul_sum ]; apply Finset.sum_congr rfl; intro i hi; obtain hk:= Finset.mem_range.mp hi; rw [h.actual i (by omega), he.actual _ (by omega), ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_mul_assoc, smul_mul_assoc, mul_smul_comm ]; simp only [smul_smul, ← mul_assoc (j.choose i:ℝ)]; rw [ show ( ( j.choose i:ℝ )*( i.factorial:ℝ )*(Nat.factorial (j-i):ℝ))=(j.factorial:ℝ) from by exact_mod_cast Nat.choose_mul_factorial_mul_factorial ( Nat.lt_add_one_iff.mp hk ), inv_mul_cancel₀ ( by positivity ),one_smul ]
lemma reservation {n:ℕ}(a b:Word (Buffer F d)) : (luxury a b n).val= (a n).val+(b n).val+∑ i∈ Finset.range (n+1), (a i).val*(b (n-i)).val:= by
    let x:= delay a n; let y:= delay b n; let A:= E F d →L[ℝ] E F d; let L:Buffer F d→L[ℝ] ( E F d→L[ℝ] E F d ) := ( buffers F d ).subtypeL;
    have hx:Act n x a:= Act.swell a le_rfl; have hy:Act n y b:= Act.swell b le_rfl; have hp:Act n (L ∘ x) ( L ∘ a ):= Act.linear (L:=L) (G:= E F d →L[ℝ] E F d) hx; have hc: Act n (L ∘ y) (L ∘ b):= Act.linear (L:=L) (G:=E F d →L[ℝ] E F d) hy; have hu : Act n ( L ∘ (fun t:ℝ=> settled ( x t,y t))) ( L ∘ luxury a b):= by apply Act.linear (L:=L) (E:=Buffer F d) (G:=E F d →L[ℝ] E F d) ((hx.zipper hy).transit (m:=settled) settled_diff.contDiffAt);
    have H:( L ∘ (fun t:ℝ=> settled ( x t,y t)))=( L ∘ x)+(L ∘ y)+(L ∘ x)*(L ∘ y):= funext fun i=>rfl; rw [ H ] at hu; exact hu.trans_at (( hp.add hc ).add ( inter_links (X:= E F d →L[ℝ] E F d) hp hc )) le_rfl
-- if a(x),b(x) coarse report adjust.B.tokens. pay; H.fixed.
local notation "ℓ"=> Buffer F d
local notation "Op"=> E F d →L[ℝ] E F d
variable {a b c q: Word (Buffer F d)}
lemma front_cut (hx: luxury a c= luxury b q)(he : a 0=0)(h:∀ i<n, a i=b i) (i:ℕ)(hi:i<n) : c i=q i:= by
    induction i using Nat.strong_induction_on with| h i ih=>
       apply Subtype.ext; obtain hh:= congr_arg (fun x:Word (Buffer F d)=> (x i).val ) hx; rw [ reservation,reservation,h _ hi,add_comm ( (b i).val ),add_comm ( ( b i ).val ) ] at hh; -- sum equality
       suffices hL : ∑ k∈Finset.range (i+1), (a k).val*(c (i-k)).val=∑ k∈Finset.range (i+1),(b k).val*(q (i-k)).val from (by rw [hL] at hh; simpa only [add_left_inj] using hh)
       refine Finset.sum_congr rfl fun j hj=>?_ ; by_cases hz:j=0; · subst j; rw [←h 0 (by omega),he ]; change 0*_=0*_; simp
       obtain ht:= Finset.mem_range.mp hj; rw [h _ (by omega), ih _ (by omega) (by omega) ]
lemma frontier (hx: luxury a c= luxury b q)(he : a 0=0)(hn:0<n)(h:∀ i<n, a i=b i) : (( a n ).val - ( b n ).val) * (1+(q 0).val)= (q n).val-(c n).val:= by
    let Ξ (j:ℕ):=( a j ).val*( c ( n-j ) ).val; let Z(j):=( b j ).val*( q ( n-j ) ).val; have hl:∑ j∈ range n,Ξ j=∑ j∈range n,Z j:= by apply Finset.sum_congr rfl; intro j hj; obtain hv:=mem_range.mp hj; unfold Ξ Z; by_cases hz:j=0; subst j; rw [← h 0 hn, he ]; change 0*_=0*_; simp; rw [ h j hv, front_cut hx he h _ (by omega) ];
    obtain hh := congr_arg (fun x:Word ( Buffer F d )=> (x n).val) hx; rw [ reservation,reservation, Finset.sum_range_succ, Finset.sum_range_succ, hl, Nat.sub_self,front_cut hx he h 0 hn ] at hh; rw [mul_add,mul_one,sub_mul ]; linear_combination (norm:=abel) hh -- syntax
-- removing small term estimates.B.near
omit [NormedAlgebra ℝ X] in
private lemma lemmaW (F G:X)(h: ‖G‖≤ (1/2:ℝ) ): ‖F‖ ≤ 2* ‖F*(1+G)‖:= by
    have h' := ( norm_mul_le F G ).trans (mul_le_mul_of_nonneg_left h (norm_nonneg F)); rw [mul_add,mul_one ]; obtain he := norm_add_le ( F+F*G ) ( -(F*G) ); rw [norm_neg (E:=X)] at he; rw [ add_assoc,add_neg_cancel,add_zero ] at he; linarith
variable {W U:ℕ→ Word (Buffer F d)}{A B:ℕ→ Word (Buffer F d)}
lemma clean_ξ (hx:∀ᶠ i in atTop,luxury ( W i ) ( A i ) = luxury (U i) ( B i ))(h:∀ᶠ i in atTop, W i 0=0 ∧ ∀ t<n, W i t= U i t)(hn:0<n)(hB:Tendsto (fun i=> B i 0) atTop (𝓝 0))(he:Tendsto (fun i=>B i n-A i n) atTop (𝓝 0)): Tendsto (fun i=> W i n-U i n) atTop (𝓝 0):= by
    let S(Y:ℕ→Buffer F d): Tendsto Y atTop (𝓝 0) ↔ Tendsto (fun i=> ‖Y i‖) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero (E:=Buffer F d); obtain hj:= ((S _).1 hB).eventually ( gt_mem_nhds (half_pos (by norm_num : (1:ℝ)>0)) ); rw [ S ]; refine squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) ?_ ( show Tendsto (fun i=>2*‖B i n-A i n‖) atTop (𝓝 0) from ( by simpa only [mul_zero] using! (( (S _).1 he )|>.const_mul 2) ) ); filter_upwards [hx,h,hj] with i hi he h; obtain H:=( lemmaW ((W i n).1-(U i n).1) (B i 0).1 (show ‖ ( B i 0 ).val‖ ≤ (1/2:ℝ) from le_of_lt h )); rw [frontier hi he.1 hn he.2 ] at H; exact H
end YM.FVA2.Erase
