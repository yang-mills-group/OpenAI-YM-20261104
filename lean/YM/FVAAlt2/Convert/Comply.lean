import YM.FVAAlt2.Convert.Honors
/-!
# Rotate finite-calibration supports together through weight/projector (grammar)

Use real polynomial costs (not asymptotic estimates). `Permit` then sufficient to
 rotate ANY admissible Period along *actual starts*. Assembly independent of log
 cutoff schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Convert
open Function Finset Filter MeasureTheory Lattice Matrix Polynomial
open MS MS.Koszul MS.Menus MS.Local.Physical MS.Land MS.FVA MS.FVA.Motions MS.FVA.Town MS.Lifting MS.Plane MS.Landau MS.Landau.Detect MS.Native MS.Theater
open FormalOPE FormalOPE.RG10 Labels Source Home
open MS.Book MS.Wind MS.Wind.Leading MS.High
open scoped Topology BigOperators ContDiff PowerSeries Classical Matrix
variable {G:Gauge} {F:Frames G}{B:Deck G}{d k n:ℕ}{p:ℤ}
local notation "ℓ"=> Polynomial ℝ
local notation "Θ"=> C (R:=ℝ)
variable (F) (Q:Plaid B d→Acts B d) (s t:Signed)
local notation "P"=> Plaid B d
local notation "Y"=> Glyph B d
local notation "N"=> stepR F B d
local notation "V"=> roster F B d
set_option quotPrecheck false
local notation:max "τ" n:max s:max=> (stepR F B n s).map (Polynomial.C (R:=ℝ))
set_option quotPrecheck false
local notation:max "φL" s:max=> (roster F B d s).map (Polynomial.C (R:=ℝ))
variable (B d) in
lemma low1 : N 1=1:= by unfold stepR; rw [θ₁]; simp -- need Map one
variable (B d) in
lemma ht1 : V 1=1:= by ext i j; apply Complex.ofReal_injective; rw [ real_price,step_id ]; by_cases h:i=j; subst j; all_goals simp [*]
-- likely real_price implicit F
lemma turn_comp(d:ℕ)(B:Deck G): stepR F B d s * stepR F B d t= stepR F B d (t*s):= by
 ext i j; apply Complex.ofReal_injective; rw [movesOn, Matrix.mul_apply, Complex.ofReal_sum, ← θτ F B d s t,Matrix.mul_apply]; apply Finset.sum_congr rfl; intro i _; rw [ Complex.ofReal_mul,movesOn,movesOn]
lemma price_comp(d:ℕ)(B:Deck G): roster F B d s * roster F B d t= roster F B d (t*s):= by
 ext i j; apply Complex.ofReal_injective; rw [real_price,Matrix.mul_apply,Complex.ofReal_sum,← Ξ_roll F B d s t, Matrix.mul_apply]; apply Finset.sum_congr rfl; intro i _; rw [Complex.ofReal_mul,real_price,real_price]
lemma notpaid (i j:P)(h: (Land.read i).grade ≠ (Land.read j).grade): V s i j=0:= only_r F s _ _ (fun ht=> h (congr_arg Prod.snd ht))
variable {F} -- Q has F? binder
abbrev wage_mat (B:Deck G) (d:ℕ)(Q:Plaid B d → Acts B d) (n:ℕ) : Matrix (Plaid B d) ( Glyph B d ) (Polynomial ℝ):= of fun i=> (Q i n).register
variable (F)
local notation "E"=> (wage_mat B d)

lemma swiv_matrix (n:ℕ): (E) (swiv F s Q) n=(φL s⁻¹)*(( E ) Q n*( τ d s )):= by ext1 i j; rfl
lemma net_mat (n:ℕ): (E) (net_A F Q) n= (Polynomial.C ((Fintype.card Signed:ℝ)⁻¹)) • ∑ s:Signed,(E) (swiv F s Q) n:= Matrix.ext fun i j=> by
 rw [Matrix.smul_apply,Matrix.sum_apply,Finset.smul_sum]; simp only [wage_mat,Matrix.of_apply,net_A,venture,smul_eq_mul] --
abbrev Permit (Q:Plaid B d→ Acts B d) := ∀ (s:Signed) n,(φL s)*(E Q n)= E Q n*( τ d s )
lemma stage_x(s t:Signed): τ d s * τ d t= τ d (t*s):= by rw [← Matrix.map_mul,turn_comp]
lemma stage_r(s t:Signed): φL s * φL t= φL (t*s):= by rw [← Matrix.map_mul,price_comp]
lemma permitted : Permit F (net_A F Q):= by
 intro s n; rw [net_mat]; simp_rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_sum,Matrix.sum_mul, swiv_matrix, Matrix.mul_assoc,stage_x]; rw [ ← Equiv.sum_comp (Equiv.mulLeft s) ]; refine congr_arg _ (Finset.sum_congr rfl fun k _=>?_); dsimp only [Equiv.mulLeft,Equiv.coe_fn_mk]; rw [← Matrix.mul_assoc (φL s),stage_r]; simp [mul_assoc]

-- init canopy φ rank.Saddle. `FitOrder` declared at Land.read i. ∀ i. Constructor.
abbrev firstOrder (Q:Plaid B d→ Acts B d):= ∀ i,FitOrder (Land.read i) (Q i 0)

lemma first_drive (H:firstOrder Q)(i:P)(y:ℝ): Limit (((swiv F s Q i 0).proof.input y):Dot G Cover).val ((Land.read i).grade-1):= by
 unfold swiv; change Limit ((∑ j:P,(↑((V s⁻¹) i j):ℂ) • Orient.pose s ((Q j 0).proof.input y))).val _; rw [MS.Cylinder.sum_stack]; apply Limit.sum; intro j _; by_cases h:(Land.read i).grade= (Land.read j).grade; · rw [h]; exact Limit.smul _ (FVA.City.poses_limit s ( H j |>.Low y ))
 rw [notpaid F s⁻¹ i j h,Complex.ofReal_zero,zero_smul]; exact fun _ _=>rfl
lemma drive_tag (H:firstOrder Q)(i:P)(j:Y)(he:(Land.read i).grade ≤ j.grade)(k: Signed): ∑ b:Y,(Q i 0).register b * C ((N k) b j)= C ((N k) ( Land.read i ) j) := by
 rw [Finset.sum_eq_single (Land.read i),(H i).Single _ le_rfl, if_pos rfl,one_mul]; swap; · simp
 intro b _ hb; by_cases hg:(Land.read i).grade ≤ b.grade; rw [( H i ).Single _ hg,if_neg hb, zero_mul]; rw [ only_r F k b j (fun ht=> hg (by rw [show b.grade=j.grade from congr_arg Prod.snd ht]; exact he )),map_zero,mul_zero]
lemma hedge (i:P)(j:Y): ∑ k: Y,(τ d s⁻¹) (Land.read i) k * ( τ d s ) k j= if j=Land.read i then 1 else 0:= by rw [ ← Matrix.mul_apply,stage_x, mul_inv_cancel,low1,Matrix.map_one _ (map_zero Polynomial.C) (map_one Polynomial.C) ]; by_cases h:j=Land.read i<;> simp [h, Matrix.one_apply,eq_comm] -- inspect
lemma bill₀swiv (hQ:firstOrder Q): firstOrder (swiv F s Q) := fun i=> by
 refine ⟨first_drive F Q s hQ i, fun j he=>?_ ⟩; let A:=φL s⁻¹; let β:=wage_mat B d Q 0; let S:=stepR F B d s; change ∑ a:P, C (roster F B d s⁻¹ i a) * ( ∑ k:Y,(Q a 0).register k * C ( (N s) k j ) ) = _; rw [← hedge F s i j]; let W (x':Y):= (τ d s⁻¹) (Land.read i) x' * C ( S x' j ); let f:= Land.read (d:=d) (B:=B); refine Eq.trans (b:=∑ i:P,W (f i)) ?_ ?_; rotate_left; -- caution
 · rw [← Finset.sum_image (f:=W)]; · apply Finset.sum_subset (Finset.subset_univ _); intro k _ hk; unfold W; rw [Matrix.map_apply, only_r F s⁻¹ (Land.read i) k (fun ht=>?_ ), map_zero,zero_mul]; obtain ⟨⟨a,ha⟩,u⟩:=k; have hg:a=d:= congr_arg Prod.fst ht.symm; subst a; exact hk (Finset.mem_image.mpr ⟨ u,mem_univ _,rfl ⟩)
   exact fun _ _ _ _ he=> eq_of_heq (Sigma.mk.inj he).2
 apply sum_congr rfl; intro k _; by_cases h:(Land.read k).grade= (Land.read i).grade; · rw [drive_tag F Q hQ k j (h.symm ▸ he) s]; rfl
 change C ((V s⁻¹) i k)*_= C ((V s⁻¹) i k)* _; rw [ notpaid F s⁻¹ i k (Ne.symm h), map_zero,zero_mul,zero_mul]
abbrev lump:= (Fintype.card Signed:ℕ)
lemma totalVote : (lump:Polynomial ℝ)* C ((lump:ℝ)⁻¹)=1 := by rw [ ← map_natCast Polynomial.C,← map_mul, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), map_one ]
lemma bill₀ (h:firstOrder Q): firstOrder (net_A F Q):= by
 intro i; constructor
 · intro x; simp only [net_A,venture,labor,kitty]; rw [MS.Cylinder.sum_stack]; exact Limit.sum _ (fun s _=>Limit.smul _ (( bill₀swiv F Q s h i ).Low x) )
 intro j hp; simp only [net_A,venture]; simp_rw [(show ∀ s:Signed,(swiv F s Q i 0).register j = _ from fun s=>(bill₀swiv F Q s h i).Single j hp)]; rw [Finset.sum_const, card_univ]; split_ifs <;> first| rw [nsmul_eq_mul,mul_one,totalVote]| simp

end YM.FVAAlt2.Convert

