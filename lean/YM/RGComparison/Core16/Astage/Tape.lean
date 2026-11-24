import YM.RGComparison.Core16.Astage.Inverse
import YM.PertExtension.Aspiration
/-!
# Truncated series algebra for the accuracy bridge (Stage A)

Inputs include expected order billing SAME test/geometry. Use after normalizing to UNIT ν_t
shape norm. `ι` can include choice of unit test (take comap/prod filters, keeping uniformity).
 `Attached`: RateLE allows arbitrary tiny loss, ONLY used on estimates with
strict gains. Fk coefficients themselves require Wallet (already poly-Λ, not `T.scale m`).
No analytic construction in the next lemmas, but preserves independence of the prescribed
coefficient computation (uses exact Gram recursion, not calls to unknown actual solution).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage.Tape
open Function Filter Set OPE Asymptotics
open scoped Topology BigOperators Classical
variable {ι: Type}{Λ g:ι→ℝ}{l:Filter ι}
  {V W: Type*}[NormedAddCommGroup V][NormedSpace ℂ V]
    [NormedAddCommGroup W][NormedSpace ℂ W]
  (hz:Tendsto Λ l atTop)(hg:RateIs l Λ g (-(1/2:ℝ)))

/-- ordinary truncation through R -- equal to Series.Tested.peval in the density Laurent
normalization based on reports with negative engineering powers already restored. -/
def partialSum (g:ι→ℝ)(R:ℕ)(a:ℕ→ι→V)(i:ι):=∑ k∈ Finset.range (R+1),(↑((g i)^k):ℂ) • a k i
def action (A:ℕ→ι→V→L[ℂ] W)(a:ℕ→ι→V)(k:ℕ)(i:ι):=
    ∑ p∈ _root_.Finset.HasAntidiagonal.antidiagonal k,(A p.1 i) (a p.2 i)

/- This is the *post-iteration*, pre-readout estimate; includes truncation through R but losses
are before Gram solves. Need enough R to supply χ<-(r+1)/2. -/
def Attached (l:Filter ι)(Λ g:ι→ℝ)(A:ι→V)(a:ℕ→ι→V)(R:ℕ)(χ:ℝ):=
    RateLE l Λ (fun i=> A i - partialSum g R a i) χ
def Fits (l:Filter ι)(Λ:ι→ℝ)(a:ℕ→ι→V) (R:ℕ):=∀ k ≤ R, Wallet l Λ (a k)

variable {Y:ι→V}{R k d r:ℕ}{a c:ℕ→ι→V} {A:ℕ→ι→V→L[ℂ] W}{χ:ℝ}
include hz hg
lemma scale (h:Wallet l Λ Y) (k:ℕ): RateLE l Λ (fun i=> (↑((g i)^k) : ℂ) • Y i) (-(k:ℝ)/2):=by
    apply RateLE.of_norm_le ((((hg.power k|>.pays hz).mul ((h.subpower hz).norm))).mono (by linarith))
    filter_upwards [hg.pos] with i hi
    rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg hi.le k)]
lemma single (ha:Fits l Λ a R): Wallet l Λ (partialSum g R a):= by
    have hg':Wallet l Λ g:= Wallet.of_strict hz (hg.pays hz) (by norm_num)
    have hh(k:ℕ): Wallet l Λ (fun i=>(↑((g i)^k):ℂ)):= (hg'.pow hz k).transfer (Eventually.of_forall (fun _=> (Complex.norm_real _).le))
    exact Wallet.sum hz (fun k (hk:k∈ Finset.range (R+1))=> (hh k).smul (ha k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
omit hg hz in
lemma tear (h:d ≤ R) (i:ι): partialSum g R a i-partialSum g d a i= ∑ k∈ Finset.range (R+1) \ Finset.range (d+1), (↑(g i^k):ℂ) • a k i:= by
     rw [sub_eq_iff_eq_add]
     exact (Finset.sum_sdiff (Finset.range_mono (show d+1 ≤ R+1 from by omega))).symm
lemma strict_zero (ha:Fits l Λ a R): RateLE l Λ (fun i=> partialSum g R a i - a 0 i) (-(1/2:ℝ)):=by
    apply (RateLE.sum hz (S:=Finset.range (R+1)\ Finset.range (0+1)) (f:=fun k i=>(↑(g i^k):ℂ) • a k i) ?_).congr
    · refine Eventually.of_forall fun i=>?_ ; dsimp only; rw [← tear (Nat.zero_le _)]; unfold partialSum; simp
    intro k hk; simp only [Finset.mem_sdiff,Finset.mem_range, not_lt] at hk
    have ht:k ≥ 1:= hk.2; exact (scale hz hg (ha k (by omega)) k).mono (by have ht' := (Nat.one_le_cast.mpr ht : (1:ℝ) ≤ k); linarith)
lemma bill_later (ha:Fits l Λ a R)(hR:d≤ R): Wallet l Λ
    (fun i=> (((↑(g i ^(d+1)):ℂ))⁻¹) • (partialSum g R a i-partialSum g d a i)):=by
    let s:= Finset.range (R+1)\ Finset.range (d+1)
    have hg':Wallet l Λ g:= Wallet.of_strict hz (hg.pays hz) (by norm_num)
    apply (Wallet.sum hz (s:=s) (f:=fun k i=>(↑(g i^(k-(d+1))):ℂ) • a k i) ?_).congr
    · filter_upwards [hg.pos] with i hi; rw [tear hR,Finset.smul_sum]; apply Finset.sum_congr rfl; intro k hk
      unfold s at hk; have hh:= Nat.sub_add_cancel (not_lt.mp (mt Finset.mem_range.mpr (Finset.mem_sdiff.mp hk).2))
      simp_rw [smul_smul]; apply congr_arg (· • a k i); nth_rw 2 [←hh]; simp only [pow_add,Complex.ofReal_mul]; push_cast; field_simp [(Complex.ofReal_ne_zero.mpr hi.ne')]
    intro k hk
    exact ((hg'.pow hz (k-(d+1))).transfer (g:=fun i=>(↑(g i^(k-(d+1))):ℂ)) (Eventually.of_forall (fun _=> (Complex.norm_real _).le))).smul (ha k (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_sdiff.mp hk).1)))

lemma exactPrecision (h:Attached l Λ g Y a R χ)(hχ:χ < -((d:ℝ)+1)/2)(ha:Fits l Λ a R)(hR:d≤R): ∃ q:ℕ, ∀ᶠ i in l,
       ‖Y i-partialSum g d a i‖ ≤ g i^(d+1)* Λ i^q:=by
    have hg' := hg.power (d+1); have hs:= hg'.outweigh h (by push_cast; linarith) hz
    let z i:= (((↑(g i ^ (d+1)):ℂ))⁻¹) • (partialSum g R a i-partialSum g d a i)
    obtain ⟨q,hq⟩:= bill_later hz hg ha hR; refine ⟨q+1,?_⟩; filter_upwards [hq,hg.pos,hs,hz.eventually_ge_atTop 2] with i hq hg hs hH
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hg.le _), inv_mul_le_iff₀ (pow_pos hg _)] at hq
    apply (norm_sub_le_norm_sub_add_norm_sub _ (partialSum g R a i) _).trans ((add_le_add hs hq).trans ?_); rw [pow_succ (Λ i)]; let z:= g i^(d+1); have hz:0≤z:=pow_nonneg hg.le _
    calc _ ≤ (Λ i^q+1)*z:=by change z+ g i^ (d+1)*Λ i^q≤ _; unfold z; exact le_of_eq (by ring)
         _ ≤ _:=by rw [mul_comm]; apply mul_le_mul_of_nonneg_left _ hz; nlinarith only [one_le_pow₀ (one_le_two.trans hH) (n:=q), mul_le_mul_of_nonneg_left hH (pow_nonneg (zero_le_two.trans hH) q)]

-- Adapt from PertExtension/Series.lean's product tail (private there and for a different invoice)
omit hg hz in
private lemma convolution (i:ι)(R:ℕ)(A:ℕ→ι→V→L[ℂ] W)(a:ℕ→ι→V)(g:ι→ℝ):
    let S:= Finset.range (R+1) ×ˢ Finset.range (R+1)
    let K(p:ℕ×ℕ):= (↑(g i^(p.1+p.2)):ℂ) • A p.1 i (a p.2 i)
    (partialSum g R A i) (partialSum g R a i) - partialSum g R (action A a) i=
       ∑ p∈ S.filter (fun p=> R < p.1+p.2), K p := by
    intro S K; let T:= Finset.range (R+1); let U:= S.filter (fun (p:ℕ×ℕ)=>p.1+p.2 ≤ R)
    have h0: partialSum g R (action A a) i= ∑ p∈U,K p:= by
       have hh (i : ℕ×ℕ) (hi : i∈U) : i.1+i.2∈ T:= Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2)
       rw [← Finset.sum_fiberwise_of_maps_to hh K]
       apply Finset.sum_congr rfl; intro k hk
       unfold action; rw [Finset.smul_sum]; apply Finset.sum_congr ?sets; · intro p hp; unfold K; rw [(Finset.mem_filter.mp hp).2]
       ext j; simp only [Finset.mem_range] at hk; simp only [U,S,_root_.Finset.HasAntidiagonal.mem_antidiagonal,Finset.mem_filter,Finset.mem_product,Finset.mem_range];omega
    have h1: partialSum g R A i (partialSum g R a i) = ∑ p∈ S,K p:=by
       unfold partialSum S; rw [Finset.sum_product]; simp_rw [sum_apply,map_sum,map_smul,smul_apply,smul_smul]; unfold K; simp_rw [pow_add,Complex.ofReal_mul]; apply Finset.sum_congr rfl; intro y _; apply Finset.sum_congr rfl;intro x _; rw [mul_comm]; -- or closed
    rw [h1,h0]; apply sub_eq_iff_eq_add.mpr; rw [add_comm]; simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not S (fun p=> p.1+p.2 ≤ R) K).symm

lemma pulse (R:ℕ) (u:Fits l Λ a R)(v:Fits l Λ A R):
    Attached l Λ g (fun i=> partialSum g R A i (partialSum g R a i)) (action A a) R (-((R:ℝ)+1)/2):=by
    unfold Attached; simp_rw [convolution]; apply RateLE.sum hz; intro k hk
    obtain ⟨i,j⟩:= k; obtain ⟨⟨h,h'⟩,hQ⟩:=(show (i∈Finset.range _ ∧ j∈Finset.range (R+1))∧R < (i+j) from ⟨Finset.mem_product.mp (Finset.mem_filter.mp hk).1,(Finset.mem_filter.mp hk).2⟩)
    have hu : Wallet l Λ (fun v=> A i v (a j v)) := (v i (Nat.le_of_lt_succ (Finset.mem_range.mp h))).bind (u j (Nat.le_of_lt_succ (Finset.mem_range.mp h'))) (Eventually.of_forall (fun v=>(A i v).le_opNorm (a j v)))
    apply (scale hz hg hu (i+j)).mono
    push_cast; have hv:(R:ℝ)+1 ≤ (i+j:ℕ):= by exact_mod_cast (show R+1 ≤ i+j from hQ)
    push_cast at hv; linarith
lemma apply_advance {X:ι→ (V→L[ℂ] W)} (u:Attached l Λ g Y a R χ) (v:Attached l Λ g X A R χ) (hf:Fits l Λ A R)(hg':Fits l Λ a R) (hχ:-((R:ℝ)+1)/2 ≤ χ)(hχ':χ≤0): Attached l Λ g
     (fun i=> X i (Y i)) (action A a) R χ:=by
    have hu:= (single hz hg hg'|>.subpower hz); have hv:= (single hz hg hf|>.subpower hz)
    have hX:RateLE l Λ X 0:=(RateLE.add (RateLE.mono v hχ') hv hz).congr (Eventually.of_forall (fun i=> sub_add_cancel ..))
    have h1:RateLE l Λ (fun i=> X i (Y i - partialSum g R a i)) (0+χ):= hX.bil u (Eventually.of_forall (fun i=> (X i).le_opNorm (Y i-partialSum g R a i)))
    have h2:RateLE l Λ (fun i=>(X i-partialSum g R A i) (partialSum g R a i)) (χ+0):= RateLE.bil v hu (Eventually.of_forall (fun i=>(X i-partialSum g R A i).le_opNorm (partialSum g R a i)))
    unfold Attached; have he:RateLE _ _ _ _:= RateLE.mono (pulse hz hg R hg' hf) hχ
    rw [zero_add] at h1; rw [add_zero] at h2
    apply ((h1.add h2 hz).add he hz).congr; refine Eventually.of_forall fun i=>?_ ; dsimp only; rw [map_sub,_root_.sub_apply]; abel
end YM.RGComparison.Core16.Astage.Tape
