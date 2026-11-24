import YM.RG12.Rail.Dials
/-! Synchronizing lengths and charging all costs in physical rank stove. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Rail
open Function Filter Set Finset Lattice RG Wilson Next.Rank Next.Rank.Atlas Station Prayer Perch Glimmer Real
open scoped Topology BigOperators Classical
variable {G:Gauge}(Y:Levels G)(h:G.Simple) (b:ℝ)(hb:0 < b)
set_option quotPrecheck false
local notation "yK" k:max=> Y.clock.hatBeta k
local notation "pK" k:max=> Y.clock.monitor k
local notation "cost" x:max k:max=> bill x (yK k)
local notation "width" k:max=> ((Y.S.block k).val:ℝ)
abbrev σ₀ (n:ℕ):ℝ:= (16*n)⁻¹
abbrev cut₀ (n:ℕ):ℝ:=σ₀ n/4
def fineprint (Y:Levels G)(n k:ℕ):= bill (-cut₀ n) (Y.clock.hatBeta k)
lemma budged {k n:ℕ} : Ship.budget Y n k=cost (-σ₀ n) k:=by
  unfold σ₀ Ship.budget Ship.pot; rw [fire_bill]; unfold bill; rw [Real.log_exp,mul_one]; congr 1; rw [div_eq_mul_inv,← mul_neg]
-- lattice counts, scale map
abbrev knot (N:ℕ)(μ:ℝ):ℕ:= Nat.ceil (μ/N) -- if μ>0 and N>0 at least 1
def flareR (N i k:ℕ):ℝ:=Y.S.a k * (↑(i*N):ℝ)
def atR (N i k:ℕ):ℝ:=(mag Y b k)⁻¹ * (↑(i*N):ℝ)
def torchR (N k:ℕ):ℝ:= flareR Y N (knot N (mag Y b k)) k
def drift (N k:ℕ):ℝ:= atR Y b N (knot N (mag Y b k)) k

-- compare lay `dilation ≤ lamp/current` = use Y fine already scaled by drift
def bridge (k:ℕ):ℕ:=(Y.S.block k).val
def jumped (N i k:ℕ):ℝ:= atR Y b N (bridge Y k*i) (k+1)
lemma hooked (N i k:ℕ) : flareR Y N (bridge Y k*i) (k+1)=flareR Y N i k:=by rw [flareR, Y.S.a_step]; unfold flareR bridge; push_cast; field_simp [(show (width k)≠0 from by positivity [le_of_lt (zero_lt_one.trans (lt_of_lt_of_le (by norm_num) (width_three Y k)))])]
lemma jumped_at (N i k:ℕ): jumped Y b N i k=(width k)*atR Y b N i k / (mag Y b (k+1)/mag Y b k):=by unfold jumped atR bridge; push_cast; field_simp [(mag_pos Y b k).ne']
lemma pint {k N:ℕ}(_hN:0<N): drift Y b N k= Arche.Shapes.ratio N (mag Y b k):=by unfold drift knot atR Arche.Shapes.ratio Arche.Shapes.ticks; push_cast; ring
lemma drift_pos (N:ℕ)(hn:0 < N) (k:ℕ):0 < drift Y b N k:= by rw [pint Y b hn]; exact zero_lt_one.trans_le (Arche.Shapes.ticketed N (mag Y b k) (mag_pos ..) hn).1
lemma flare_pos (N:ℕ)(hn:0 < N) (k:ℕ):0 < torchR Y b N k:=by
   have hV:= drift_pos Y b N hn k
   unfold torchR flareR; apply mul_pos (Y.S.a_pos k) (pos_of_mul_pos_right hV (inv_pos.mpr (mag_pos ..)).le)
include h hb
lemma tour_clock (hs:Slugg Y)(N:ℕ)(hN:0 < N)(n d:ℕ)(hn:2 ≤ n):
  ∀ᶠ i in atTop,
    let x:=drift Y b N i; let z:=jumped Y b N (knot N (mag Y b i)) i
    x∈Icc 1 (pK i) ∧ z∈Icc 2 (pK (i+1)) ∧
    x^(2*d) ≤ cost (cut₀ n) i ∧ z^(2*d) ≤ cost (cut₀ n) (i+1) ∧ drift Y b N (i+1) ≤ 2 := by
   let δ:=cut₀ n; let e:=δ/(4*d+10); have hd:0<δ:=by unfold δ cut₀ σ₀; have hi:0<(n:ℝ):=(by exact_mod_cast (lt_of_lt_of_le (by decide) hn:(0:ℕ)<n)); positivity
   have he:0<e := by unfold e;positivity
   have hk : δ ≤ 1:=by unfold δ cut₀ σ₀; have hx : (16*(n:ℝ))⁻¹ ≤ 1:= inv_le_one_of_one_le₀ (by have hf:2≤(n:ℝ):= (by exact_mod_cast hn); linarith); linarith
   let μ:=mag Y b
   have hV(i):1 ≤ drift Y b N i:=by rw [pint Y b hN]; exact (Arche.Shapes.ticketed N _ (mag_pos ..) hN).1
   have hj : ∀ᶠ i in atTop, drift Y b N i ≤ 2:=by
      filter_upwards [(mag_rate Y h hb).eventually_ge_atTop (N:ℝ)] with i hi
      rw [pint Y b hN]; have H:= (Arche.Shapes.ticketed N (μ i) (mag_pos ..) hN).2; linarith only [H,(div_le_one (show 0<μ i from mag_pos ..)).mpr hi]
   filter_upwards [hj,(tendsto_add_atTop_nat 1).eventually hj,bill_mono Y h hd.le, hs e he, -- fix bill_lo
     ((bill_lo he).comp (hat_rate Y h)).eventually_ge_atTop 4,bill_mono Y h hb.le,bill_mono Y h he.le,(neighboring Y h hs b hb).eventually (ge_mem_nhds (show (1:ℝ)<3/2 by norm_num))] with i h1 hT hx h2 hB h3 hG h4
   intro x z
   have ha := mag_pos Y b i; have hζ:=mag_pos Y b (i+1)
   have hm :1 ≤ μ (i+1)/μ i:=by rw [one_le_div ha]; change mag _ _ _ ≤ mag _ _ _; simp only [mag_bill]; exact h3
   have hU := width_three Y i
   have hZ:z*(μ (i+1)/μ i)=width i*x:=by rw [show z=_ from jumped_at ..]; rw [div_mul_cancel₀ _ (div_pos hζ ha).ne'];rfl
   have hz: z ≥ 2:=by
       rw [show z=_ from jumped_at ..,ge_iff_le,le_div_iff₀ (div_pos hζ ha)]; change 2*(μ (i+1)/μ i) ≤ (width i)*x; change μ (i+1)/μ i ≤ _ at h4; have ht:1 ≤ x:=hV i; nlinarith
   let M':=cost e i; have hp:1≤M':=by linarith only [show 4≤ M' from hB]
   change 4 ≤ M' at hB
   have ht:z ≤ M'^2:=by
      have h : z≤(width i)*x:= (le_mul_of_one_le_right (zero_le_two.trans hz) hm).trans_eq hZ
      exact h.trans (by rw [sq]; exact mul_le_mul h2 (show x ≤ M' from h1.trans (show 2 ≤ M' by linarith only [hB])) (zero_le_one.trans (hV i)) (zero_le_one.trans hp))
   have hv : e*(2*(max 1 (2*(d:ℝ)))) ≤ δ :=by
       unfold e; rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]; rcases le_total (2*(d:ℝ)) 1 with h₁|h₁
       · rw [max_eq_left h₁]; nlinarith [Nat.cast_nonneg (α:=ℝ) d]
       rw [max_eq_right h₁]; nlinarith
   have hw(k:ℕ)(hc:(k:ℝ) ≤ max 1 (2*(d:ℝ))): M'^(2*k) ≤ cost δ i:=by
      unfold M'; rw [bills]; apply billed; push_cast; nlinarith only [he,hv,hc, mul_le_mul_of_nonneg_left hc he.le]
   have hm₁:M'^2 ≤ cost δ i:=hw 1 (by rw [Nat.cast_one];exact le_max_left ..)
   have hm₂:(M'^2)^(2*d) ≤ cost δ i:= by rw [← pow_mul]; exact hw _ (by exact_mod_cast (show ((2*d:ℕ):ℝ)≤ max 1 (2*(d:ℝ)) by push_cast; exact le_max_right ..))
   have h₀: cost δ i≤pK i:=by rw [fire_bill]; exact billed _ hk
   have hy : M'^2 ≤ pK (i+1):= by rw [fire_bill]; exact (hm₁.trans hx).trans (billed _ hk)
   have htx:x ≤ M'^2:= h1.trans ((show 2≤M' by linarith only [hB]).trans (le_self_pow₀ hp (by norm_num)))
   exact ⟨⟨hV i,htx.trans (hm₁.trans h₀)⟩,⟨hz,ht.trans hy⟩,(pow_le_pow_left₀ (zero_le_one.trans (hV i)) htx _).trans hm₂,(pow_le_pow_left₀ (zero_le_two.trans hz) ht _).trans (hm₂.trans hx),hT⟩
end YM.RG12.Rail
