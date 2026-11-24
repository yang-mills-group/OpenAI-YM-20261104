import YM.FormalOPE.RG10.Capture.Inlet

/-!
# Explicit unread generator lease for far argument

`Tariff` is where the single-mark stability assumption at *fine/soft* overlap and support
interpretation sit (uses LIFTS in a declared `pov`, not all tensors in root-varying frames). The
units/conventions correspond on choosing e.g. finite approximant to cover-with-rooted test
preimages and with the arrow ratios of `Scale` (i finer step). Needs a period/halo adapter from
unwrapped estimates if those are all one has! No assertion intersection of those properties.
Uniform
through the chosen `b`, impulse envelope support for test-address through `n` & differential list
specified via S and its park, cost polynomial in Y from far test scale. No assumption on joined
expressions. In particular the lift owner must construct the cylinder, justify projected vectors
are in the intended physical full alphabet and choose the **appropriate special subspace** (e.g.,
invariant proof-carrying germs and their legitimate radius translations with lifted moments
of the finite demand). Don't choose a new frame based on the residual or assert invariance recovered
by canceling torus windings. This Budget is phrased so the precursor *bound* uses a tested
presentation directly (`Fits`) rather than arbitrarily suppressing columns. This version
needs a solution of a seam issue, if working with any *finite period* estimate of ordinary
bulk: stability estimate must be proved on this space with the declared `Fits` seminorm (torus
cost & for all declared views), while keeping lifts; if seminorm doesn't control extra wrapping
path data needed for the propagated norm, need an lift-sensitive deposit. E.g. discharge `Loan` instead using an extra account
explicitly on the paid-for presentation, and Matron compensation theorem (norm on lift).


`Install` in `Costume` accepts a `Loan` at the declared lift with a proved input
Fit fee. A stronger `Tariff` supplies this input through `Tariff.lends`.
Matron also gives the required bound on the lift. The installer returns the
single-kernel outputs with the stated capture and test norms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Function Finset MeasureTheory Filter Route Transit Weave Cylinder
open scoped Topology BigOperators Classical
variable {X : Type} {U T J : ℕ → Type} {K:ℕ→Type*} {ι α β A A': Type*}
    [∀ i,AddCommGroup (K i)] [∀ i,Module Series (K i)]
    {W : Scale X U} [∀ i,Fintype (T i)] {Z : Cylinder T U K α ι}
    {b i k h s N : ℕ}
local notation "Γ" => ι→ Series
section currency
lemma coupon_not (B I : ℕ) (_x:K B) (q:K I) (φ:α): nominal ((W.μ B/W.μ k)^h) • restore W h Z φ k I q=restore W h Z φ B I q := by
  unfold restore fingerprint; dsimp only [LinearMap.comp_apply,LinearMap.coe_mk,AddHom.coe_mk]; rw [smul_smul];
  have hk:= W.positive k; have hb:=W.positive B; have hI:=W.positive I
  rw [price,price,← product_nom]; congr 1; congr 1; simp_rw [div_pow]; field_simp
omit [∀ i,Fintype (T i)] in
lemma roll_r (hz : s ≤ b) (hj : b ≤ k) (hk:k ≤ N) (x:K b) :
    (Z.roll k N).symm (report W h Z x s k) = nominal ((W.μ b/W.μ k)^h) • (Z.roll b N).symm (designated Z x s) := by
  rw [report,map_smul]; congr 1; apply (Z.roll s N).injective; rw [Z.rollNow (hz.trans hj) hk,Z.rollNow hz (hj.trans hk)] -- inspect
  simp [designated]
lemma shiny (x : K b) (φ:α) (hs:s ≤ b) (hk:b ≤ k) (hN:k ≤ N) : coupon W h Z φ k N (report W h Z x s k)= coupon W h Z φ b N (designated Z x s) := by
   unfold coupon; rw [roll_r hs hk hN x,map_smul, map_smul,coupon_not b N x]
variable (Z) [Fintype ι]
def scaleC (r : ℕ) (v : ι → Series) := ∑ i,∑ j∈range (r+1), ‖coeff j (v i)‖
lemma scaleC_nn (r:ℕ)(v:Γ): 0≤ scaleC r v := sum_nonneg fun _ _=> sum_nonneg fun _ _ => norm_nonneg _
lemma scaleC_sub (r : ℕ) (v w:Γ) : scaleC r (v-w) ≤ scaleC r v+scaleC r w := by
  unfold scaleC; rw [← sum_add_distrib]; apply sum_le_sum; intro i _; rw [← sum_add_distrib];
  apply sum_le_sum; intro j _; simp only [Pi.sub_apply,map_sub]; exact norm_sub_le ..
end currency
variable [MeasurableSpace X] [∀ i,Fintype (J i)]
    (S : Locale T X α β)
variable [Fintype ι] {Q : Voyage U J} {F : Fibers T} (pov : Submodule Series (K b))
    (L : ℝ)

/-- Single-mark startup. Use order r chosen; moment support n for projection and cap price.
Needs the actual stencil interpretation in S and `Z` for the estimate to apply at stated position
support. Including younger-lane price because bare columns are in the far comparison normalized
at different scale than b. Marker estimates before capture are separate. -/
structure Tariff (W : Scale X U) (Z : Cylinder T U K α ι) (S : Locale T X α β) (b s t N : ℕ) (r n : ℕ)
    (C : ℝ) (ξ : ℝ) (δ : ℕ) (pov : Submodule Series (K b)) : Prop where
  title : ∀ v,Z.column b v∈pov
  projection : ∀ u∈ pov, ∀ L≥ (0:ℝ), Fits W S b (Z.prints b u) n r L→ scaleC r (Z.probe b u) ≤ (W.Y C (W.μ t) b)^δ * L
  terminal : ∀ u∈ pov, ∀ L≥ (0:ℝ), Fits W S b (Z.prints b u) n r L→ ∀ i∈Icc t b,
     Fits W S i (Z.prints i (Z.spin i b (u-Z.column b (Z.designated u s)))) n r ((W.Y C (W.μ t) b)^δ * L * W.fade ξ b i)
  seed : ∀ v,∀ i∈ Icc b N, Fits W S i (Z.prints i (Z.column i ((Z.roll b i).symm v))) n r ((W.Y C (W.μ t) i)^δ * scaleC r v)

/-- Only charge for this specified lift & at specified input budget `L` (not all proofs or budgets).
 A primitive producer may work with *more data* in its priced kernel lift space & certify input
 `capital ≤ Y^q * L` on precisely this M (from grown representation and ITS size), then derive
 these projection/end/seed prices. No mis-inferring the lift cost by cancellation on a move between
 charts or periodisation. Fits certifies material cost used in OLD Tile units before pricing; e.g.
 for more faithful kernel entries this can turn into that capital charge, via proved comparison,
 or if working with more data it **needn't** supply that charge on THIS lift. The antecedent cost
 is proved from independent receipts; not a conclusion storing the far bound, nor an exit estimate
 on mixed contraction assumed for all time. See the Matron adapter using single-step graded prices.
 Note that this inserts inputs `∈pov`, `0≤L`, `Fits...L` so later consumers using Loan require
 these proofs even if (for their specific stronger capital assertion) some irrelevant to pricing. -/
structure Loan (W : Scale X U) (Z : Cylinder T U K α ι) (S : Locale T X α β)
    (b s t N r n : ℕ) (C ξ : ℝ) (δ : ℕ) (pov : Submodule Series (K b)) (M : K b) (L : ℝ) : Prop where
  extent : M ∈ pov → 0 ≤ L → Fits W S b (Z.prints b M) n r L → scaleC r (designated Z M s) ≤ (W.Y C (W.μ t) b)^(δ+δ+1)*L
  terminal : M ∈ pov → 0 ≤ L → Fits W S b (Z.prints b M) n r L → ∀ i∈Icc t b,
    Fits W S i (Z.prints i (Z.spin i b (M-Z.column b (Z.designated M s)))) n r ((W.Y C (W.μ t) b)^δ * L * W.fade ξ b i)
  seed : ∀ v,∀ i∈ Icc b N,Fits W S i (Z.prints i (Z.column i ((Z.roll b i).symm v))) n r ((W.Y C (W.μ t) i)^δ * scaleC r v)

local notation "μ" => W.μ
variable {S L pov} {C₀ ξ:ℝ} {r n δ t : ℕ} (c : Tariff W Z S b s t N r n C₀ ξ δ pov)
local notation "Y" => W.Y C₀ (W.μ t) -- later position
variable {v : K b} (hv : v ∈ pov) (hh : Fits W S b (Z.prints b v) n r L)
include c hv hh in
lemma Tariff.income (he:s ≤ b) (ht:t ≤ b) (hN:b ≤ N) (H : Reading F Q W h s N Z) (hL:0≤L) (hC : 2 ≤ C₀) :
    scaleC r (designated Z v s) ≤ Y b ^ (δ+δ+1) * L := by
  have h1 : 0 < μ b:= W.positive b; have hy : 2 ≤ Y b:= W.rich (μ t) C₀ (le_refl (μ t)) hC ht
  have hX : 1 ≤ Y b:=by linarith
  have h0:= zero_le_one.trans hX
  let w:=designated Z v s; let z:= v - Z.column b w
  have he' : Z.probe b v-Z.probe b z=w:= by unfold z; rw [map_sub,H.measures _ (mem_Icc.mpr ⟨he,hN⟩),sub_sub_cancel]
  have hz : Fits W S b (Z.prints b z) n r (Y b^δ*L) := by
    have ht':= c.terminal v hv L hL hh b (mem_Icc.mpr ⟨ht,le_rfl⟩); simpa [Scale.fade,z,w] using ht'
  change scaleC r w ≤ _; rw [← he'];
  apply (scaleC_sub r _ _).trans; apply (add_le_add (c.projection _ hv L hL hh) (c.projection _ (pov.sub_mem hv (c.title _)) _ (by positivity) hz)).trans
  rw [pow_add,pow_add, pow_one]; rw [← mul_assoc _ _ L, ← add_mul]; exact mul_le_mul_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_right hy (sq_nonneg (Y b ^ δ)),one_le_pow₀ (n:=δ) hX]) hL
include c
/-- Adapter from previous cp through 19; replacement for Tariff in Install. -/
theorem Tariff.lends (he:s ≤ b) (ht:t ≤ b) (hN:b ≤ N) (H : Reading F Q W h s N Z) (hC : 2 ≤ C₀) : Loan W Z S b s t N r n C₀ ξ δ pov v L :=
  ⟨fun hv hL hh=> c.income hv hh he ht hN H hL hC,fun hv hL=> c.terminal v hv L hL, c.seed⟩
end YM.FormalOPE.RG10.Capture
