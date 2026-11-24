import YM.Juniper.Orrery.Hemispheres
import YM.Juniper.LocalAtlas.Law
/-!
 # Tilted scenery, coordinate scaling costs

 Keep pure and mixed charges visible IN SAME normalization convention as
 Juniper.LocalAtlas's unmarked pure version. Includes all bonds of normalization before taking log
 in a single Gaussian oracle. Tensor order n! as always. Later identifying
 even the assignment's coefficient convention still required, including
 switching Laurent ranks in Tilted (uses full post epoch clipping depending
 on θ, not choosing Φ by formal minimum), cutoff regression, and born.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open MeasureTheory Set Function Matrix Metric Filter ProbabilityTheory
open PhysicalNext.Repeat Lantern RG Wilson
open ConnectedActivityE6 Blaze Brush Poll Sienna
open Work.G05 WilsonStartup Analysis Tensor
open LocalAtlas
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {E F : Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
section scale
variable (s:ℝ)(f:E→F)(i:ℕ)
def std (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (s:ℝ) := s • ContinuousLinearMap.id ℝ E
local notation "A"=> std E s
lemma atBase (x:E) : std E s x = s • x:= rfl
lemma dim (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E] (s:ℝ) : ‖std E s‖≤ |s| := by unfold std; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg s) ContinuousLinearMap.norm_id_le
lemma coeff_scale (h : ContDiffAt ℝ (i:ℕ∞ω) f 0) : Tensor.coeff (f ∘ std E s) i 0 = s^i • Tensor.coeff f i 0:= by
    have he := Lantern.shift_affine (f:=f) 0 0 (A) i (by rw [map_zero,add_zero]; exact h); simp only [map_zero,zero_add] at he
    ext1 z; unfold Tensor.coeff; change (i.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ i (fun x:E=> f (A x)) 0 z) = s^i • ((i.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ i f 0 z)); rw [he,ContinuousMultilinearMap.compContinuousLinearMap_apply]; -- all inputs scalar
    let b:= iteratedFDeriv ℝ i f 0; rw [show (fun i=>A (z i))=(fun i=>s • z i) from rfl] -- fn expression comp?
    rw [ContinuousMultilinearMap.map_smul_univ]; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact smul_comm _ _ _
def scaledP (q:PacketSeries E F)(s:ℝ) : PacketSeries E F:=fun i=> s^i • q i
lemma through_scale {a q:PacketSeries E F}(h:∀ j ≤ i, a j=scaledP q s j): through i a= (through i q) ∘ (std E s):= by
    funext x; simp only [through,Function.comp_apply,Finset.sum_apply]; apply Finset.sum_congr rfl; intro j hj; rw [h j (by rw [Finset.mem_range] at hj; omega),atBase, Tensor.homogeneous]
    rfl
lemma block_scaled (h:ContDiffAt ℝ (i:ℕ∞ω) f 0): blockTaylor i (f ∘ std E s) = (blockTaylor i f) ∘ (std E s):= through_scale s i fun j hj=> coeff_scale s f j (h.of_le (Nat.cast_le.mpr hj)) -- simp Nat.cast
end scale
section cut
variable {X : Type} [MeasurableSpace X] (μ : Measure X) (D : Set X)(s:ℝ)(f:E→ℝ) (g: X→ E→ℝ)
-- build standard estimate in scaled/unscaled variables
local notation "τ"=> std E s
-- definitions not assuming q positive; use log at cut
noncomputable def full (n:ℕ) : Tensor.T E ℝ n := ∫ z, Tensor.coeff (Real.exp ∘ g z) n 0 ∂μ
noncomputable def cut (x:E) := ∫ z, D.indicator (fun z=> Real.exp (g z x)) z ∂μ
noncomputable def gauge (i:ℕ) := through i (full μ g) -- ambiguous with Lattice.gauge; refer
noncomputable def sampleLog := Real.log ∘ cut μ D g
noncomputable def clean (i:ℕ):= blockTaylor i (Real.log ∘ through i (full μ g))
abbrev foldR (g:X→ E→ℝ)(s:ℝ) : X→ E→ℝ:=fun z=> g z ∘ std E s
local notation "g'"=> foldR g s
local notation "P"=> Mulberry.gauge
variable (i:ℕ)
lemma cut_scale : cut μ D g' = cut μ D g ∘ std E s:=rfl
lemma sample_scale : sampleLog μ D g'= sampleLog μ D g ∘ std E s:=rfl
lemma scaled (h : ∀ z: X, ContDiffAt ℝ (i:ℕ∞ω) (g z) 0): full μ g' i=s^i • full μ g i:=by
    unfold full; rw [← integral_smul]; exact integral_congr_ae (Eventually.of_forall fun x=> coeff_scale s (Real.exp ∘ g x) i (h x|>.exp))
lemma tastable (h: ∀ z:X, ContDiffAt ℝ (i:ℕ∞ω) (g z) 0) : P μ g' i = P μ g i ∘ std E s:= through_scale s i fun j hj=> scaled μ s g j (fun z=> (h z).of_le (Nat.cast_le.mpr hj)) -- args

-- Need constant q(g_z at flat)=0. Normalizes full coefficient zeroth moment. Caps & gaussian ensure regular. No still-on-cut assumption.
variable (h : ∀ z:X,g z 0=0)[IsProbabilityMeasure μ]
include h
lemma nulls : full μ g 0=Tensor.coeff (fun _ : E=> (1:ℝ)) 0 0 := by
    have he z : Tensor.coeff (Real.exp ∘ g z) 0 0= Tensor.coeff (fun _ : E=> (1:ℝ)) 0 0 := by
       ext; simp only [Tensor.coeff, _root_.smul_apply, iteratedFDeriv_zero_apply, Function.comp_apply, h,Real.exp_zero]
    unfold full; simp_rw [he]; simp
lemma clearVal : P μ g i 0=1 := by
   unfold Mulberry.gauge; rw [LocalAtlas.home,nulls μ g h]; exact Tensor.coeff_apply_zero ..
lemma clearLog (hs:∀ z:X, ContDiffAt ℝ (i:ℕ∞ω) (g z) 0) : clean μ g' i = clean μ g i ∘ std E s := by
    have he : ContDiffAt ℝ (i:ℕ∞ω) (Real.log ∘ through i (full μ g)) 0 := (LocalAtlas.t_smooth (n:=i) (full μ g)|>.of_le le_top|>.contDiffAt).log (show through i (full μ g) 0 ≠ 0 from by change Mulberry.gauge μ g i 0 ≠ 0; rw [clearVal μ g i h]; exact one_ne_zero)
    unfold clean; rw [show through i (full μ g')= _ from tastable μ s g i hs]; exact block_scaled s (Real.log ∘ through i (full μ g)) i he
end cut
section currency
variable (h:E→F){j:ℕ}{a b u s t p:ℝ} {x:E}
local notation "S"=> std E s
local notation "u'"=> std E (s⁻¹)
lemma rewind (hp:Brush j a b (h ∘ std E s) x)(hs:0<s) : Brush j a (b*s⁻¹) h (S x) := by
   have he(y:E): S (u' y)= y:= smul_inv_smul₀ hs.ne' y; have ht:u' (S x) = x := inv_smul_smul₀ hs.ne' _; apply (Brush.reading u' (?_ : Brush j a b (h ∘ S) (u' (S x))) ((dim ..).trans_eq (abs_of_pos (inv_pos.mpr hs)))).shimmy; exact Eventually.of_forall fun y=> congr_arg h (he y|>.symm); rw [ht]; exact hp
-- coordinate map for all brush and pF conversion y horizon.
lemma rewind_full (hv : Brush j a b (h ∘ std E s) (u' x))(hs:0<s) : Brush j a (b/s) h x:= by
   rw [div_eq_mul_inv]; exact (show S (u' x)= x from smul_inv_smul₀ hs.ne' _) ▸ Mulberry.rewind h hv hs
lemma leading (hs:0<s)(hv:s ≤ 1) (h₀:Brush j a b h (std E s x)) : Brush j a b (h∘ std E s) x:= (Brush.reading (std E s) h₀ ((Mulberry.dim E s).trans_eq (abs_of_pos hs))).climb le_rfl (mul_le_of_le_one_right h₀.pos hv)
lemma reel (hp: Brush j a b (h ∘ std E s) x) (hs:s≠0) : ContDiffAt ℝ (j:ℕ∞ω) h (std E s x):= by
    let T:= std E s; let L := std E s⁻¹; have he : ((h ∘ T) ∘ L)=h:= funext fun y=> congr_arg h (smul_inv_smul₀ hs y); have hh:L (T x)= x:= inv_smul_smul₀ hs _; exact he ▸ (ContDiffAt.comp (f:=L) (g:=(h ∘ T)) (T x) (hh.symm ▸ hp.smooth) L.contDiff.contDiffAt)
end currency
end YM.Juniper.Mulberry
