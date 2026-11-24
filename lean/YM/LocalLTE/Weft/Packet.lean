import YM.LocalLTE.Weft.Value
import YM.LocalLTE.Hall.Trim
/-!
Finite rendering of Laurent input polynomials, in root-frame width.
Uniform for ANY terms carrying this budget. Root metrics composition with other geometry.
No assumption that these coefficients fit an actual source/output push.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Mask Matter Coat Frond
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Fan Brush Foramen Pastel
variable {v z r W w s t y η γ B a κ: ℝ} {j n m N M : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open Weft AnalyticBridge.VerifiedReset FrameBox
local notation "E"=> Directions G c
variable {l :ℕ} {x:Site c}
-- Fin-k can account varying field powers, ALL inside a common grove.Needs not give $P^s(U)$ itself.Hex permits multiple actual stencils different proposals.
structure Weft.Scene (X:Grove x) (κ:ℝ)(l k n:ℕ)(f:ℝ→ Config G c→ℝ)(C:ℝ) : Prop where
    price : 0≤C
    weft : Hex k f
    plaque (s:ℝ)(hv:s∈ clip) : ∃ p:Cabana.Pkt (Directions G c) n, f s=FrameBox.realise X l κ p∧∀ i:Fin n, ‖s^(i.val:ℕ) • p i‖≤C
namespace Weft.Scene
variable {E':Type}[NormedAddCommGroup E'][NormedSpace ℝ E']
variable {X:Grove x} {P:BudgetPoint} {k m:ℕ} {ε Q:ℝ} {f:ℝ→ Config G c→ℝ}
def scoreBp (n k:ℕ)(V:ℝ) := (n:ℝ)*V^n*(1+(n:ℝ))^k
lemma glory (k':ℕ)(hk:Reliable G κ v)(H:Weft.Scene X (G:=G) κ l k n f Q) {g:E'→ Config G c} (hu:g 0=1) (w:BudgetPoint)
    (h:Brush k' B 1 ((X.crook l Chi.canonical κ)∘g) 0)(he:1≤B): Arp k k' (Q*scoreBp n k' B) (fun s=> f s∘g) :=by
    let g':= X.crook (G:=G) l Chi.canonical κ ∘ g; have hx:g' 0=0:=by unfold g'; rw [Function.comp_apply,hu,FrameBox.Hall.home _ _ hk w]
    refine ⟨Hex.invert (fun x=>H.weft.use _),fun s hs=> ?_⟩
    obtain ⟨p,hP,hC⟩:=H.plaque s hs
    let u(x:E'):= s⁻¹ • g' (s • x); have hf:= Arp.opening h hx hs
    have hh i: Brush k' (Q*B^n*(1+(n:ℝ))^k') 1 (Tensor.diagonal (s^(i:Fin n).val • p i) ∘ u) 0:=by
       refine ((Arp.stemB hf _ (s^i.val • p i)).trim).climb (?_) le_rfl
       have hz: 1+(i.val:ℝ)*1≤1+(n:ℝ):=by rw [mul_one]; exact add_le_add_right (Nat.cast_le.mpr i.isLt.le) _
       exact mul_le_mul (mul_le_mul (hC _) (pow_le_pow_right₀ he i.isLt.le) (pow_nonneg (zero_le_one.trans he) _) H.price) (pow_le_pow_left₀ (by positivity) hz _) (by positivity) (mul_nonneg H.price (pow_nonneg (zero_le_one.trans he) _))
    have he:= Brush.spree Finset.univ (fun i=>Tensor.diagonal (s^(i:Fin n).val • p i) ∘ u) _ (x:= (0:E')) zero_le_one (fun i _=> hh i)
    simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at he; refine (he.climb (le_of_eq (by unfold scoreBp; ring)) le_rfl).shimmy (Eventually.of_forall fun x=> ?_)
    rw [hP]; change Cabana.actual p (g' (s • x))=_; unfold Cabana.actual; rw [Finset.sum_apply]; apply sum_congr rfl; intro i _
    change Tensor.diagonal (p i) _= s^i.val • Tensor.diagonal (p i) (u x); rw [← Tensor.homogeneous (p i) _ s]; unfold u; rw [smul_inv_smul₀ hs.1.ne'] -- edit
lemma nearby {x':E'} {g:E'→ Config G c} (h₀:s∈clip)(hp: Weft.Scene X κ l k n f Q) (h:∀ᶠ y in 𝓝 x', Brush m B 1 ((X.crook l Chi.canonical κ)∘ g) y)(he:1≤B): ∀ᶠ y in 𝓝 x',Brush m (Q*scoreBp n m B/s^n) 1 (f s∘g) y := by
    obtain ⟨p,hP,hC⟩:=hp.plaque s h₀; rw [hP]
    let C:= X.crook l Chi.canonical κ ∘ g; filter_upwards [h] with i hi
    have he (k:Fin n): Brush m ((Q*B^n)*(1+(n:ℝ))^m /s^n) 1 (Tensor.diagonal (p k) ∘ C) i:= by
       apply ((Arp.stemB hi k.val (p k)).trim).climb (?_) le_rfl
       have ht:1+(k.val:ℝ)*1 ≤ 1+(n:ℝ):=by rw [mul_one]; exact add_le_add_right (Nat.cast_le.mpr k.isLt.le) _
       have hb : s^n * ‖p k‖ ≤ Q:=by apply le_trans (b:=‖s^(k.val:ℕ) • p k‖) _ (hC k); rw [norm_smul,Real.norm_of_nonneg (pow_nonneg h₀.1.le _)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h₀.1.le h₀.2 k.isLt.le) (norm_nonneg _)
       rw [le_div_iff₀ (pow_pos h₀.1 _)]; exact ((le_of_eq (by ring : _ = s^n* ‖p k‖ *B^k.val*(1+(k.val:ℝ)*1)^m))).trans (mul_le_mul (mul_le_mul hb (pow_le_pow_right₀ he k.isLt.le) (pow_nonneg (zero_le_one.trans he) _) hp.price) (pow_le_pow_left₀ (by positivity) ht _) (by positivity) (mul_nonneg hp.price (pow_nonneg (zero_le_one.trans he) _)))
    have H' := Brush.spree Finset.univ _ _ zero_le_one (fun i _=> he i); simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at H'
    exact (H'.climb (le_of_eq (by unfold scoreBp; ring)) le_rfl).shimmy (Eventually.of_forall fun x'=>by unfold FrameBox.realise Cabana.actual; dsimp only [Function.comp_apply]; rw [Finset.sum_apply]; rfl)
lemma beacon (s:ℝ)(h:s∈clip)(p: Weft.Scene X κ l k n f Q) (hp: Reliable G κ v) : Measurable (f s):=by
    obtain ⟨p,hP,-⟩:= p.plaque s h; rw [hP]; unfold FrameBox.realise; apply (Cabana.moves p ω|>.continuous.measurable.comp ?_) -- edit
    refine (X.shore l|>.continuous.measurable).comp (measurable_pi_lambda _ (fun i=> ?_)); exact (hp.borel _).comp (show Continuous (fun U:Config G c=> X.fix U i) by unfold Grove.fix Grove.uplink Lattice.gauge; fun_prop).measurable
end Weft.Scene
end YM.LocalLTE
