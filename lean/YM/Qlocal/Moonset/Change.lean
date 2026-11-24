import YM.Qlocal.Moonset.Costume
import YM.Qlocal.Moonset.Sundown
/-!
Insert the post-forecast pricing correction for coupling on the same representation already
counting the true seed penalties and all re-expression masks. Retains all histories separately at
the receiving support exponent. Here use REAL analytic amplitudes. Complex rectilinear total &
inherited discrepancies unchanged (and re-expression equalities hold in the native Poly).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern
open AllOrder AllOrder.Floe AllOrder.Floe.Pace
open Reckoner
variable {V Ω J J' J₀ K α:Type}[DecidableEq V][Fintype V]{R:Marker.Census V}{G:Gauge}
variable {n:Side} {g:V→ℕ}{p M:ℕ}{a b C B v r t w δ:ℝ} {o: V→Site n}
open Dialect Patchwork Quipu.Eluder.Incline.Bookworm
namespace Adjustment
variable (Y:Ω→ Stanza R G g p)
-- only the prescribed momentum cutoff is advertised, including rank zero
noncomputable abbrev lettering (Y: Stanza R G g p) (P:BudgetPoint)(w N:ℕ)(s:Senses R)(o:V→ Site n)(h z:ℝ): Config G n→ℂ := Patchwork.substantive z w (Stanza.son Y N) (Anthem.statement (Stanza.son Y N)) P o s h
lemma registry (Y:Stanza R G g p) (o:V→Site n)(w N:ℕ): Tale.short (Stanza.son Y N) (Anthem.statement (Stanza.son Y N)) w=Stack.selector (Stanza.son Y N) (fun i=>i  ≤  w):= by
 funext s i k m; apply propext; exact ⟨fun h=> h.2, fun h=> ⟨trivial,h⟩⟩
lemma connected (Y: Stanza R G g p)(P:BudgetPoint)(o:V→Site n)(w N:ℕ)(t:Senses R)(h z:ℝ)(x:Config G n) :
    masked P.threshold (Tale.court P.B (o (Sonnet.root t))) (Complex.ofReal ∘ (h •immediate Y t o w N z)) x= lettering Y P w N t o h z x:= by
 unfold lettering Patchwork.substantive; rw [registry _ o]; by_cases hv:Healthy P.threshold (Tale.court P.B (o (Sonnet.root t))) x
 · rw [masked_eq _ _ _ _ hv]; simp only [Function.comp_apply,Pi.smul_apply]; rw [masked_eq _ _ _ _ hv]; rfl
 rw [masked_ne _ _ _ _ hv]; simp only [Function.comp_apply,Pi.smul_apply,masked_ne _ _ _ _ hv,smul_zero,Complex.ofReal_zero]

variable (X:RG.Rep G n) (s:V→Support n)(o:V→Site n)(w N:ℕ) (f:Senses R→ℝ)
    (q: Coin) (q₀:q 0=0) (z zp:ℝ) (T : Ray R) (ht:Rental T)
noncomputable def deltaSheet (P:BudgetPoint): Scribe Ω (Senses R) G n R where
  tag i:= i.val
  region i := Tale.court P.B (o (Sonnet.root i))
  total _:= False
  score x i := Complex.ofReal ∘ (f i • (immediate (toParent q (Y x)) i o w N zp - immediate (Y x) i o w N z))
set_option quotPrecheck false
local notation "F" => deltaSheet Y o w N f q z zp X.p
open Scribe
include X
lemma identity_p (U:Config G n)(x:Ω)(i:Senses R) : ((F).send X.p x U).part i.val= lettering (toParent q (Y x)) X.p w N i o (f i) zp U-lettering (Y x) X.p w N i o (f i) z U:= by
 unfold send; rw [tsum_fintype, Poly.part_sum, Finset.sum_eq_single i]
 · unfold enters render; rw [if_neg (show ¬(F).total i from id), Poly.part_send, if_pos (show i.val=(F).tag i from rfl),← connected, ← connected]; let H:=Tale.court X.p.B (o (Sonnet.root i)); rw [show ((F).region i) = H from rfl]; by_cases ht:Healthy X.p.threshold H U
   · rw [masked_eq _ _ _ _ ht, masked_eq _ _ _ _ ht, masked_eq _ _ _ _ ht]; simp only [deltaSheet,Function.comp_apply,Pi.smul_apply,Pi.sub_apply]; rw [smul_sub, Complex.ofReal_sub]
   rw [masked_ne _ _ _ _ ht, masked_ne _ _ _ _ ht, masked_ne _ _ _ _ ht]; simp
 · intro a h he; unfold enters; rw [Poly.part_send, if_neg (show ¬ i.val=(F).tag a from fun H=> he (Subtype.ext H.symm))]
 simp

variable (he:∀ i,s i⊆ Tale.court (X.p.B-w) (o i)) (hb:w  ≤  X.p.B)
local notation "φ"=>X.p.threshold
local notation "Θ" x=>Tale.court X.p.B (o (Sonnet.root x))
variable (hf:∀ i,0 ≤ f i)(hz:0<z)(hz':0<zp)
    (d a:ℝ)(hd:d/X.p.B  ≤  a)(h0:0  ≤  d)(ha:0<a)
    (hY:∀ x,(Stanza.son (Y x) N).Allows (2*a) 1)
variable (L K:ℕ)(hR: ∀ r:Senses R,Lagger.dues g r.val  ≤  L)
noncomputable abbrev life (X:RG.Rep G n)(k p L:ℕ)(z zp d a:ℝ)(q:Coin):ℝ:= rent_gap (G:=G) X.p p k L z zp (price_ops (Moonset.raise q) p (p+L) 1) d a q
local notation "T!"=> life X N p L z zp d a q
local notation "E" i=> Real.exp (-(d*coverNumber X.p.B (Θ i)))
include hd ha h0 he hR hY q₀ hz hz' hb hf
protected lemma patch (i:Senses R)(x:Ω):
    let u(x:Ω):= f i • (immediate (toParent q (Y x)) i o w N zp-immediate (Y x) i o w N z)
    PayR X.p (Tale.court X.p.B (o (Sonnet.root i))) (f i*(T! *E i)) (u x) := by
 intro u; rw [show f i=|f i| from (abs_of_nonneg (hf i)).symm]; apply PayR.z_m (u:=f i) -- argument order?
 exact Moonset.responsible (Y x) i o N X.p d hb q q₀ z hz zp hz' ha hd h0 ha.le ((two_mul a) ▸ hY x) L hR
lemma poseC : Scribe.Proper (F) X.p s:= by
 refine ⟨fun i=>⟨o (Sonnet.root i), (Lattice.halo_subset ..) (mem_singleton_self _)⟩, fun x i=> Blush.ornate (Adjustment.patch Y X s o w N f q q₀ z zp he hb hf hz hz' d a hd h0 ha hY L hR i x).genuine, ?_, ?_, fun _ _ _ h=>h.elim⟩
 · intro i j x U h; apply Tale.vestments X.p i o (by apply Classical.byContradiction; intro hV; apply h; unfold deltaSheet immediate record; dsimp only; rw [← registry _ o,← registry _ o,Tale.evacuated i _ _ o hV,Tale.evacuated i _ _ o hV]; simp) (fun i _=>he i) hb j
 intro i h; exact False.elim (i.prop.ne_empty (show i.val.val=∅ from congr_arg (Subtype.val) h)) -- infer bad
local notation "κ"=> Fintype.card (Senses R)
omit hd ha h0 he hR hY q₀ hz hz' hb hf in
lemma vital (ha:0<a): 0 ≤  life X N p L z zp d a q:= by unfold life rent_gap; exact sum_nonneg (fun i _=> sum_nonneg fun j _=> mul_nonneg (abs_nonneg _) (Moonset.toll_positive _ _ _ (Moonset.nonneg_price _ zero_le_one _ _) ha))
variable (hw:Fintype.card (Senses R) ≤  K)(hU:∀ i:Senses R,T i.val * f i  ≤  C)(hC:0 ≤ C)
include ht hw hU hC
lemma stars : Spend (F) X.p T d (K*(C*(life X N p L z zp d a q))):=by
 let r i:= f i*(T! * E i); have hp:= vital X N q z zp d a L ha (p:=p); -- arity
 have hr i:0 ≤  r i:= mul_nonneg (hf i) (mul_nonneg hp (Real.exp_nonneg _)); refine ⟨r, ⟨hr,fun x i j hj=>?_⟩,fun i=> ?_⟩
 · let h:= Adjustment.patch Y X s o w N f q q₀ z zp he hb hf hz hz' d a hd h0 ha hY L hR i x; exact Blush.pricingG h.genuine (h.statement j hj)
 refine budget_finite (fun j=>?_) ?_
 · split; exact mul_nonneg (mul_nonneg (ht.pos _).le (hr _)) (Real.exp_nonneg _); exact le_rfl
 refine le_trans (b:=∑ _ : Senses R,C*T!) (sum_le_sum ?_) (by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hw) (mul_nonneg hC hp))
 intro j _; split; next hz=>
    change T j.val* (f j*(T! * E j))* Real.exp _  ≤  _; refine le_trans (Eq.le (b:=T j.val*f j*T!) ?_) (mul_le_mul_of_nonneg_right (hU j) hp); rw [mul_assoc, mul_assoc, mul_assoc, ← Real.exp_add, show -(d*↑(coverNumber X.p.B (Θ j)))+d*↑(coverNumber X.p.B ((F).region j))=0 from neg_add_cancel _, Real.exp_zero,mul_one]; ring -- motive
 next hz=> exact mul_nonneg hC hp
end Adjustment
end YM.Qlocal.Moonset
