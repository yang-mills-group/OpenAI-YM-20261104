import YM.Qlocal.Moonset.Change
/-!
# Call site at the marked re-encoding for the next step

Actual amplitude gain *values* (real) come with their rental receipts. After the stencil edit,
rendering remains the true full common-hull mask of the model and we change normalization by a
scalar W keeping its cost visible. Exact error data with the same uncertainty history and ready
board. We've *not* actually re-allocated/layout-compressed the hard terms here (not necessary —
on precisely the same activities and support). They must pass the next K budget including any
support charges at that next-parent step.
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
variable {n:Side} {g:V→ℕ}{p M:ℕ}{a b C B v r t δ:ℝ} {o: V→Site n}
open Dialect Patchwork Quipu.Eluder.Incline Quipu.Eluder.Incline.Bookworm
namespace Adjustment
noncomputable def purchase (δ:ℝ) (A: Stanza R G g p) : Stanza R G g p:= Stack.horizon (fun _ : Unit=> A) (fun _ _=> δ⁻¹)
section power
variable (Z:Stanza R G g p)(b P:ℝ)(hb: 0<b)(hP:1 ≤ P)(a:ℝ)(ha:0<a)(N:ℕ)(h:(Stanza.son Z N).Allows a b)
include h hP
lemma acquire (hz:b ≤ P) : (Stanza.son (purchase P Z) N).Allows a 1:= by
 refine Stack.honors (η₀:=fun _=>b) (fun _ : Unit => Z) (fun _ _=>P⁻¹) (fun _=> h) ?_ ; intro s; let h :=zero_lt_one.trans_le hP; simp only [Fintype.univ_punit,Finset.sum_singleton,abs_of_pos (inv_pos.mpr h)]; rw [mul_comm,← div_eq_mul_inv]; exact (div_le_one h).2 hz -- Fintype.univ_punit etc
variable (η:ℝ)(p':BudgetPoint)(w:ℕ)(o: V→ Site n)(s:Senses R)(x:Config G n)
include ha
lemma adverts : lettering (purchase P Z) p' w N s o (P*η) v x= lettering Z p' w N s o η v x:= by
 unfold lettering Patchwork.substantive; let p:=p'.threshold; let H:= Tale.court p'.B (o (Sonnet.root s)); by_cases hp:Healthy p H x
 · simp only [Function.comp_apply,Pi.smul_apply]; rw [masked_eq _ _ _ _ hp,masked_eq _ _ _ _ hp]; unfold purchase; rw [Stack.uncured (fun _ : Unit => Z) (fun _ _=> P⁻¹) (fun _=> b) (fun _=>h) s o x ha]; let h := (zero_lt_one.trans_le hP).ne'; simp only [Fintype.univ_punit,Finset.sum_singleton,smul_eq_mul]; field_simp
 simp only [Function.comp_apply,Pi.smul_apply]; rw [masked_ne _ _ _ _ hp,masked_ne _ _ _ _ hp,mul_smul,smul_zero,smul_zero] -- maybe mul_smul notation smul ℝ
variable (x':Ker.rule (Primitives.TwoWave.RealSlice.Coarse G) n)(v₁:ℕ)
lemma description (d:ℕ) : data (purchase P Z) s o N ((P*η:ℝ):ℂ) d x'= data Z s o N (η:ℂ) d x':= by
 unfold purchase data; rw [Stack.words (fun _ : Unit => Z) (fun _ _=> P⁻¹) (fun _=> b) (fun _=>h) s o ha, ← Complex.ofReal_mul, ← Complex.ofReal_mul]; let h := (zero_lt_one.trans_le hP).ne'; simp only [Fintype.univ_punit,Finset.sum_singleton]; apply congr_arg; field_simp
end power
-- Control receipt at this `Rep` point (Scribe tapes on output)
variable (X:RG.Rep G n) [Nonempty V] (s: V→Support n) (o:V→Site n)(w N:ℕ) (f:Senses R→ℝ)
    (q: Coin) (q₀:q 0=0) (z zp:ℝ) (T : Ray R) (ht:Rental T)
variable (Y:Ω→ Stanza R G g p) {A D d v0 v1 v2 K1 τ C:ℝ} (a:ℝ) (ha:0<a)
variable (L M:ℕ) (hδ : D ≤ X.p.supportExponent+1) (hD : 0 ≤ D)
-- a width proof pre-metric, and reserve charge fit at that actual support exponent. numeric supplied.
structure Knowledge (M:ℕ) (ρ:ℝ) (C:ℝ) (E:ℝ) : Prop where
 height : (X.p.supportExponent+1) ≤ a*X.p.B
 halo : w ≤ X.p.B
 fit (i:V) : s i⊆ Tale.court (X.p.B - w) (o i)
 living : ∀ x,(Stanza.son (Y x) N).Allows (2*a) 1
 shapes :∀ i:Senses R, Lagger.dues g i.val≤ L
 count : Fintype.card (Senses R)≤ M
 hi : M*(ρ*life X N p L z zp (X.p.supportExponent+1) a q) ≤ C
 tag (i:Senses R): 0 < f i ∧ T i.val* f i ≤ ρ
 money : 1 ≤ E
 cut : price_ops (Moonset.raise q) p (p+L) 1 ≤ E
 nonneg : 0 ≤ ρ
-- capital
set_option quotPrecheck false
local notation "F" => Adjustment.deltaSheet Y o w N f q z zp X.p
local notation "Y★" => fun x=> purchase r (toParent q (Y x))
local notation "C!"=> (life X N p L z zp (X.p.supportExponent+1) a q)
open Scribe
variable (hK: Knowledge X s o w N f q z zp T Y a L M A C r)
    (hZ:0<z)(hZ':0<zp)
include hK ha hZ hZ'
local notation "Z[t]" => t*w
include ht q₀ 
lemma sailors
     : Spend (F) X.p T (X.p.supportExponent+1) C := by
 obtain ⟨H,hB,he,h₁,h₂,h₃,hY,hη,t,r0,hC⟩:=hK; apply Spend.loosen _ hY
 exact Adjustment.stars Y X s o w N f q q₀ z zp T ht he hB (fun i=>(hη i).1.le) hZ hZ' _ a ((div_le_iff₀ (show 0 < ((X.p.B):ℝ) from Nat.cast_pos.mpr X.p.B_pos)).2 H) (by linarith [X.p.exponent_pos]) ha h₁ L M h₂ h₃ (fun i=> le_trans (le_of_eq (by ring)) ((hη i).2)) hC
-- typed application: all thermal predicates now connector.Geometric
variable [Countable J][Countable J'][Countable K] (S:Scribe Ω J G n R)(E:Scribe Ω J' G n R) (U:Scribe Ω K G n R)(K0:Source G n Ω R)
    (W:Ω→ Config G n→Poly R)(hB:Certified X s T D v v0 v1 v2 S E U K0 W)
variable (h0:∀ x i y,(S.send X.p x y).part (i:Senses R).val= lettering (Y x) X.p w N i o (f i) z y)
-- sells true readout *coarse exterior by renormalized model* after generation. Later tie to ModelProof for single epoch. Before Warp weights regrouping.
include q₀ ht hδ hD hB h0
lemma grabbed : Certified X s T D v (v0+C) (v1+C) v2 (S.pile (F)) (E.pile (F).discount) U K0 W ∧ ∀ x i y, ((S.pile (F)).send X.p x y).part (i:Senses R).val= lettering (purchase r (toParent q (Y x))) X.p w N i o (r*f i) zp y:= by
 let p:=X.p.supportExponent+1; have hg : (X.p.supportExponent+1)/X.p.B ≤ a:= (div_le_iff₀ (show 0 < ((X.p.B):ℝ) from Nat.cast_pos.mpr X.p.B_pos)).2 hK.height
 let Hp:=(Adjustment.poseC Y X s o w N f q q₀ z zp hK.fit hK.halo (fun i=>(hK.tag i).1.le) hZ hZ' p a hg (hD.trans hδ) ha hK.living L hK.shapes); let hs: Spend (F) X.p T D C := Spend.narrow (sailors X s o w N f q q₀ z zp T ht Y a ha L M hK hZ hZ') ht hδ
 refine ⟨hB.extend ht hD (F) Hp hs,fun x i y=>?_⟩ -- dot arguments order
 rw [pool hB.model_ok Hp hB.model_spend hs ht hD,Poly.part_plus,identity_p,h0]
 let d':=p; have hS:= retain_price (Y x) (Moonset.raise q) L 1 hK.shapes (hK.living x); rw [adverts (v:=zp) (toParent q (Y x)) _ _ hK.money (2*a) (mul_pos (by norm_num) ha) N hS _ X.p w o i y]; abel
end Adjustment
end YM.Qlocal.Moonset
