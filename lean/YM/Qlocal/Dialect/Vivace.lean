import YM.Qlocal.Dialect.Masons
/-!
# Authorization billing table for one REAL value/sensing family.Shroud active for EXACT
 one set of canonical input log rows with markup. Output summary publishes REAL Φ kernel & prices, yet still supports every old payload via Epoch.Section.We.Edge.Calendar.Modeling proof.Frame.
 Group *all simultaneously* even with different actual incoming targets. Homogeneity costs.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Dialect
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical YM.Qlocal.Gauges.Atlas
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V Ω J J' J₀ K α:Type}[DecidableEq V]{G:Gauge}{n:Side}{N j k:ℕ} {R:Census V}
open Gauges Quipu Quipu.Sonnet Tern
namespace Patchwork
open Atlas
variable [Fintype V]
variable {s:Senses R} {g:V→ℕ} {η β x C v: ℝ}
open AllOrder AllOrder.Floe AllOrder.Fire Gauge
open Quipu.Eluder.Incline Quipu.Eluder.Incline.Bookworm
variable [Nonempty V]
instance options (R:Marker.Census V): Nonempty (Atlas.Notice R):= by
 let p :V:= Classical.ofNonempty; let Q:Senses R:=⟨R.fire p,singleton_nonempty _⟩; exact ⟨⟨{Q},singleton_nonempty _,fun _ hu j hv h=>False.elim (h ((mem_singleton.mp hu).trans (mem_singleton.mp hv).symm)),(by rw [singleton_biUnion]; exact (Q.val).prop)⟩⟩
-- binder semantics h(s) positive serializer symbol.We keep public thresholds ℝ.T.Time. use also κ flags across Warm restoration. Need unify with .Frame_NOTICE.
variable (S:Atlas.Notice R→ Stanza R G g j)(w:Senses R→ℝ)(h:Senses R→ℝ)
noncomputable abbrev tintR (i:Atlas.Notice R):ℝ:= ∏ j∈i.val,w j
lemma tint_cost (i:Atlas.Notice R): Patchwork.term i (Complex.ofReal ∘ w)=↑(tintR w i):= (Complex.ofReal_prod ..).symm
noncomputable def cargo (i:Atlas.Notice R)(s:Senses R):ℝ:= if i∈ attention s then (tintR w i)/(h s) else 0
noncomputable abbrev skyline : Stanza R G g j:= Stack.horizon S (cargo w h)
local notation "K"=> Stanza.son (skyline S w h) N
local notation "J"=> Atlas.Notice R
local notation "S[" i "]"=> Stanza.son (S i) N
variable (η₀:Atlas.Notice R→ℝ) (hp:∀ i,(Stanza.son (S i) N).Allows η (η₀ i))(hQ:0<η)(ht:∀ i,0< h i)
variable {q':Ray R}
variable (q:Rental q')(hv:∀ i,q' (i:Senses R).val* |w i| ≤1)
variable (s:Senses R)(o:V→Site n)(U:Config G n)(x:ℝ)
set_option quotPrecheck false
local notation "Λ"=> attention s
local notation "κ"=> (h s)
local notation "cost"=> q' s.val
include ht
-- h≥ U0/q(heroτ) (h assigned target certification number, not new meaning). pay_ Weights shape.
lemma striving (u:ℝ)(A:Atlas.Notice R→ℝ)(hA:u= ∑ t:J,cargo w h t s*A t): κ*u= ∑ t∈Λ,(tintR w t)*A t:= by
 rw [hA,mul_sum, Patchwork.attention,sum_filter]; apply sum_congr rfl; intro p _; unfold cargo Patchwork.attention; split_ifs with he ht₁ hv hv
 · field_simp [(ht s).ne']
 · exact (ht₁ (mem_filter.mp he).2).elim
 · exact (he (mem_filter.mpr ⟨mem_univ _,hv⟩)).elim
 simp
include hp
-- any payment ambition.Mark.En
lemma owns (hc:∀ s:Senses R, ∑ i:Atlas.Notice R, |cargo w h i s| *η₀ i≤C): (Stanza.son (skyline S w h) N).Allows η C:= Stack.honors S (cargo w h) η₀ hp hc
omit ht hp
include q hv
lemma invoice (i:Atlas.Notice R)(he:i∈attention s): q' s.val* |tintR w i| ≤1:= by
 have hx:grade R i = s.val:=congr_arg Subtype.val ((mem_filter.mp he).2); have hc: q' s.val ≤ ∏ j∈i.val, q' ((j:Senses R).val):= hx ▸ Revenue.buys q Subtype.val i.val i.prop.2; unfold tintR; rw [Finset.abs_prod]; apply (mul_le_mul_of_nonneg_right hc (prod_nonneg fun j _=> abs_nonneg _)).trans; rw [← Finset.prod_mul_distrib]; apply le_trans (Finset.prod_le_prod (g:=fun _=>1) ?_ ?_) (le_of_eq (prod_const_one)); exact fun i _=>mul_nonneg (q.pos _).le (abs_nonneg _); exact fun i _=>hv i -- args
include ht
private lemma loyalty (i:J)(he: η₀ i≤ C)(hx:C≥0)(hη:0≤ η₀ i) : |cargo w h i s| * η₀ i≤ C /(q' s.val*h s):= by
 unfold cargo; have hc: 0 < q' s.val:=q.pos _; have hz:0 < h s:= ht s; split_ifs with hi; swap; · rw [abs_zero,zero_mul]; positivity
 rw [abs_div,abs_of_pos hz]; apply (le_div_iff₀ (mul_pos hc hz)).2; calc (_ : ℝ) = q' s.val* |tintR w i| * η₀ i:= (by field_simp)
                                                         _ ≤ C := (mul_le_of_le_one_left hη (invoice w q hv s i hi)).trans he
lemma accepted (C:ℝ) (hU:∀ i,η₀ i≤C)(hC: C≥0)(hv':∀ i,0≤η₀ i) (hk:∀ s:Senses R, (Fintype.card (Atlas.Notice R):ℝ)* C ≤ q' s.val*h s) : ∀ s, ∑ i:J, |cargo w h i s| *η₀ i ≤ 1:= by
 intro s; apply le_trans (Finset.sum_le_sum (g:=fun i=>C/(q' s.val*h s)) (fun i _=>loyalty w h η₀ ht q hv s i (hU i) hC (hv' i))) ?_; rw [sum_const,nsmul_eq_mul,card_univ,← mul_div_assoc]; exact (div_le_one (mul_pos (q.pos _) (ht _))).2 (hk _)
omit q hv
include hp hQ
lemma published (j:ℕ) : h s*Tale.wake s K (Tale.short K (Anthem.statement K) j) o x U=∑ t∈Λ, tintR w t*Tale.wake s S[t] (Tale.short S[t] (Anthem.statement S[t]) j) o x U:= by apply striving w h ht s _ _; exact Stack.uncured S (cargo w h) η₀ hp s o U hQ x j
open AllOrder.Ker Primitives.TwoWave Primitives.TwoWave.RealSlice Exterior Precision
lemma hailed (x:rule (Coarse G) n)(j:ℕ): h s*Anthem.grasp0 K o s j x=∑ t∈Λ, tintR w t * Anthem.grasp0 S[t] o s j x := by apply striving w h ht s; exact Stack.words S (cargo w h) η₀ hp s o hQ x j
end Patchwork
end YM.Qlocal.Dialect
