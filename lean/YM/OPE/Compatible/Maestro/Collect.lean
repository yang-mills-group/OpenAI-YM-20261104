import YM.OPE.Compatible.Maestro.Cycle
/-! Geometry with one finite-set post-L constant, full parameter family -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot Series
variable {G:Gauge}{C:Family G}{I V:Type}{φ:Filter I}{T r : I→ℝ}{q:I→ℕ}{b n:ℕ}
variable [PartialOrder V][Fintype V][OrderBot V](D:Origin V){η : ℝ} {s:I→V→ℝ}{M:ℝ}{Q:Finset V}
variable (hG:G.Simple)(A:Allot C)(h: Glowing D Q φ T s η)
-- earth parameters: N=ceiling enough. compared widths. recovery uses at most ratio(T parent) powers
-- l=C*(gap+3+2)=C*gap. allocate H ... use GridTexture projection closeness. s_center. geometry for direct sweep, priced arbitrary evaluation grids via offsets. no constraints outside
set_option quotPrecheck false
variable (b d J:ℕ)
local notation "t"=>fun i=>schedule C b η (s i)
local notation "at!"=>fun i=>aperture D C b d η (T i) (s i)
local notation "sp"=>fun i=> C.S.a i
def course (C:Family G)(b L i:ℕ):= L*(5+gapL C b i)
-- relative edge spacings budget. only crown.
structure Ridge (s:V→ℝ) (η M:ℝ)(D:Origin V)(U:Finset V)(x:V→E4): Prop where
    belly : x ⊥=0
    near x' y : x'∈ U→ y∈allUp D U → x'≤ y→ ‖x x'-x y‖ ≤ M * s x'
    span x' y: x'∈ allUp D U→ y∈allUp D U→ ¬ x' ≤ y → ¬ y≤ x' → η*s (couple D x' y) ≤ ‖x x'-x y‖
lemma diverge {x y:V}(hp: Crown Q)(hx:x∈ allUp D Q)(h:¬ x ≤ y) : couple D x y∈ Q:=by
    have ht:= separate_left D h; rcases Finset.mem_union.mp hx with hh|hh; exact hp.roots ht.le hh; exact hp.roots (touch_par D ht) ((on_brim ..).mp hh|>.2.2)
include hG A h
lemma canopy_wave (hM:0 ≤ M) (L:ℕ)(hL:8*M/η+2 ≤ (L:ℝ)):∀ᶠ i in φ,∀ y:V→ Cover,∀ W:ℕ,Ridge (s i) η M D Q (C.S.gridPoint W ∘ y) → y ⊥=0→ (∀ v∈allUp D Q, at! i v≤ W ∧ ∃ x:Cover,C.S.gridPoint W (y v)= C.S.gridPoint (at! i v) x) → Pixel.Positioned C D Q (t i) (at! i) b J W (course C b L) y:=by
    have hb := h.crowned.base; let a i:= t i; let z i:= at! i
    have hh:=lives D hG A h b hb
    have hZ : ∀ᶠ i in φ, 8*(M*s i ⊥) ≤ C.S.a J := (show Tendsto (fun i=> 8*(M*s i ⊥)) φ (𝓝 0) from by simpa using ((h.fade _ hb).mono_right nhdsWithin_le_nhds|>.const_mul M|>.const_mul 8)).eventually (ge_mem_nhds (C.S.a_pos _))
    obtain ⟨g,hg⟩:= eventually_atTop.1 ((timer_stops hG A b).eventually (ge_mem_nhds (C.S.a_pos J)))
    filter_upwards [hZ,hh.eventually_ge_atTop g, hh.eventually_gt_atTop (C.ref 0),hh.eventually_ge_atTop J,(eventually_all_finset Q).mpr (fun v hv=> caught hG A b h.positive (h.fade v hv))] with i he hv ht he' hz y W hU hY hN
    let x u:= C.S.gridPoint W (y u); have hB:x ⊥=0:=hU.belly
    refine ⟨ht,he',fun _ _=> finish_aperture D b d _ _, fun x hx=> (hN x hx).1,fun x hx=> (hN x hx).2,hY,fun v hy=>?_,fun j hj=> ?_, fun u v hu hv hx hy j he=> ?_,fun u v hu hy hh hi=> ?_⟩
    · have h:= hU.near _ v hb hy bot_le; change ‖x ⊥-x v‖ ≤ _ at h; rw [hB,zero_sub,norm_neg] at h; exact (mul_le_mul_of_nonneg_left h (by norm_num)).trans he
    · have h:=hg j (le_trans hv hj); change touch C b j ≤ C.S.a J at h; unfold touch scopeR at h; have hf:= C.S.a_pos J; linarith only [h,hf]
    · let u':=couple D u v; have h: touch C b j < η * s i u' := (hz u' (diverge D h.crowned hu hx)).2 _ he; unfold touch scopeR at h; have ht:=(u':V) -- remove
      have hw:= scopeR_up C b j; unfold scopeR at hw; change _ ≤ ‖x u-x v‖; have hK:η*s i u' ≤ ‖x u -x v‖:=hU.span _ _ hu hv hx hy; nlinarith only [mul_nonneg (le_trans zero_le_one hw) (C.S.a_pos j|>.le), h,hK]
    let q:= schedule C b η (s i) u; have hu':η*s i u ≤ 8*C.S.a q*scopeR C b q:= (hz u hu).1
    let H:= gapL C b q; let B:ℝ:= (bins C q).B; let a0:= C.S.a q; let g:ℝ:= L; have ha:0<a0:=C.S.a_pos _; have he2:0<η:=h.positive
    have hT:1 ≤ B:= by unfold B; exact_mod_cast (show 1 ≤ (bins C q).B from (bins C q).B_pos)
    have hp : scopeR C b q ≤ (5+H:ℝ)*B := by unfold scopeR atLevel; push_cast; unfold H B; linarith only [hT] -- nat casts
    have hM':s i u ≤ ((8/η)*((5+H:ℝ)*B))*a0:=by
       apply le_of_mul_le_mul_left _ he2; refine le_trans hu' ((mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq ?_); unfold a0; field_simp
    have hh' :(course C b L q:ℝ)*B=g*(5+H)*B:=by unfold course; push_cast; rfl
    change ‖x u-x v‖+2*a0 ≤ a0*_ *B
    have hh'' : (5+H:ℝ)*B≥1:=by nlinarith [Nat.cast_nonneg (α:=ℝ) H]
    calc
      _ ≤ M*(((8/η)*((5+H:ℝ)*B))*a0)+2*a0 := add_le_add_left ((hU.near u v hu hy hh).trans (mul_le_mul_of_nonneg_left hM' hM)) _
      _ ≤ ((8*M/η+2)*((5+H:ℝ)*B))*a0:=by
          rw [add_mul _ _ ((5+H:ℝ)*B),add_mul _ _ a0]; refine add_le_add (le_of_eq ?_) ?_; ring; exact mul_le_mul_of_nonneg_right (by linarith only [hh'']) ha.le
      _ ≤ _:= le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL (zero_le_one.trans hh'')) ha.le) (le_of_eq (by rw [mul_assoc a0,hh']; unfold g; ring)) -- hp name
end YM.OPE.Arboreal
