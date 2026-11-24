import YM.OPE.Compatible.Maestro.ClockCapture
/-!
# Relative cost at receiver budget

Along the time q. Epoch and relative mesh polynomial in growth.
Also match one much deeper parent-offset clock for every node.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot
variable {G:Gauge}{C:Family G}{I : Type}{l:Filter I}{T r : I→ℝ}{q:I→ℕ}{η:ℝ}
variable (hG:G.Simple)(A:Allot C)(b:ℕ)
variable (hη:0 < η)(hr:Tendsto r l (𝓝[>]0))(ht:Tendsto T l atTop)
-- receiver even when no subordinate logarithmic growth is known. need an upper logarithmic budget in analysis.
variable (h:Score l T (fun i=>-Real.log (r i)))
def closeK (C:Family G)(b:ℕ)(η R:ℝ):ℕ:= topClock C b (η*R)
set_option quotPrecheck false
local notation "m"=> fun i=>closeK C b η (r i)
include hr hη
set_option linter.unusedSectionVars true
lemma downscopes (j:ℕ):∀ᶠ i in l,0 < r i∧ η*r i ≤ touch C b j:=by
   refine (hr.eventually self_mem_nhdsWithin).and ?_
   have small := (hr.mono_right nhdsWithin_le_nhds).eventually
     (ge_mem_nhds (div_pos (touch_pos C b j) hη))
   filter_upwards [small] with i hi
   simpa only [mul_comm (r i) η] using (le_div_iff₀ hη).mp hi
include A hG
lemma elevated :Tendsto (fun i=>closeK C b η (r i)) l atTop:=by
    refine tendsto_atTop.mpr (fun j=>?_); filter_upwards [downscopes (C:=C) b hη hr j] with i ⟨hp,h⟩; exact (wins (b:=b) hG A (mul_pos hη hp) ⟨j,h⟩).2 j h
lemma caught : ∀ᶠ i in l, η*r i ≤ touch C b (m i)∧ ∀ j:ℕ,m i < j→touch C b j < η*r i:=by
    filter_upwards [downscopes (C:=C) b hη hr 0] with i ⟨hp,h⟩; have he:=wins (b:=b) hG A (mul_pos hη hp) ⟨0,h⟩; exact ⟨he.1,fun j hh=> lt_of_not_ge fun hp=>hh.not_ge (he.2 j hp)⟩
include ht h
lemma epoch_score :Round l T (fun i=>β C (m i)):=by
    have hh:= elevated hG A b hη hr; apply scale_coin hG hh ht; have hp:= ((h.plus (Score.steady (-Real.log η) ht) ht).product (Score.steady 2 ht)); apply hp.pointwise _ (Eventually.of_forall fun i=> Shoot.scale_nn ..)
    filter_upwards [caught hG A b hη hr,(hr.eventually self_mem_nhdsWithin), hh.eventually (timer_rate hG A b)] with i hc hf hw
    have ha:= Real.log_le_log (mul_pos hη (show 0< r i from hf)) (hc.1.trans hw); rw [Real.log_mul hη.ne' (ne_of_gt hf),Real.log_exp] at ha; linarith only [ha]
lemma arrival_price : Round l T (fun i=>C.S.a (m i)/r i):=by
    let v i:=closeK C b η (r i); let L:=level C; have he:= epoch_score hG A b hη hr ht h; have hh:= caught hG A b hη hr
    have hv : ∀ᶠ i in l,0 < r i:= hr.eventually self_mem_nhdsWithin
    have hy : ∀ᶠ i in l,0 < C.S.a (v i)/r i:= hv.mono fun i hi =>div_pos (C.S.a_pos _) hi
    refine ⟨hy, Score.pointwise (r:=fun i=> β C (m i)*η) (he.up.product (Score.steady η ht)) ?_ (hy.mono fun i hp=> hp.le),((Score.steady (8/η:ℝ) ht).product (round_time hG A b ht he.up|>.up)).pointwise ?_ (hy.mono fun _ hp=> (inv_pos.mpr hp).le)⟩
    · filter_upwards [hv,hh] with i hp hu
      apply (div_le_iff₀ hp).2; have hv:=scopeR_up C b (v i+1); let Y:= C.S.a (v i+1)
      have hI:Y ≤ touch C b (v i+1) := le_trans (le_mul_of_one_le_left (C.S.a_pos _|>.le) (by norm_num : 1≤ (8:ℝ))) (le_mul_of_one_le_right (mul_nonneg (by norm_num) (C.S.a_pos _).le) hv)
      have hL:0<extent C (v i):=by exact_mod_cast (C.path.levels.S.block (v i)).property
      have hc:= hI.trans (hu.2 _ (lt_add_one _)).le; have ht' : C.S.a (v i)= Y*extent C (v i):= by unfold Y;rw [C.S.a_step]; exact (div_mul_cancel₀ _ hL.ne').symm
      change C.S.a (v i) ≤ _; rw [ht']; exact (mul_le_mul hc (A.block_cheap _) hL.le (by positivity)).trans_eq (by ring)
    filter_upwards [hh] with i hi; rw [inv_div]; apply (div_le_iff₀ (C.S.a_pos _)).2; refine le_trans ((le_div_iff₀ hη).mpr ((mul_comm ..).le.trans hi.1)) (le_of_eq ?_); unfold touch; ring
end YM.OPE.Arboreal
