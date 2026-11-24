import YM.RG12.Common.Advance
/-!
# A thinner connector plan to pay all stage gaps

Just `Covered` bought one gap of logarithmic length. For cumulative use of the price criterion,
we need to charge every stage crossing (even when there are ambiguities near stage boundaries).
This implements stage financing for those connector apertures; it costs just an extra threshold
on the contours of the constructed schedule. Charges are sub-polynomial, express in terms of
`mite j`, share of a fixed total exponent budget allocated to stage j. Crucially can charge
against stage monotonicity for ALL transitions, even if the bars themselves are not chosen
doubling/reg-varying across stages. No occurrence of a stage-specific constant in the cumulative
transport's polynomial exponents.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Alidade
open Function Filter Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak Commission
open Pert.Dense
open scoped Topology BigOperators

def mite (j : ℕ) : ℝ := ((j:ℝ)+1)⁻¹ - ((j:ℝ)+2)⁻¹
def pile (j : ℕ) : ℝ := 1 - ((j:ℝ)+2)⁻¹
lemma mite_eq (j:ℕ) : mite j = ( (j:ℝ)+1)⁻¹ * ((j:ℝ)+2)⁻¹:=by
   unfold mite
   have h:0<(j:ℝ)+1:=by positivity
   have h':0<(j:ℝ)+2:=by positivity
   field_simp; ring
lemma mite_pos (j:ℕ):0< mite j:=by rw [mite_eq]; positivity
lemma mite_le (j:ℕ):mite j≤1:=by rw [mite_eq]; exact mul_le_one₀ (inv_le_one_of_one_le₀ (by linarith [show 0≤ (j:ℝ) by positivity])) (inv_nonneg.mpr (by positivity)) (inv_le_one_of_one_le₀ (by linarith [show 0≤ (j:ℝ) by positivity]))
lemma mite_anti {i j:ℕ}(h:i≤j): mite j ≤ mite i:=by rw [mite_eq,mite_eq]; gcongr
lemma pile_mono : Monotone pile:=by
   intro i j h; unfold pile; gcongr
lemma pile_pos (j:ℕ):0 ≤ pile j:=by unfold pile; linarith only [inv_le_one_of_one_le₀ (show (1:ℝ)≤ (j:ℝ)+2 by linarith only [Nat.cast_nonneg (α:=ℝ) j])]
lemma pile_le (j:ℕ):pile j≤ 1:=by unfold pile; linarith only [inv_nonneg.mpr (show (0:ℝ) ≤ (j:ℝ)+2 by positivity)]
lemma pile_pays {i j u:ℕ}(h:i<j)(ht:j≤u): pile i+mite j ≤ pile u:=by
   apply le_trans _ (pile_mono ht); unfold pile mite; have h':(i:ℝ)+2 ≤ (j:ℝ)+1:=by exact_mod_cast (show i+2≤ j+1 by omega)
   linarith only [inv_anti₀ (show 0<(i:ℝ)+2 by positivity) h']

def radar (x:ℝ)(j:ℕ):ℝ:=exp (Real.log x * mite j)
lemma radar_big {x:ℝ}(h:1≤x)(j:ℕ):1≤radar x j:=one_le_exp (mul_nonneg (Real.log_nonneg h) (mite_pos j).le)
lemma radar_later {x y:ℝ}{i j:ℕ}(h:1≤ x)(he:x≤y)(hf:i≤j): radar x j≤radar y i:=exp_monotone (mul_le_mul (Real.log_le_log (zero_lt_one.trans_le h) he) (mite_anti hf) (mite_pos _).le (Real.log_nonneg (h.trans he)))
lemma radar_paid {x:ℝ}(h:1≤x) {i j u:ℕ}(hp:i<j)(ht:j≤u)(A:ℕ): (radar x j)^A * exp ((pile i * Real.log x)* A) ≤ exp ((pile u * Real.log x)*A):=by
   unfold radar; rw [← exp_nat_mul,← exp_add]
   apply exp_monotone; nlinarith only [mul_le_mul_of_nonneg_right (pile_pays hp ht) (mul_nonneg (Real.log_nonneg h) (Nat.cast_nonneg A))]
lemma radar_grows (j:ℕ) : Tendsto (fun x:ℝ=>radar x j) atTop atTop:= Real.tendsto_exp_atTop.comp (Real.tendsto_log_atTop.atTop_mul_const (mite_pos _))

variable {G:Gauge}{p:Sheet G}{w:Rolls p}{θ:Protection w}{D:Delays θ}{B:Bar D}
local notation "lim0"=> Real.log
-- Scheduling thresholds enforce two classes: (1) cheap cover by preceding stage within mite
-- loghat (2) ratio of station pressures and single-step apertures also within mite power of hat,
-- even as meter exceeds L (as already purchased by Slugg and budget). First is realized via
-- extra Wait on this same schedule. Bound kept so use previous covering and adapters unchanged.
structure Thinner (U:Wait B)(j:ℕ)(s:ℝ) extends Bound U j s where
   thins (x):s≤x → ↑(U.window j x)*wide w j ≤ lim0 (preHat B x)*mite j

-- build Thinner
lemma allows_thin (H:G.Simple)(U:Wait B)(h:Early U)(j:ℕ): ∀ᶠ s in atTop, Thinner U j s:=by
   have hf:Tendsto (preHat B) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos H))
   have hx:= (h j).eventually (ge_mem_nhds (div_pos (mite_pos j) (wide_pos w j)))
   obtain ⟨t,ht⟩:= eventually_atTop.mp (hx.and (hf.eventually_gt_atTop 1))
   filter_upwards [allowed H U h j,eventually_ge_atTop t] with k hk hz
   refine ⟨hk,fun x hv=>?_⟩
   obtain ⟨hp,ho⟩:=ht x (hz.trans hv)
   exact (div_le_div_iff₀ (Real.log_pos ho) (wide_pos w j)).mp hp |>.trans_eq (mul_comm ..)
lemma permit (S:Wait B)(h:Early S)(H:G.Simple)(U:Wait B):∃ V:Wait B, Thicker S V ∧ Thicker U V ∧ ∀ j s,V.readyHere j≤ s → Thinner S j s ∧ Thinner S (j+1) s ∧ trial (B:=B) j s ≤ V.window j s:=by
   obtain ⟨V,hp,hq,hv⟩:=prepared S h H U
   choose u hu using fun j=> eventually_atTop.mp (allows_thin H S h j)
   let Q:Wait B:={V with readyHere:=fun j=>max (V.readyHere j) (max (u j) (u (j+1))) }
   exact ⟨Q,⟨hp.minL,fun i=>(hp.ready i).trans (le_max_left ..),hp.range⟩,⟨hq.minL,fun i=>(hq.ready i).trans (le_max_left ..),hq.range⟩,fun j s hQ=>by
     have h1:= (max_le_iff).mp hQ; have h2:= (max_le_iff).mp h1.2; exact ⟨hu _ _ h2.1,hu _ _ h2.2,(hv _ _ h1.1).2.2⟩⟩
end YM.RG12.Alidade
