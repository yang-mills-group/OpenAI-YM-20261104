import YM.FormalBulk08.Grail.Oath

/-! Polynomial charges for the moment and distance-weighted norm bounds. Distances may be
in reporting units or either native mesh. Work in the same receipt
algebra using logarithmic reaches.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sable
open Reef Flat Lattice Laurent Filter Function Next.Free Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {I Y V: Type*} {m n u:ℕ} {ε : ℝ≥0} {σ η A B:ℝ}
-- grain metric

def slant (ε:ℝ≥0)(d:ℕ) := Real.log (1+(ε:ℝ)*d)
def plum (ε:ℝ≥0)(d:ℕ):ℕ:= Nat.ceil (slant ε d)
lemma slant_pos (d:ℕ) : 0≤ slant ε d := Real.log_nonneg (le_add_of_nonneg_right (by positivity))
lemma slant_mono : Monotone (slant ε) := fun a b h=> Real.log_le_log (by positivity) (by gcongr)
lemma plum_mono : Monotone (plum ε):= Nat.ceil_mono.comp slant_mono
lemma plum_self (ε:ℝ≥0) : plum ε 0=0:= by simp [plum,slant]
lemma plum_tri (a b:ℕ): plum ε (a+b)≤ plum ε a +plum ε b:= by
   have hz: (1+(ε:ℝ)*(a+b:ℕ))≤ (1+(ε:ℝ)*a)*(1+(ε:ℝ)*b):= by push_cast; have hh:=mul_nonneg (a:=(ε:ℝ)*a) (b:=(ε:ℝ)*b) (by positivity) (by positivity); linarith
   have ht := Real.log_le_log (by positivity) hz; rw [Real.log_mul (by positivity) (by positivity)] at ht
   apply Nat.ceil_le.mpr; rw [Nat.cast_add]; exact le_trans ht (add_le_add (Nat.le_ceil _) (Nat.le_ceil _))

def grain (R:Reach I)(ε:ℝ≥0) : Reach I where
   d a b:=plum ε (R.d a b)
   turn a b:=by rw [R.turn]
   self a:=by rw [R.self]; exact plum_self _
   tri a b c:=(plum_mono (R.tri ..)).trans (plum_tri ..)
abbrev coast (I:Type)(ε:ℝ≥0):= grain (fame I) ε
lemma plume (R:Reach V)(v:chain V m):wide (grain R ε) v= plum ε (wide R v):= by
   apply le_antisymm; · exact known_wide _ _ _ fun i j=> plum_mono (reached R v i j)
   cases m with
   | zero=>
      suffices wide R v=0 by rw [this,plum_self];exact Nat.zero_le _
      simp [wide]
   | succ m => obtain ⟨k,hx,hp⟩:= Finset.exists_mem_eq_sup (s:=Finset.univ) Finset.univ_nonempty (fun p:Fin (m+1)×Fin (m+1)=> R.d (v p.1) (v p.2)); rw [show wide R v =_ from hp]; exact reached (grain R ε) v k.1 k.2

def gauge (u:ℕ)(ε:ℝ≥0)(d:ℕ):ℝ:=(1+(ε:ℝ)*d)^u
lemma gauge_low (u:ℕ)(ε:ℝ≥0)(d:ℕ):0 ≤ gauge u ε d:= by unfold gauge; positivity
lemma gauge_exp (u : ℕ)(ε:ℝ≥0)(d:ℕ) : gauge u ε d= Real.exp ((u:ℝ)*slant ε d):= by unfold gauge slant; rw [Real.exp_nat_mul,Real.exp_log (by positivity)]
lemma grain_down (u d:ℕ):gauge u ε d ≤ Real.exp ((u:ℝ)*plum ε d):= by rw [gauge_exp]; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _))
lemma grain_up (u d:ℕ): Real.exp ((u:ℝ)*plum ε d) ≤ Real.exp u * gauge u ε d := by
    rw [gauge_exp,←Real.exp_add]; apply Real.exp_monotone; have he: ↑(plum ε d)≤ slant ε d +1 := le_of_lt (Nat.ceil_lt_add_one (slant_pos _)); exact le_trans (mul_le_mul_of_nonneg_left he (show (0:ℝ)≤u by positivity)) (le_of_eq (by ring))
abbrev Mote (R:Reach I)(u:ℕ)(ε:ℝ≥0) := @Knoxville I n (grain R ε) (u:ℝ) -- auto implicits

variable {R:Reach V}{T:Tile V m}{o:V}
lemma particle (h: Knoxville (grain R ε) u o T B) :
    0 ≤ B ∧ Summable (fun v=>gauge u ε (herb R o v)*‖T v‖) ∧ ∑' v,gauge u ε (herb R o v)*‖T v‖≤B:= by
    refine ⟨h.1, from_evil h.1 (fun v=>mul_nonneg (gauge_low ..) (norm_nonneg _)) (le_trans ?_ h.2)⟩; apply ENNReal.tsum_le_tsum; intro v; rw [ENNReal.ofReal_mul (gauge_low ..), ofReal_norm,plume]; exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (grain_down ..)) _
lemma back_grain (he:0≤ B) (h:Summable (fun v=>gauge u ε (herb R o v)*‖T v‖))(hp:(∑' v,gauge u ε (herb R o v)*‖T v‖) ≤ B): Knoxville (grain R ε) u o T (Real.exp u*B):= by
    refine ⟨mul_nonneg (Real.exp_pos _).le he,?_⟩
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le]; have hz:= ENNReal.ofReal_le_ofReal hp; rw [ENNReal.ofReal_tsum_of_nonneg (fun _=> mul_nonneg (gauge_low ..) (norm_nonneg _)) h] at hz; refine le_trans ?_ (mul_le_mul_right hz _); rw [←ENNReal.tsum_mul_left]; refine ENNReal.tsum_le_tsum fun v=>?_; rw [ENNReal.ofReal_mul (gauge_low ..),ofReal_norm,plume,←mul_assoc,← ENNReal.ofReal_mul (Real.exp_pos _).le]; apply mul_le_mul_left; exact ENNReal.ofReal_le_ofReal (grain_up _ _)
-- Exponential supplies → polynomial demands via receipts, price explicit before L.
def sack (u:ℕ)(η:ℝ):ℝ:= Real.exp u*(pockets u (σ:=1) (by norm_num)).choose * (1+η⁻¹)^u
lemma sack_pos (u:ℕ)(hs:0 < η): 0 ≤sack u η:= by unfold sack; have hx:= (pockets u (σ:=1) (by norm_num)).choose_spec.1; positivity
lemma sack_for (u:ℕ) (hs:0<η)(e:ε≤1)(n:ℕ): Real.exp ((u:ℝ)* plum ε n) ≤ sack u η * Real.exp (η*n):= by
    apply (grain_up _ _).trans
    have hε:(ε:ℝ)≤1:=by exact_mod_cast e
    let s:ℝ:=1+η*n
    have h:1+(ε:ℝ)*n ≤ (1+η⁻¹)*s:= by dsimp [s]; have hg:=mul_nonneg hs.le (Nat.cast_nonneg (α:=ℝ) n); have hp:=inv_pos.mpr hs; have hl: η⁻¹*(η*(n:ℝ))=n:=inv_mul_cancel_left₀ hs.ne' _; nlinarith
    have hx: gauge u ε n ≤ (1+η⁻¹)^u * s^u:= by rw [←mul_pow];apply pow_le_pow_left₀ (by positivity) h
    unfold sack
    have hu: s^u ≤ _:= (pockets u (σ:=1) (by norm_num)).choose_spec.2 (η*n) (by positivity); rw [one_mul] at hu; apply (mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_left hu (by positivity))) (Real.exp_pos _).le).trans_eq; ring
lemma sack_to (u:ℕ)(hs:0<η)(hb:ε≤1)(h:Knoxville R η o T B): Knoxville (grain R ε) u o T (sack u η *B):= by
   refine ⟨mul_nonneg (sack_pos u hs) h.1,?_⟩; rw [ENNReal.ofReal_mul (sack_pos u hs)]; refine le_trans ?_ (mul_le_mul_right h.2 _);rw [←ENNReal.tsum_mul_left];refine ENNReal.tsum_le_tsum fun v=>?_ ; rw [←mul_assoc, plume,Gorge.shine,Gorge.shine,←ENNReal.ofReal_mul (sack_pos u hs)]; exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (sack_for u hs hb _)) _
end YM.FormalBulk08.Sable
