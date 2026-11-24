import YM.FormalBulk08.Spigot.Stone
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}
open Grail Precision Work.F03 Pose Tensor
open Planned.PrimaryIntegral295 Place Carrier
open scoped Matrix.Norms.Frobenius
variable {M:Cabin D I G r}
lemma deposits (h:Energy M u σ A)(hs:0≤σ)(p:Studio D): SumBudget (fun i=> (M.atoms i).budget σ * ‖M.pulse i p‖) (A*‖p‖):= by
   refine sum_tier ⟨fun i=>mul_nonneg (h.income.1 i) (norm_nonneg p),h.income.2.1.mul_right ‖p‖, Eq.le (tsum_mul_right ..) |>.trans (mul_le_mul_of_nonneg_right h.income.2.2 (norm_nonneg p))⟩ (fun i=> by unfold Atom.budget Atom.magnitude; positivity) (fun i=>?_)
   let μ:=M.plus i; let ν:=M.minus i; let m:ℝ:=(M.atoms i).length
   rw [h.paper]; have hp: 0≤(M.atoms i).magnitude:= by unfold Atom.magnitude; positivity
   unfold Atom.budget; rw [mul_assoc, mul_assoc]; apply mul_le_mul_of_nonneg_left _ hp
   refine (mul_le_mul_of_nonneg_left (record_prices (h.plus i) (h.minus i) p) (Real.exp_pos _).le).trans ?_
   rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (burse_cold u (Nat.cast_nonneg _) hs (h.plus i) (h.minus i)) (norm_nonneg _)

def candle (M:Cabin D I G r)(p:Studio D)(j:ℕ):Tile (edgeL G) j:=fun v=> ∑' i,M.pulse i p * flame (M.atoms i) j v
lemma candle_low (M:Cabin D I G r)(p:Studio D)(j:ℕ)(h:j<r): candle M p j=0:= funext fun v=> by simp [candle,flame_low _ h]
lemma candle_turn (M:Cabin D I G r)(p:Studio D)(j:ℕ): Agate (candle M p j):= fun v l=>tsum_congr fun i=>congr_arg (M.pulse i p * ·) (flame_register _ _ v l)
lemma candle_bill (o:Loc G 1)(r t:ℕ)(hs:0<σ):∃ η C:ℝ,0<η∧0≤C ∧ ∀ (M:Cabin D I G r)(A:ℝ)(u:ℕ), Energy M u σ A →∀ p:Studio D,Allow (fame _) η (0,o) (fun v i=> M.pulse i p * flame (M.atoms i) t v) (A*C*‖p‖):= by
   obtain ⟨η,C,h,hC,H⟩:= rub o t r hs; refine ⟨η,C,h,hC,fun M A u h p=>?_⟩
   have hA:0≤A:= (tsum_nonneg h.income.1).trans h.income.2.2; refine ⟨by positivity,?_⟩
   rw [ENNReal.tsum_comm]; let f i:=(M.atoms i).budget σ*‖M.pulse i p‖; have hk:=deposits h hs.le p
   have hp i : Knoxville (fame _) η (0,o) ((M.pulse i p) • flame (M.atoms i) t) (f i*C) := by have hh:= (H (M.atoms i)).smul (M.pulse i p); rw [←Real.norm_eq_abs,mul_left_comm,←mul_assoc] at hh; exact hh
   refine (ENNReal.tsum_le_tsum fun i=> (hp i).2).trans ?_; rw [←ENNReal.ofReal_tsum_of_nonneg (fun i=>mul_nonneg (hk.1 i) hC) (hk.2.1.mul_right _),tsum_mul_right]; apply ENNReal.ofReal_le_ofReal; exact (mul_le_mul_of_nonneg_right hk.2.2 hC).trans_eq (mul_right_comm ..)
lemma candle_linear (o: Loc G 1)(h:Energy M u σ A)(hs:0<σ)(j:ℕ): IsLinearMap ℝ (fun p=> candle M p j):= by
   obtain ⟨η,C,H,-,hp⟩:=candle_bill (D:=D) (I:=I) o r j hs
   constructor
   · intro x y;ext w; unfold candle; rw [Pi.add_apply]; simp_rw [map_add,add_mul]; exact (((hp M A u h x).points H.le w).of_norm).tsum_add (((hp M A u h y).points H.le w).of_norm)
   intro a x; ext w; unfold candle;simp_rw [Pi.smul_apply,map_smul,smul_eq_mul,mul_assoc,tsum_mul_left]
lemma Allow.clock
    {J X:Type*}{T:chain (Biglot J) t→ X→ℝ}{o:Biglot J}(h:Allow (fame _) η o T A)(hs:0≤η)(x:chain (Tor n J) t): sieve n (fun v=> ∑' i,T v i) x=∑' i,sieve n (fun v=> T v i) x:= by
    unfold sieve;let I:=Yard n x; let f (p:I × X):= T p.1.val p.2
    have hf:Summable f:= by
       apply Summable.of_norm; apply tsum_enorm_ne_top_iff_summable_norm.mp; refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ h.2); rw [ENNReal.tsum_prod']; refine le_trans ?_ (ENNReal.tsum_comp_le_tsum_of_injective (f:=fun p:I=>p.val) Subtype.val_injective _); exact ENNReal.tsum_le_tsum fun p=> ENNReal.tsum_le_tsum (fun i=> le_mul_of_one_le_left' (shine_plus _ hs _))
    symm; exact Summable.tsum_comm hf
lemma candle_tor (o:Loc G 1)(h:Energy M u σ A)(hs:0<σ)(p:Studio D)(v:chain (wire G n) t):sieve n (candle M p t) v=∑' i,M.pulse i p * jetL (M.atoms i) n t v:= by
    unfold candle; obtain ⟨η,C,hp,-,H⟩:=candle_bill (D:=D) (I:=I) o r t hs; refine Eq.trans (Allow.clock (H M A u h p) hp.le v) ?_; refine tsum_congr fun i=>?_ ; rw [← jet_comp]; exact congr_fun (sieve_smul n (flame _ _) (M.pulse i p)) v
end YM.FormalBulk08.Spigot
