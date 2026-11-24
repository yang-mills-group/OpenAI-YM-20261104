import YM.MS.Vista.Scales
/-!
# Grade windows. Monotone envelopes.Net stages. No exponential needed except scalar future.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo
open scoped Topology ContDiff Interval
variable {I E:Type}{G:Gauge}[NormedAddCommGroup E][NormedSpace ℝ E]{P:Belt I}{M:Visa I}{a:I→ℝ}{F H: Glade G I}{ L:I→Side}{b c:Bool}{d:ℤ}
abbrev goodM (P:Belt I)(x:ℝ)(i:P.time):ℝ:= P.price.length i ^ (-x)
-- use R^ℝ. ξ=.5
lemma pay_m (P:Belt I)(x:ℝ): nn ( goodM P x ):= fun _=> Real.rpow_nonneg (P.price.pos _|>.le) _
lemma gearZ (P:Belt I)(x:ℤ): goodM P (x:ℝ)= rateS P x:= by ext p; unfold goodM rateS; rw [ ← Int.cast_neg, Real.rpow_intCast ]
def gainQ (P:Belt I)(L:I→Side)(j:ℕ)(x:P.time): ℝ:= ( P.price.length x / tickA L x.1 )^j
lemma gain_pos (P:Belt I)(L:I→ Side)(j:ℕ): nn (gainQ P L j):= fun x=> pow_nonneg ( div_nonneg ( P.price.pos x |>.le ) ( δ_p L x.1 |>.le ) ) _
lemma AmountMX (x: (midpoint M L).time): (midpoint M L).price.length x= lamp (tstart x):= rfl
lemma midT (x:(midpoint M L).time): 0≤tstart x ∧ tstart x ≤ until0 L x.1:= x.2.property
lemma gain_le { j k:ℕ}(hp:j≤k): gainQ (midpoint M L) L k ≤ gainQ (midpoint M L) L j := by intro p; apply pow_le_pow_of_le_one (div_nonneg (lamp_p _|>.le) (δ_p ..|>.le)) _ hp; exact ( div_le_one (δ_p ..)).mpr ( le_trans ( le_of_eq ( AmountMX p ) ) (lamp_m ( midT p|>.2)|>.trans_eq (glowH ..))) -- binder
lemma tsbill (h:Accel P a){n:ℕ}(i j:P.time)(hp:i.1=j.1)(he:tstart i≤ tstart j)(c:ℝ)(hx: 0≤ (n:ℝ)-c) : goodM P c i * gainQ P L n i ≤ goodM P c j *gainQ P L n j := by
    let X:= tickA L i.1; have ht : ∀ z:P.time, goodM P c z * gainQ P L n z = P.price.length z ^ ((n:ℝ)-c) / ( tickA L z.1 )^n := by intro z; rw [goodM,gainQ,div_pow,Real.rpow_sub (P.price.pos ..),Real.rpow_natCast,Real.rpow_neg (P.price.pos _|>.le)]; ring
    rw [ht,ht,hp]; obtain hh := h.step i j hp he; exact div_le_div_of_nonneg_right ( Real.rpow_le_rpow ( P.price.pos _|>.le) hh hx ) ( pow_nonneg ( δ_p ..|>.le) _ )
lemma unit_β (x:ℝ)(w:Wire (BH G) E QP)(p:P.time): Qbud w P.price (goodM P x) p= goodM P (x-pitch w) p:= by unfold Qbud goodM; rw [ ← Real.rpow_intCast, ← Real.rpow_add (P.price.pos p) ]; congr 1; ring
lemma colony (h:Accel P a)(k:ℕ){x:ℝ}(he: x≤(if c then 1 else 0) + (k:ℝ)) : Adjuster (G:=G) P b c ( goodM P x * gainQ P L k ):= by
    intro E _ _ w hw ht p q hq hV; have hz: 0 ≤ (k:ℝ) - (x-pitch w):= by
       cases c; · have hv : (0:ℝ)≤ (pitch w):=(by exact_mod_cast pitch_nn w); simp only [if_false,Bool.false_eq_true,zero_add] at he; linarith
       have hv: (1:ℝ) ≤ (pitch w):=(by exact_mod_cast ( Vane.pos_pitch w ( ht rfl ) )); rw [ if_pos rfl ] at he; linarith
    change P.price.length p ^ pitch w * ( goodM P x p * _ ) ≤ P.price.length q ^ pitch w * (goodM P x q * _); rw [← mul_assoc, ← mul_assoc , show P.price.length p ^ pitch w * goodM P x p= _ from unit_β x w p, show P.price.length q ^ pitch w * goodM P x q= _ from unit_β x w q]; exact tsbill h p q hq hV _ hz -- `unit_β` lhs no rewrite?
lemma gain0 (P:Belt I)(L:I→ Side): gainQ P L 0=1:= funext fun _=> pow_zero _
lemma level (h:Accel P a){x:ℝ}(hx:x≤(if c then 1 else 0)): Adjuster (G:=G) P b c ( goodM P x ):= by -- use fake L.If no L.Free explicit constant side
   obtain ht:= colony h (L:=fun _=> (1:Side)) (b:=b) (c:=c) (G:=G) 0 (show x ≤ (if c then 1 else 0) + (↑(0:ℕ):ℝ) from (by simpa only [ Nat.cast_zero, add_zero ] using hx) ); rwa [gain0,mul_one] at ht
end YM.MS.Vista
