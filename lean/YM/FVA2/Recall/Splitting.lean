import YM.FVA2.Recall.Cash
/-!
 # Contraction onto a fresh field frame

 Open-coarse-coordinate argument is an ACTUAL formal variable in these results.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint Euler PertExtension PertExtension.Series Radial GaussianScore
open scoped Classical Topology BigOperators ContDiff
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma boost_C (d:F→ₗ[ℝ] E)(p:Permit E) : boost d (C p)= C (Papers.translation d p):= PowerSeries.map_C ..
lemma boost_s (T:F→ₗ[ℝ] E)(p:Ticket E): constantCoeff (boost T p) = Papers.translation T (constantCoeff p):= by unfold boost; rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply ]; rfl
lemma essential (φ: Ticket E→+* Ticket F)(h:Neat φ)(hk:∀ p:ℝ,φ (roll p)=roll p){w:Ticket E}(hx:constantCoeff w=0)(he:constantCoeff (φ w)=0): exponential (φ w)= φ (exponential w):= by
 apply PowerSeries.ext; intro i; rw [acting he i i le_rfl,h (acting hx i) i le_rfl]; simp_rw [map_sum,map_mul,map_pow,hk]
variable (m: Move)
lemma exponent_p (w:Ticket E)(h:constantCoeff w=0): Move.walk m E ( exponential w )= exponential (Move.walk m E w):= (essential (Move.walk m E) m.neat m.fix h ( m.constantLead w|>.trans h )).symm
lemma exponent_w (d:F→ₗ[ℝ] E)(w:Ticket E)(h:constantCoeff w=0) : boost d ( exponential w ) = exponential ( boost d w ):= (essential (boost d) (neatC (Papers.translation d).toRingHom) ( OpenSlots.boost_c d ) h (by rw [boost_s,h,map_zero])).symm

namespace Move
variable [FiniteDimensional ℝ E]
def adjust (Q:E→ₗ[ℝ] Module.Dual ℝ E): Ticket E:= exponential (carry m.drift * C (Euler.fuel Q))
lemma zero_rise (Q:E→ₗ[ℝ] Module.Dual ℝ E) : constantCoeff (carry m.drift * C (Euler.fuel Q))=0:= by unfold carry; rw [ map_mul,←coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,m.drift0, map_zero,zero_mul]
variable {A:E→ₗ[ℝ] Module.Dual ℝ E} {B:F→ₗ[ℝ] Module.Dual ℝ F}
lemma folds [FiniteDimensional ℝ F] (d:F→ₗ[ℝ] E)(h:∀ x:F,A (d x) (d x)= B x x): boost d (adjust m A)= adjust m B:= by
 unfold adjust; rw [ exponent_w _ _ (zero_rise ..),map_mul,unsigned,boost_C ]; rw [show Papers.translation d (fuel A)= fuel B from (?_ : _)]; apply Subtype.ext; funext x; change (fuel A).val (d x)=_; simp_rw [heat,h]
lemma combined (Q P B:E→ₗ[ℝ] Module.Dual ℝ E)(h:∀ x:E,Q x x=P x x+B x x) : adjust m Q= adjust m P*adjust m B:= by
 unfold adjust; rw [ ← OpenSlots.compose_two _ _ (m.zero_rise P) (m.zero_rise B), ←mul_add,←map_add C, show fuel Q=fuel P+fuel B from ?_ ]; apply Subtype.ext; funext x; change _=(fuel P).val x+(fuel B).val x; simp_rw [heat,h,add_div]

section
open Facade OpenSlots.Quadratic
variable [MeasurableSpace E][BorelSpace E]
local notation "P"=> LinearMap.fst ℝ E F
local notation "Σ₀"=> LinearMap.snd ℝ E F
local notation "χ"=> m.walk (E×F)
local notation "Φ"=> m.walk F
local notation "d"=> Module.finrank ℝ E
-- `splitting` map around centered field

abbrev pure (L:Law E)(μ:Measure E)[μ.IsAddHaarMeasure] : Ticket (E×F) →+ Ticket F:= throughPrice (Papers.splitting L μ).toAddMonoidHom
variable (L:Law E)(μ:Measure E)[μ.IsAddHaarMeasure]
local notation "Γ"=> Move.pure (F:=F) L μ

lemma lowers_zero (p: Permit F)(q:Permit (E×F)): Papers.splitting L μ (Papers.right p * q)=p*Papers.splitting L μ q:= by
 apply Subtype.ext; funext x; change Papers.opening μ L (Papers.froze x _) = p.val x * Papers.opening μ L (Papers.froze x q); rw [map_mul, show Papers.froze x (( Papers.right (E:=E) ) p)= constant (p.val x) from ?_,← Paint.flash, map_smul]; rfl
 apply Subtype.ext; funext y; rw [Papers.froze_at]; rfl
lemma lowers_left (p: Permit E): Papers.splitting (F:=F) L μ (Papers.left p)= constant (Papers.opening μ L p):= by
 apply Subtype.ext; funext x; change Papers.opening μ L (Papers.froze x _) = _; rw [show Papers.froze (E:=E) (F:=F) x (Papers.left p)=p from Subtype.ext (funext (fun y=>Papers.froze_at ..)) ]; rfl -- tactic precision

lemma lowers (p:Ticket F)(q:Ticket (E × F)): Γ (boost Σ₀ p * q) = p * Γ q:= by
 apply PowerSeries.ext; intro i; unfold Move.pure; rw [tagThrough, coeff_mul, coeff_mul,map_sum]; unfold boost;
 apply Finset.sum_congr rfl; intro j _; rw [tagThrough,coeff_map]; exact lowers_zero L μ (coeff j.1 p) (coeff j.2 q)
lemma off (p:Ticket E): Γ (boost P p)= carry (input L μ p) := by apply PowerSeries.ext; intro i; unfold Move.pure boost input carry; rw [tagThrough,coeff_map,coeff_map,tagThrough]; exact lowers_left L μ (coeff i p)
lemma pays_pure (p:Ticket (E×F))(z:PowerSeries ℝ): Γ (carry z * p)= carry z * Γ p := tender ( Papers.splitting L μ ) _ _
section firing
local notation "Q"=> (boost P (Move.adjust m L.P))
local notation "T"=> (carry (E:=F) (m.p^d))
lemma pointing (x:Ticket E)(y: Ticket F)(A:Ticket (E×F)) (h:A= boost Σ₀ y * boost P x): Γ ( Q * χ A ) = T * Φ (Γ A):= by
 rw [ h, lowers L μ,off, map_mul χ, boots m (Σ₀), boots m (P),mul_left_comm, lowers L μ, ←map_mul (boost P),off, Move.adjust, Book.night L μ m x,_root_.map_mul,_root_.map_mul (Φ),m.carries]; ring -- unfold adjust
private lemma upward (p:Permit (E×F)): Γ ( Q*χ (C p))=T * Φ (Γ (C p)) := by
 induction Papers.integral_plan p using Submodule.span_induction with
 | mem x h=> obtain ⟨⟨x,y⟩,rfl⟩:=h; apply pointing m L μ ( C x ) ( C y ); rw [boost_C,boost_C,mul_comm, ←map_mul C]; rfl
 | zero=> simp only [map_zero,mul_zero]
 | add=> rename_i ih kh; simp only [map_add,mul_add,ih,kh]
 | smul=> rename_i t v hv h; rw [ Paint.flash ]; simp only [ _root_.map_mul C,show ∀ x:ℝ,C (constant (E:=E×F) x)=carry (C x) from fun _=> Eq.symm (PowerSeries.map_C ..), map_mul χ,Move.carries,mul_left_comm (Q) (carry (m.sponsor _)) ]; simp_rw [ pays_pure, h, map_mul Φ,m.carries, mul_left_comm (carry (m.sponsor _)) (T) ]; -- order
lemma exportL (x:Ticket (E×F)): Γ ( Q*χ x )= T * Φ (Γ x):= by
 refine recruit ((Γ).comp ((clothe Q).comp (χ).toAddMonoidHom)) ((clothe (T)).comp ((Φ).toAddMonoidHom.comp (Γ))) ( fun h=> keepsThrough (Papers.splitting L μ).toAddMonoidHom ( Through.mul (Through.refl Q) (m.neat h) )) (fun h=> Through.mul (Through.refl T) (m.neat (keepsThrough (Papers.splitting L μ).toAddMonoidHom h))) ?_ x
 intro k v; change Γ ( Q*χ (X^k*C v) )= (T)*Φ ( Γ (X^k * C v) )
 rw [ ← show carry (E:=E×F) ((X («R»:=ℝ))^k)= X^k from Eq.trans (map_pow ..) (congr_arg (· ^ k) (PowerSeries.map_X ..))]; simp_rw [ _root_.map_mul χ, Move.carries ]; rw [mul_left_comm, pays_pure L μ,upward, pays_pure,map_mul (Φ), Move.carries, mul_left_comm]
end firing
variable [FiniteDimensional ℝ F]

-- Apply the splitting identity to open-frame uptake under the price admissibility condition below.
variable (q: Quadratic (E×F))(p:(core q).RespectsPrice)
local notation "R"=> reduced q p
local notation "δ"=> uptake q μ p
local notation "W"=> carry ( m.p^d )

omit [FiniteDimensional ℝ F] in
lemma aside (A:Ticket (E×F)): δ A= Move.pure p.inner μ (boost (center q p) A):= by apply PowerSeries.ext; intro i; unfold uptake Move.pure; rw [tagThrough,tagThrough]; unfold boost; rw [coeff_map]; rfl
omit [MeasurableSpace E] [BorelSpace E] in
lemma sine : boost (center q p) (Move.adjust m q.P)= boost Σ₀ (Move.adjust m (R).P)*boost P (Move.adjust m (p.inner.P)) := by
 let a:= (drag (center q p) q).P; let u:=( drag Σ₀ R ).P; let v:= ( drag P (recordQ p.inner) ).P
 rw [m.folds _ (A:=q.P) (B:=a) (fun _=> rfl),m.folds _ (A:=(R).P) (B:=u) (fun _=>rfl), m.folds _ (A:=p.inner.P) (B:=v) (fun _=>rfl)]; refine m.combined a u v (fun ⟨x,y⟩=>?_); have h:= ordinary_square q p x y; unfold flourish at h; exact h.trans ( ( add_comm .. ).trans (congr_arg ((reduced q p).flourish y + ·) (congr_arg (fun L=> (L : E→ₗ[ℝ] Module.Dual ℝ E) x x) (decided (core q) p).symm)))
-- key result factoring slips
lemma receipt_u (v:Ticket (E×F)): uptake q μ p (Move.adjust m q.P * χ v)= carry (m.p^d) * Move.adjust m ( R ).P * Φ (uptake q μ p v):= by
 simp_rw [aside μ q p]; rw [_root_.map_mul (boost _),sine m q p,mul_assoc,lowers p.inner μ, ← m.boots, exportL, mul_comm (W),mul_assoc]; ring
end
end Move
end YM.FVA2.Recall
