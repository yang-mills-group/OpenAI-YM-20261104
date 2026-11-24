import YM.FVA2.RateC
import Mathlib.RingTheory.PowerSeries.Expand
/-! # Position-independent relation between g_* and κ with polynomial coefficients in the logarithm
The relation is actually from the comparison theorem, not assumed. We include Taylor authority
(includes positivity and poles) as used by `ThePitch`, not a regulator-by-regulator customer.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Clock
open Function Filter Set MS MS.Land MS.Landau MS.Logarithm MS.High MS.Tide MS.Menus
open Pert Maxwell Maxwell.Free Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet MS.Book MS.Book.Program
open Panel ColorCode Forge Forge.Parity BoxOffice WorldJet Elegant MS.Book.Convolve PowerSeries
open scoped BigOperators Classical Topology ContDiff
variable {G:Gauge}(V: Warehouse G){h:G.Simple}{B: Booked (wings G)}(M:MS_Data G B){p:ℝ}(R:Booth p V.F){s:ℝ}{n m d:ℕ}
variable (P:Land.Prescription (wings G))(HS: Blaze.ExactSpin V P)(HU:Frost.Trusted P) (H: MixedStory.AllProfiles M V P)
variable {q:ℕ+}(hq:1<q.val) (A:Knocker h R q hq ( BoxOffice.warehouse V )) (p:Team)
-- in real polynomials of log parameter. exact Root(λ)=1 no ambiguity.
abbrev PaperLog := PowerSeries (Polynomial ℝ)
def looped (p:Team) : PaperLog := PowerSeries.mk fun j=> if j=0 then 1 else (p (2*j+1)).coupling
def κlog := invOfUnit (looped p ^ 2) 1
lemma log_init : constantCoeff (looped p)=1:= by simp [looped, ← coeff_zero_eq_constantCoeff_apply ]
lemma constantκ : constantCoeff (κlog p)=1:= by simp [κlog]
lemma square_κ : κlog p* (looped p)^2=1:= invOfUnit_mul _ _ (by rw [ map_pow,log_init,one_pow ]; rfl) -- parse
abbrev expanded (x:ℝ)(p:PaperLog):PowerSeries ℝ := expand 2 (by decide) (PowerSeries.map (Polynomial.evalRingHom x) p)
lemma log_is (x:ℝ) (n:ℕ) (p:PaperLog): coeff (2*n) (expanded x p)=(coeff n p).eval x:= ( coeff_expand_mul .. ).trans ( coeff_map .. ) -- ambiguous
lemma κ_spec (x:ℝ): expanded x (κlog p)*expanded x (looped p)^2=1 ∧ constantCoeff (expanded x (κlog p))=1 ∧ constantCoeff (expanded x (looped p))=1:= by unfold expanded; rw [ ← map_pow, ← map_pow (PowerSeries.map _), ← map_mul, ← map_mul, square_κ,map_one,map_one ]; rw [constantCoeff_expand,constantCoeff_expand ]; simp only [← coeff_zero_eq_constantCoeff_apply,coeff_map]; rw [coeff_zero_eq_constantCoeff_apply,coeff_zero_eq_constantCoeff_apply, constantκ,log_init,map_one ]; simp -- maybe simp map
include H HS HU A
lemma price_g (x:ℝ): Clock.rate P.team x=X*expanded x (looped P.team):= by
    let X₁ (j:ℕ):= Plot.coupling_e V M R P HS HU H hq A j; apply PowerSeries.ext; intro i; rcases i with _|i; · rw [rooted, coeff_zero_eq_constantCoeff_apply ]; simp
    rw [coeff_succ_X_mul]; by_cases ht:2 ∣ i
    · obtain ⟨u,rfl⟩:=ht; rw [log_is ]; unfold Clock.rate looped; by_cases hu:u=0; simp [hu]; simp only [coeff_mk,if_neg (show 2*u+1≠0 from (by omega)),if_neg (show 2*u+1≠1 from (by omega)),if_neg hu ]
    have hp:Even (i+1):= even_iff_two_dvd.mpr (by omega); rw [show coeff (i+1) (Clock.rate P.team x)=0 from Plot.parity0 ( Plot.clockParity V M R P HS HU H hq A x ) _ hp, expanded, coeff_expand_of_not_dvd _ _ _ ht ]
lemma implementation (x:ℝ): expanded x (κlog P.team) * Clock.rate P.team x ^2=X^2:= by rw [price_g V M R P HS HU H hq A , mul_pow, mul_left_comm, (κ_spec ..).1,mul_one]
end YM.FVA2.Clock
