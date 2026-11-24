import YM.FVA2.Recall.Book
/-!
 # Moment scaling connection identity with exact shift and every $q$-power
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint Euler PertExtension PertExtension.Series Radial GaussianScore
open scoped Classical Topology BigOperators ContDiff
section linear
-- X-adic linear transformations on PS with vector coefficients.
variable {S R:Type}[CommRing S][Algebra ℝ S] [CommRing R][Algebra ℝ R]
variable (s: R →ₗ[ℝ] S)
abbrev pay (p:PowerSeries R) : PowerSeries S:= throughPrice s.toAddMonoidHom p
lemma pay_c (r:R): pay s (C r)=C (s r):= by apply PowerSeries.ext; intro i; unfold pay; rw [ Facade.tagThrough,coeff_C,coeff_C]; split; rfl; rw [map_zero]
lemma tender (q:PowerSeries ℝ)(p:PowerSeries R) : pay s (map (algebraMap ℝ R) q * p)= map (algebraMap ℝ S) q * pay s p:= by
 apply PowerSeries.ext; intro i; unfold pay; rw [Facade.tagThrough,coeff_mul,coeff_mul,map_sum]; apply Finset.sum_congr rfl; intro j _; rw [ Facade.tagThrough, coeff_map,coeff_map, ← Algebra.smul_def, ←Algebra.smul_def ]; exact s.map_smul _ _ -- pay use smul
abbrev clothe (Q:PowerSeries R): PowerSeries R →+ PowerSeries R:= AddMonoidHom.mulLeft Q -- check
omit [Algebra ℝ R] in
lemma neat_cl (p:PowerSeries R): Neat (fun x:PowerSeries R=> p*x):= fun h=> ( Through.refl p ).mul h
-- power roll is scalar series: X^k · a(b)
end linear

namespace Book
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable (L:Law E) [MeasurableSpace E][BorelSpace E] (μ:Measure E)[μ.IsAddHaarMeasure]
local notation "d"=> Module.finrank ℝ E
local notation "H"=> Euler.fuel L.P
local notation "Φ"=> Papers.opening μ L
local notation "Ω"=> input L μ
variable (v:Permit E)
theorem secured (x:PowerSeries ℝ)(z:Ticket E): Ω (carry x * z)=x * Ω z:= by
 change pay (Φ) ( map (algebraMap ℝ (Permit E)) x * z )=x * Ω z; rw [tender]; congr
lemma own : Ω ( C v )=C ( Φ v ):= pay_c ..
lemma rules (p:Ticket E)(x:ℝ) : Ω (roll x * p) = C x * Ω p:= by rw [ ← show carry (E:=E) (C x)=roll x from PowerSeries.map_C .. ]; exact secured ..
-- exact generating function in a formal parameter b with zero constant
variable (b:PowerSeries ℝ)(h:constantCoeff b=0)
local notation "φ"=> (carry (E:=E) b * C H)
include h
lemma book : input L μ (Stack.exponential (carry (E:=E) b * C (Euler.fuel L.P))* C v )= (Book.archive L μ v).subst b:= by
 have hx : constantCoeff φ=0:= by rw [map_mul,←coeff_zero_eq_constantCoeff_apply, carry,coeff_map,coeff_zero_eq_constantCoeff_apply,h,map_zero, zero_mul]
 apply PowerSeries.ext; intro i; rw [ show (coeff i (Ω (exponential φ * C v)))= _ from keepsThrough (Φ).toAddMonoidHom ((acting hx i).mul ( Through.refl (C v) )) i le_rfl, Position.AlignSeries.subst_finite h ]; -- syntax
 -- list proof
 change coeff i (Ω ((∑ j ∈ Finset.range (i+1), _ ) * _)) = ∑ j∈_,_
 rw [ Finset.sum_mul, _root_.map_sum, map_sum ]
 apply Finset.sum_congr rfl; intro j _; simp_rw [mul_pow,← map_pow, Book.archive_c ]; let z:=(( j.factorial:ℝ )⁻¹); change coeff i (Ω (roll z * ( carry (b^j) * C (H^j) ) * C v ))= (factor L μ v j)*( _ ); rw [mul_assoc, mul_assoc (carry (E:=E) _), ← map_mul C,rules,secured,own,coeff_C_mul, coeff_mul_C]; unfold factor; ring
omit h
variable (m:Move)
local notation "Φm"=> Move.walk m E
local notation "R"=> exponential ( carry m.drift * C ( Euler.fuel L.P ) )

lemma ridge : Ω ( R * service m.q E v )= m.p^d * C (Φ v):= by
 induction Paint.covers v using Submodule.span_induction with
 | mem v h=>
    obtain ⟨n,h⟩:=h
    rw [ service_value _ v h, ←map_pow (carry (E:=E)),mul_left_comm (R), secured, book L μ v m.drift m.drift0, m.climbs (d+n) _ (Book.climb L μ v h), archive_z,pow_add]
    rw [show m.q^n*( C (Φ v)*( m.p^d*m.p^n))= ( m.p^n*m.q^n ) * (m.p^d * C (Φ v)) from ?_]; -- set
    · rw [←mul_pow,m.old,one_pow,one_mul]
    ring
 | zero=> simp
 | add=> rename_i ih kh; simp only [_root_.map_add,mul_add,ih,kh]
 | smul=> rename_i r v _ hv;
          rw [ map_smul Φ, flash r v, map_mul (service m.q E), fixed_g, mul_left_comm (R) (roll (E:=E) r), rules,hv]; rw [smul_eq_mul,map_mul]; ring

lemma night (t:Ticket E): input L μ (R * Φm t)=m.p^d * m.sponsor (Ω t):= by
 refine recruit ((Ω).comp ((clothe (R)).comp ( Φm ).toAddMonoidHom )) (( clothe (m.p^d) ).comp ( m.sponsor.toAddMonoidHom.comp Ω )) ( fun k=> keepsThrough (Φ).toAddMonoidHom (Through.mul (Through.refl (R)) (m.neat k)) ) ( fun h=> Through.mul ( Through.refl _ ) (m.sponsor_neat (keepsThrough (Φ).toAddMonoidHom h)) ) ?_ t
 -- formal power series identity
 intro k v; change Ω (R * Φm _) = _ * m.sponsor (Ω _)
 let w:= (X («R»:=ℝ))^k  -- bad syntax repair
 have hp:X^k * C («R»:=Permit E) v=carry w * C v:= by unfold w; rw [map_pow,show carry (E:=E) X= X from PowerSeries.map_X ..]
 rw [hp, map_mul (Φm), m.carries, mul_left_comm (R), secured L μ, Move.walk_c,ridge, secured, map_mul m.sponsor, own,m.sponsor_c]; ring
end Book
end YM.FVA2.Recall
