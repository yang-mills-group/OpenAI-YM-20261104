import YM.AlbaMS.Inlay.Air
import YM.AlbaMS.Super.Shoe

/-! Weft maps to fixed order algorithm (nil, no hypothesis about coefficients except first).
The transformations act on individual fragments; sums use any root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Bric.Coil
open Set Function Finset
open scoped BigOperators Classical
variable {ι κ R S : Type*}[CommRing R][CommRing S]{ρ:ι→Bool}{σ:κ→Bool}{u:ℕ}{T:ι→κ→R}{H:Routes ρ σ T}{s:Finset ι}{F:Coil ρ R}
lemma shot_rank (n:ℕ): shot s T H (rankn n F)=rankn n (shot s T H F):=by
  ext l; induction l generalizing F n with|nil=> rw [shot_nil,rankn_read,rankn_read,shot_nil]; simp| cons i l ih=>
    rw [← D_read,shot_D]; obtain _|n:=n
    · simp_rw [rankn_read]; rw [drip_apply, ((rankn.heg F 0).cap _ _).eroded]; simp
    rw [drip_apply, map_sum]; simp_rw [D_rank,map_smul,sum_read,smul_read,ih]; rw [← D_read, D_rank, shot_D,drip_apply,map_sum,map_sum,sum_read]; simp_rw [map_smul, smul_read]
lemma weft_shot (A : ι→R)(B:κ→R)(h:∀ i∈s,∀ j,T i j*A i=T i j*B j): shot s T H (weft A F)=weft B (shot s T H F):=by
  ext l; induction l generalizing F with|nil=> simp only [shot_nil,weft_nil]|cons i l ih=>
    rw [← D_read, ← D_read (F:=weft B _),shot_D,weftD,shot_D]; simp_rw [drip_apply, map_sum, map_smul, Finset.smul_sum]; simp_rw [weftD,map_smul,sum_read]; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [smul_smul,smul_smul,mul_comm (B i),h j hj i]; rw [smul_read,smul_read,ih]
lemma Cap.weft (A:ι→R)(h:Cap F u): Cap (Coil.weft A F) u:=fun l ht=>h l fun hv=> ht (by simp [wefts,hv])
lemma loom_prec (z:R)(m:ℕ)(h:Heg u F): loom z m F=(z^(u-m)) • F:=by ext l; rw [looms,smul_read]; by_cases he:F l=0; simp [he]; rw [h l he]
lemma loom_zero (h:needy u F) : loom (0:R) u F=rankn u F:=by
  ext l; rw [looms, rankn_read]; by_cases he:l.length=u; · simp [he]
  rw [if_neg he]; by_cases ht:F l=0; · simp [ht]
  rw [zero_pow _,zero_mul]; have h:=h l ht; omega
lemma shot_wind (A:R→+*S)(h:Routes ρ σ fun i j=> A (T i j)):
    Wind σ A (shot s T H F)=shot s (fun i j=> A (T i j)) h (Wind ρ A F):=by
  ext l; induction l generalizing F with|nil=> rfl| cons i l ih=>
   rw [← D_read, ← D_read (F:=shot _ _ _ (Wind _ _ _)), shot_D];
   simp_rw [show ∀ x (F:Coil _ R),D x (Wind σ A F)=Wind σ A (D x F) from fun _ _=>rfl, shot_D,drip_apply,map_sum,map_smul,Wind_smul,sum_read,smul_read, ih]; rfl
end YM.MSBar.Bric.Coil
namespace YM.MSBar.Inlay
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {V W I J R : Type*}{G:Gauge}[CommRing R]
-- structured lattice calibration for this separate expansion. β conventional g_*⁻².
structure Tune (R:Type*)[CommRing R] where
  z : R
  A : Rˣ
  Gc : Rˣ
  D : ℝ →+* R
  a : ℝ
  ha : 0<a
namespace Tune
variable (P:Tune R)
def loomT : Leaf G V I→R:= Sum.elim (Sum.elim (fun _=>P.D P.a * P.A) (fun _=>P.D P.a ^ 2 * (↑(P.A⁻¹):R))) (Sum.elim (fun _=> P.D P.a* P.Gc) (fun _=>P.D P.a^2* (↑(P.Gc⁻¹):R)))
-- read full canonical power, specializing without considering rank cap
abbrev up (n:ℕ)(F:Heave G V I ℝ):Heave G V I R:= weft P.loomT (loom P.z n (Wind _ P.D F))
-- kinetic uses only `abiot` unflowed real basis and frame powers
protected def coul:=P.z * P.Gc
-- occupy scalar mesh with no perturbation. scale exists thru `ha`.
def baseT (x:ℝ)(h:0<x): Tune ℝ:=⟨0,1,1,RingHom.id ℝ,x,h⟩
def bracket (i j : Leaf G V I): R:= P.D (P.a⁻¹)^4 * Loft.oriented R i j
def original (i j : Leaf G V I):R:= Loft.oriented R i j
lemma prime : Graded (@ø (Flit G V) (Flit G I)) true P.bracket:=fun i j h=> lead i j (right_ne_zero_of_mul (a:=P.D P.a⁻¹^4) h)
lemma canonized (i j:Leaf G V I): P.bracket i j*P.loomT i*P.loomT j=P.D (P.a⁻¹)* P.D (Loft.oriented ℝ i j):=by
  have he : P.D (P.a⁻¹)*P.D P.a=1:=by rw [← map_mul, inv_mul_cancel₀ P.ha.ne',map_one]
  have ht (T:Rˣ): P.D P.a⁻¹^4 *(P.D P.a*T)*(P.D P.a ^2*(↑(T⁻¹):R))=P.D P.a⁻¹:=by
    have hd : P.D P.a⁻¹^4 *(P.D P.a*T)*(P.D P.a ^2*(↑(T⁻¹):R))=P.D P.a⁻¹ * ((P.D P.a⁻¹*P.D P.a)^3 * ((T:R)*↑(T⁻¹))):=by ring
    rw [hd,he, one_pow, Units.mul_inv,one_mul,mul_one]
  rcases i with (i|i)|(i|i) <;> simp only [Tune.bracket, Loft.oriented]
  · split_ifs with h; · rw [h,mul_one]; simpa [h,loomT,Place.k] using ht P.A
    simp
  · simp
  · split_ifs with h; · rw [h]; simpa [loomT,Place.l] using ht P.Gc
    simp
  simp
variable {Ω:Net V I}{H:Net W J}{F:Heave G V I ℝ}
lemma steer (u:Net.Receipt G Ω H): Routes ø ø (fun i j=> P.D (u.skein i j)):=fun i j h=>u.routed i j (fun hv=>h (by simp only [hv,map_zero])) -- should be lemma not def
variable [Fintype V][Fintype I]
def crossT (u:Net.Receipt G Ω H): Heave G V I R→ₗ[R]Heave G W J R:=shot Finset.univ (fun i j=>P.D (u.skein i j)) (P.steer u)
lemma commute (u:Net.Receipt G Ω H)(k:ℕ)(F:Heave G V I ℝ): P.crossT u (P.up k F) = P.up k (u.track F):=by
  have he i (_:i∈Finset.univ) j:P.D (u.skein i j)*P.loomT i=P.D (u.skein i j)*P.loomT j:=by rcases i with (i|i)|(i|i)<;> rcases j with (j|j)|(j|j)<;> first|rfl|(simp [Net.Receipt.skein])
  unfold crossT up; rw [weft_shot P.loomT P.loomT he, loom_change,← shot_wind P.D]; rfl

-- BV interaction with measure. stationarity `S(0)=0,...` comes from concrete model. use lemma.
def fuelT (F : Heave G V I ℝ) (J : Heave G V I ℝ):= P.up 2 F-P.up 0 J
def kinetic (a:ℝ)(h:0<a)(F:Heave G V I ℝ):= weft (baseT a h).loomT (rankn 2 F)
variable [Algebra ℚ R]
lemma liftT {J:Heave G V I ℝ}(h:Trad F J (Loft.oriented ℝ) Finset.univ): master P.bracket Finset.univ (P.fuelT F J)=0:=by
  have hp:= Trad.heatproof (ρ:=ø) P.D h lead P.z
  unfold master at hp ⊢; rw [fuelT,up,up, ← map_sub];
  simp_rw [weft_cross (g:=fun i j=> P.D (Loft.oriented ℝ i j)) _ (P.canonized), weft_touch (g:=fun i j=> P.D (Loft.oriented ℝ i j)) _ (P.canonized)]; rw [smul_comm (halve R), ← map_smul, ← smul_sub, ← map_sub,hp,map_zero,smul_zero] -- orientation
end Tune
end YM.MSBar.Inlay
