import YM.Integration.WilsonIndependentCollarEngineeringClock
import YM.Integration.WilsonReceivedCanonicalVersePortfolio
/-! A single measured clock pays the restored public coordinate budget at every physical cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedPublicClock
open Finset Filter Function Lattice Wilson RG PhysicalNext.Repeat.Legato
open WilsonReceivedCanonicalVersePortfolio (Selection wallet)
open WilsonReceivedCanonicalVerseRegister (shoulder)
open ActualRunAdmissionScales OriginalBareMarkedInvoice Pert.Asymptotics
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)

def roof (A:ℕ):ℝ:=2*(1+2*G.slopeConstant*A)

theorem clock (simple:G.Simple)(A m K N per:ℕ)(live:m+1 ≤ N)
    (span:R.family.S.scale K-R.family.S.scale m ≤ (A:ℝ)*(1+Real.log (R.family.path.levels.clock.hatBeta (m+1)))):
    R.family.path.levels.clock.hatBeta K*(regulatorRun R.family N per (m+1))^2 ≤ roof (G:=G) A:=by
  let L:=R.family.path.levels
  let H:=L.clock.hatBeta (m+1)
  let β:=R.family.path.β N per (m+1)
  have pos:=Gauge.slopeConstant_pos simple
  have h1:1 ≤ H:=(L.fits.delayed _).le
  have beta0:0 < β:=Overlay.beta_positive R.makes.wilson live
  have lower:H/2 ≤ β:=(R.makes.wilson.represents N per (m+1) live).band.1
  have hit:H ≤ 2*β:=by linarith only [lower]
  have step:L.clock.hatBeta K=L.clock.hatBeta m+G.slopeConstant*(L.S.scale K-L.S.scale m):=by
    change _+_*L.S.scale K=(_+_*L.S.scale m)+_*(L.S.scale K-L.S.scale m);ring
  have later:L.clock.hatBeta m ≤ H:=by
    change _+_*L.S.scale m ≤ _+_*L.S.scale (m+1)
    exact add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono R.family.S).monotone (Nat.le_succ m)) pos.le) _
  have slow:1+Real.log H ≤ 2*H:=by linarith only [Real.log_le_self (zero_le_one.trans h1),h1]
  change L.clock.hatBeta K*(Real.sqrt β)⁻¹^2 ≤ _
  rw [inv_pow, Real.sq_sqrt beta0.le,←div_eq_mul_inv,div_le_iff₀ beta0]
  calc
    _ ≤ H+G.slopeConstant*((A:ℝ)*(2*H)):=by
      rw [step]
      exact add_le_add later (mul_le_mul_of_nonneg_left (span.trans
        (mul_le_mul_of_nonneg_left slow (Nat.cast_nonneg A))) pos.le)
    _ = (1+2*G.slopeConstant*A)*H:=by ring
    _ ≤ (1+2*G.slopeConstant*A)*(2*β):=mul_le_mul_of_nonneg_left hit (by positivity)
    _ = _:=by unfold roof;ring

theorem restored (k:Fin n → ℕ)(S:Finset (Fin n))(power target:ℕ)(B H g C:ℝ)(bp:0 ≤ B)(hp:0 ≤ H)(gp:0 ≤ g)
    (small:g ≤ 1)(bill:H*g^2 ≤ C):
    wallet R k (fun _=>B*H^power) S*g^(target+2*power*n) ≤
      wallet R k (fun _=>B*C^power) S*g^target:=by
  have shoulder₀ (j:Fin n):0 ≤ ∑z:WilsonThermometerDeclaredSeeds.Choice R k j,shoulder R k j z:=
    sum_nonneg (fun z _=>WilsonReceivedCanonicalVersePortfolio.nonneg R k j z)
  have size:S.card ≤ n:=by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have product:g^(2*power*S.card)=∏_j:S,(g^2)^power:=by
    rw [Finset.prod_const,Finset.card_univ,Fintype.card_coe,←pow_mul,←pow_mul,Nat.mul_assoc]
  have paid:wallet R k (fun _=>B*H^power) S * g^(2*power*S.card) ≤ wallet R k (fun _=>B*C^power) S:=by
    rw [product]
    unfold wallet
    rw [←prod_mul_distrib]
    apply Finset.prod_le_prod
    · exact fun i _=>mul_nonneg (mul_nonneg (shoulder₀ i) (mul_nonneg bp (pow_nonneg hp _))) (pow_nonneg (sq_nonneg _) _)
    · intro i _
      rw [mul_assoc,mul_assoc,←mul_pow]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hp (sq_nonneg _)) bill _) bp) (shoulder₀ i)
  have wp:0 ≤ wallet R k (fun _=>B*H^power) S:=
    prod_nonneg (fun i _=>mul_nonneg (shoulder₀ i) (mul_nonneg bp (pow_nonneg hp _)))
  calc
    _=wallet R k (fun _=>B*H^power) S*g^(2*power*n)*g^target:=by rw [pow_add];ring
    _≤(wallet R k (fun _=>B*H^power) S*g^(2*power*S.card))*g^target:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one gp small (Nat.mul_le_mul_left _ size)) wp) (pow_nonneg gp _)
    _≤_:=mul_le_mul_of_nonneg_right paid (pow_nonneg gp _)

end YM.Integration.WilsonReceivedChronologicalFixedPublicClock
end
