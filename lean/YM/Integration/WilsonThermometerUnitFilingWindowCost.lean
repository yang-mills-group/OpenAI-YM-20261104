import YM.Integration.WilsonThermometerUnitFilingWindowRates

/-! Sum the fixed-grade chart costs on the actual short interval, including the native lower reporting shift. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWindowCost
open Function Filter Finset Real Lattice Wilson RG PhysicalNext PhysicalNext.Repeat Legato Pert.Asymptotics
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (simple:G.Simple)
local notation "C" => R.family
local notation "hat!" i:max => (C).path.levels.clock.hatBeta i
local notation "σ" => (C).S.scale

def order (q d:ℕ):ℕ:=q+2*(d+1)
def price (q d:ℕ) (K:ℝ):ℝ:=(2*(5*K+2)/Real.log 2)*8^(order q d)*2^(d+1)

include simple in
theorem original : ∃u:ℕ,∀{K:ℝ},0≤K → ∀ᶠ b:ℕ in atTop,∀v:ℕ,u≤v → v≤b →
    σ b-σ v ≤ K*Real.log (4*(hat! b))+(1+Real.log (hat! b)) →
    ∀N per:ℕ,b<N → ∀ q d:ℕ,
      ∑j∈Ico v b,(hat! j)^d*(regulatorRun C N per (j-1))^(order q d) ≤
        price q d K*(regulatorRun C N per (b+1))^q:=by
  obtain ⟨u,windows⟩:=WilsonThermometerUnitFilingWindowRates.original R simple
  refine ⟨u,?_⟩
  intro K kp
  filter_upwards [windows K kp] with b paid
  intro v start vb short N per live q d
  obtain ⟨runpos,thermal,counts,adjacent⟩:=paid v start vb short N per live
  let g:=regulatorRun C N per (b+1)
  have gp:0≤g:=runpos.le
  have hatp:0 ≤ hat! b:=zero_le_one.trans ((C).path.levels.fits.delayed b).le
  have countp:0 ≤ 2*(5*K+2)/Real.log 2:=by positivity
  have big:0 ≤ (hat! b)*g^2:=mul_nonneg hatp (sq_nonneg _)
  have localpay:∀j∈Ico v b,(hat! j)^d*(regulatorRun C N per (j-1))^(order q d) ≤
        ((hat! b)^d*8^(order q d))*g^(order q d):=by
    intro j hj
    have exactRoute:=adjacent j hj
    have loan:=pow_le_pow_left₀ exactRoute.1 exactRoute.2 (order q d)
    rw [mul_pow] at loan
    have resident:=pow_le_pow_left₀ (zero_le_one.trans ((C).path.levels.fits.delayed j).le)
      (WilsonThermometerUnitFilingWindowRates.increasing R simple (mem_Ico.mp hj).2.le) d
    calc _ ≤ (hat! b)^d*(8^(order q d)*g^(order q d)):=
           mul_le_mul resident loan (pow_nonneg exactRoute.1 _) (pow_nonneg hatp _)
         _=_:=by ring
  have lift:0 ≤ ((hat! b)^d*8^(order q d))*g^(order q d):=by positivity
  calc ∑j∈Ico v b,(hat! j)^d*(regulatorRun C N per (j-1))^(order q d) ≤
        ∑_j∈Ico v b,((hat! b)^d*8^(order q d))*g^(order q d):=sum_le_sum localpay
       _=((Ico v b).card:ℝ)*(((hat! b)^d*8^(order q d))*g^(order q d)):=by simp
       _≤ ((2*(5*K+2)/Real.log 2)*(hat! b))*(((hat! b)^d*8^(order q d))*g^(order q d)):=
            mul_le_mul_of_nonneg_right counts lift
       _= (2*(5*K+2)/Real.log 2)*8^(order q d)*(((hat! b)*g^2)^(d+1))*g^q:=by
            simp only [order,pow_add,mul_pow,pow_mul,pow_one];ring
       _≤price q d K*g^q:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ big thermal _) (mul_nonneg countp (by positivity))) (pow_nonneg gp _)

end YM.Integration.WilsonThermometerUnitFilingWindowCost
