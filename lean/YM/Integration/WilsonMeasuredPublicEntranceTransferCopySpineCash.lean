import YM.Integration.WilsonOriginalPublicTrialPhaseSpine
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyWidthStream

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopySpineCash
open Filter Real Lattice Wilson RG PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Bandage
open WilsonOriginalPublicTrialPhaseSpine (capital)
open WilsonOriginalPublicTrialPhaseLanding (first)
variable {G:Gauge}(R:Run G)(simple:G.Simple)
local notation "S" => R.family.S
local notation "H" i:arg => R.family.path.levels.clock.hatBeta i

def stock (T:ℝ)(e:ℕ):ℝ:=1+2*T*(2:ℝ)^e

theorem native {c K:ℕ}{d D A e:ℕ}{C B:ℝ}(dD:d≤D)
    (hp:0≤C)(bp:0≤B)(heat:H K≤2*H c)(span:(S).a c/(S).a K≤(H c)^A)
    (funded:B≤C*(H K)^e)(i:ℕ)(ci:c≤ i)(ik:i≤K):
    1+2*|capital (S) d K i B|≤ stock C e*(H c)^(A*(D+4)+e):=by
  have one:1≤H c:=(R.family.path.levels.fits.delayed c).le
  have kh:0≤H K:=zero_le_one.trans (R.family.path.levels.fits.delayed K).le
  have hh:0≤H c:=zero_le_one.trans one
  have anti:Antitone (S).a:=antitone_nat_of_succ_le (fun j=>by
    rw [(S).a_step];apply div_le_self ((S).a_pos j).le;exact_mod_cast ((S).block j).property)
  have big:1≤(S).a i/(S).a K:=(one_le_div ((S).a_pos K)).mpr (anti ik)
  have ratio:(S).a i/(S).a K≤(H c)^A:=
    (div_le_div_of_nonneg_right (anti ci) ((S).a_pos K).le).trans span
  have factor:((S).a i/(S).a K)^(d+4)≤(H c)^(A*(D+4)):=by
    rw [pow_mul]
    exact (pow_le_pow_right₀ big (by omega : d+4≤D+4)).trans
      (pow_le_pow_left₀ (zero_le_one.trans big) ratio _)
  have salary:B≤C*((2:ℝ)^e*(H c)^e):=by
    rw [←mul_pow]
    exact funded.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ kh heat _) hp)
  have use:=mul_le_mul factor salary bp (pow_nonneg hh _)
  have h1:1≤(H c)^(A*(D+4)+e):=one_le_pow₀ one
  have pos:0≤capital (S) d K i B:=mul_nonneg (pow_nonneg (zero_le_one.trans big) _) bp
  rw [abs_of_nonneg pos]
  dsimp only [capital,stock]
  rw [pow_add (H c) (A*(D+4)) e]
  rw [pow_add] at h1
  nlinarith only [use,h1]

include simple in
theorem original {c K:ℕ}(ck:c+1≤K)(d D A e:ℕ)(dD:d≤D)(C B:ℝ)
    (cp:0≤C)(bp:0≤B)(heat:H K≤2*H c)(span:(S).a c/(S).a K≤(H c)^A)
    (norm:B≤C*(H K)^e)(w:ℕ→ℝ)(start:(w K)⁻¹≤B)
    (positive:∀j,c+1≤j→j≤K→0<w j)
    (file:∀j,c+1≤j→j<K→w j=renal R.family.path.levels j*first (w (j+1)) (capital (S) d K j B)):
    (w (c+1))⁻¹≤(4*(H c)^2)^(K-(c+1))*(stock C e*(H c)^(A*(D+4)+e)):=by
  have one:1≤H c:=(R.family.path.levels.fits.delayed c).le
  have sale:=native R (c:=c) (K:=K) dD cp bp heat span norm
  have bill:=sale K (by omega) le_rfl
  rw [WilsonOriginalPublicTrialPhaseSpine.capital_base,abs_of_nonneg bp] at bill
  have top:=start.trans (show B≤ stock C e*(H c)^(A*(D+4)+e) by linarith only [bill,bp])
  have actual:=WilsonMeasuredPublicEntranceTransferCopyWidthStream.original R.family.path.levels (c+1) K ck
    w (fun j=>capital (S) d K j B) _ (2*H c) (by linarith only [one]) positive top
    (fun j low high=>sale j (by omega) high.le)
    (fun j _ high=>(WilsonStartup.Timing.hat_mono R.family.path.levels
      (Gauge.slopeConstant_pos simple).le (by omega:j+1≤K)).trans heat) file
  simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using actual
end YM.Integration.WilsonMeasuredPublicEntranceTransferCopySpineCash
end
