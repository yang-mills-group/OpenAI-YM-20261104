import YM.Integration.WilsonReceivedChronologicalFixedRoseNormalizedTerms
import YM.Integration.WilsonOriginalOpticalCouplingBand

/-! The original cutoff charge on the elected public amplitudes at every occupied face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseCutoffSalary
open Function Filter Finset Lattice RG Wilson PhysicalNext.Repeat.Legato
open Pert.Asymptotics
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonAddressedHomeDose (ceiling)
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:ℕ}(R:Run G)(simple:G.Simple)(d:Fin n → ℕ)
local notation "H" i:max => R.family.path.levels.clock.hatBeta i

private theorem ceiling_pos (M:Fin n → ℝ)(one:∀i,1≤M i)(i:Fin n):
    0≤ceiling (R:=R) (d i) (M i):=by
  exact le_trans (by linarith only [one i]:0≤2*M i) (le_max_left _ _)

include simple in
private theorem cold {v f N per:ℕ}(vf:v≤f)(live:f≤N)
    (cold:2≤(regulatorRun R.family N per v)⁻¹):
    0<regulatorRun R.family N per v ∧ regulatorRun R.family N per v≤1 ∧
      (H f)⁻¹≤regulatorRun R.family N per v:=by
  let b:=R.family.path.β N per v
  have pos:0 < H v:=zero_lt_one.trans (R.family.path.levels.fits.delayed v)
  have band:(H v)/2≤b ∧ b≤2*(H v):=(R.makes.wilson.represents N per v (vf.trans live)).band
  have bp:0<b:=lt_of_lt_of_le (half_pos pos) band.1
  have root:0<Real.sqrt b:=Real.sqrt_pos.mpr bp
  have two:2≤Real.sqrt b:=by simpa only [regulatorRun,inv_inv] using cold
  have linear:Real.sqrt b≤b/2:=by
    nlinarith only [Real.sq_sqrt bp.le,mul_nonneg root.le (sub_nonneg.mpr two)]
  have old:Real.sqrt b≤H v:=linear.trans (by linarith only [band.2])
  have fresh:H v≤H f:=ActualCoarseStagePrice.hatBeta_mono R.family.path.levels simple vf
  exact ⟨inv_pos.mpr root,(inv_le_one₀ root).mpr (by linarith only [two]),inv_anti₀ root (old.trans fresh)⟩

include simple in
theorem original (M:Fin n → ℝ)(one:∀i,1≤M i):
    ∀ᶠ v:ℕ in atTop,∀{f K N per:ℕ}(_vf:v≤f)(fk:f≤K)(kn:K≤N)
    {requested pole t:ℕ}{B:ℝ}(panel:Panel R d N per f K fk kn requested pole t B),
    panel.M=M → ∀(s:Finset (Fin n)){r:ℝ},0≤r → r≤1 → ∀{p order:ℕ},p+1≤order →
      r^(∑i∈s,d i)*((∏i∈s,ceiling (R:=R) (d i) (panel.M i))*((H f)^order)⁻¹) ≤
        (regulatorRun R.family N per v)^p:=by
  let cap:=fun s:Finset (Fin n)=>∏i∈s,ceiling (R:=R) (d i) (M i)
  have nn:∀s,0≤cap s:=fun s=>Finset.prod_nonneg (fun i _=>ceiling_pos R d M one i)
  have allFaces:∀ᶠ v:ℕ in atTop,∀s:Finset (Fin n),∀N per:ℕ,v≤N →
      cap s≤(regulatorRun R.family N per v)⁻¹:=by
    exact Filter.eventually_all.mpr (fun s=>WilsonOriginalOpticalCouplingBand.cold R simple (cap s))
  filter_upwards [allFaces,WilsonOriginalOpticalCouplingBand.cold R simple 2] with v salary coldAt
  intro f K N per vf fk kn requested pole t B panel chosen s r rp ro p order level
  rw [chosen]
  let g:=regulatorRun R.family N per v
  have live:=fk.trans kn
  obtain ⟨gp,go,temperature⟩:=cold R simple vf live (coldAt N per (vf.trans live))
  have pos:0≤(H f)⁻¹:=(inv_pos.mpr (zero_lt_one.trans (R.family.path.levels.fits.delayed f))).le
  have source:cap s*g≤1:=by
    calc cap s*g ≤ g⁻¹*g:=mul_le_mul_of_nonneg_right (salary s N per (vf.trans live)) gp.le
         _=1:=inv_mul_cancel₀ gp.ne'
  have physical:((H f)^order)⁻¹ ≤ g^(p+1):=by
    rw [←inv_pow]
    exact (pow_le_pow_left₀ pos temperature order).trans (pow_le_pow_of_le_one gp.le go level)
  have invoice:cap s*((H f)^order)⁻¹≤g^p:=by
    calc cap s*((H f)^order)⁻¹ ≤ cap s*g^(p+1):=mul_le_mul_of_nonneg_left physical (nn s)
         _=(cap s*g)*g^p:=by rw [pow_succ];ring
         _≤1*g^p:=mul_le_mul_of_nonneg_right source (pow_nonneg gp.le p)
         _=g^p:=one_mul _
  exact (mul_le_of_le_one_left (mul_nonneg (nn s) (inv_nonneg.mpr (pow_nonneg (by linarith only [R.family.path.levels.fits.delayed f]) _)))
    (pow_le_one₀ rp ro)).trans invoice

end YM.Integration.WilsonReceivedChronologicalFixedRoseCutoffSalary
