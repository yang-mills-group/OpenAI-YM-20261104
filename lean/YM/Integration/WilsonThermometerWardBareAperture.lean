import YM.Integration.WilsonThermometerWardBareCourse
import YM.Integration.WilsonCapturedPrimaryWardGapAperture
import YM.Integration.WilsonOriginalAdjacentMicroscopicPrice

/-! The actual microscopic wages of the three Ward-corrected fields and their finite relative interval. -/
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWardBareAperture
open Function Filter Finset Lattice Wilson RG Labels Source Push Extraction RG12 RG17 Climb Trace.Pilot
open MergeProof Next.Extract PhysicalNext.Repeat.Legato PhysicalNext.Repeat Legato Bandage
open RG05Readout RG05Readout.Address WilsonThermometerOffsetTrajectory WilsonThermometerOwnOffsetField
open WilsonCapturedPrimaryActiveArms WilsonCapturedPrimaryWardGapAperture
open scoped Classical Topology
open YM.Next.Rank.Price
open private size_sc from YM.Next.RANK.Matrices
variable {G:Gauge} (R:Run G)
local notation "fam" => R.family
local notation "chip" d:max N:max p:max x:max => Next.Rank.Price.awake (fam) d N N p x
local notation "cost" d:max x:max => ((fam).labels.level d).coeffSize x

theorem coin {k N p d:ℕ} (Q:Emblems (fam) d) (live:k≤N) (ref:(fam).ref d≤N) (y:Palette (fam) d):
    let E:=WilsonCapturedPrimaryWardGapHome.column R (p:=p) Q live (((fam).S.a k:ℂ)^d • y)
    cost d (chip d N p E)=((fam).S.a k/(fam).S.a N)^d*
      cost d (finer Q live y (primaryLetter d)):=by
  intro E
  let T:=(fam).factory d N p
  let x:(fam).label d:=finer Q live y (primaryLetter d)
  have base:(T.entries N (T.terminal.symm E)).x=T.terminal.symm E:=(R.makes.calibrated d N p ref).bare_coord _
  have escort:T.terminal.symm E=((fam).S.a k:ℂ)^d • x:=by
    change T.terminal.symm (T.terminal _) = _
    rw [T.terminal.symm_apply_apply]
    exact congrFun ((finer Q live).map_smul (((fam).S.a k:ℂ)^d) y) (primaryLetter d)
  have val:chip d N p E=((((fam).S.a N:ℂ)^d)⁻¹*((fam).S.a k:ℂ)^d) • x:=by
    change (((fam).S.a N:ℂ)^d)⁻¹ • (T.entries N (T.terminal.symm E)).x=_
    rw [base,escort,smul_smul]
  rw [val]
  have real:‖(((fam).S.a N:ℂ)^d)⁻¹*((fam).S.a k:ℂ)^d‖=((fam).S.a k/(fam).S.a N)^d:=by
    rw [norm_mul,norm_inv,norm_pow,norm_pow,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg ((fam).S.a_pos N).le,Real.norm_of_nonneg ((fam).S.a_pos k).le,
      div_pow,div_eq_mul_inv,mul_comm]
  rw [size_sc,real]

theorem charged {n k N p:ℕ} (d:Fin n→ℕ) (sites:Fin n→Site ((fam).side N p))
    (S:Shelf (N:=N) (p:=p) R k d sites) (live:k≤N) (ref:∀i,(fam).ref (d i)≤N)
    (y:(i:Fin n)→Palette (fam) (d i)) (i:Fin n):
    cost (d i) (chip (d i) N p (exposed R d sites S live y i)) ≤
      ((fam).S.a k/(fam).S.a N)^(d i)*(stringCost (fam) live*size (y i)):=by
  rw [exposed,scaled,coin R (S.route i) live (ref i)]
  have entry:cost (d i) (finer (S.route i) live (y i) (primaryLetter (d i))) ≤
      size (finer (S.route i) live (y i)):=by
    rw [bill_group]
    exact Finset.single_le_sum (f:=fun j=>((fam).labels.level (kept j)).coeffSize (finer (S.route i) live (y i) j))
      (fun _ _=>Work.G08.size_nonneg _ _) (Finset.mem_univ (primaryLetter (d i)))
  exact mul_le_mul_of_nonneg_left (entry.trans ((S.receipt i).inverse le_rfl live le_rfl (y i)))
    (pow_nonneg (div_nonneg ((fam).S.a_pos _).le ((fam).S.a_pos _).le) _)

theorem band (ε:ℝ) (pos:0<ε):∀ᶠ k:ℕ in atTop,∀{n N p:ℕ}(d:Fin n→ℕ)(sites:Fin n→Site ((fam).side N p))
    (S:Shelf (N:=N) (p:=p) R k d sites)(live:k≤N)(_ref:∀i,(fam).ref (d i)≤N)(y:(i:Fin n)→Palette (fam) (d i))
    (i:Fin n),cost (d i) (chip (d i) N p (exposed R d sites S live y i)) ≤
      ((fam).S.a k/(fam).S.a N)^(d i)*(Real.exp (ε*((fam).S.scale N-(fam).S.scale k))*size (y i)):=by
  filter_upwards [string_paid (C:=(fam)) pos] with k budget
  intro n N p d sites S live ref y i
  exact (charged R d sites S live ref y i).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (budget N live) (size_ge _))
    (pow_nonneg (div_nonneg ((fam).S.a_pos _).le ((fam).S.a_pos _).le) _))
end YM.Integration.WilsonThermometerWardBareAperture
