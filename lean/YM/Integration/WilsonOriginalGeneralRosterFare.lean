import YM.Integration.WilsonOriginalGeneralRosterScalar
import YM.Integration.WilsonOriginalGeneralRosterFile

/-! Restore the finite physical rotation and charge bill face by face before
comparing with the filed K product. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterFare
open PhysicalNext.Repeat.Legato Trace.Physical Trace.Physical.Germ
open Function Finset Set Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical.GermGraph Climb Maxwell Maxwell.Free GapsContact
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalGeneralRosterScalar (directPrice gap)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}{D T:ℕ}(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val){n:ℕ}(port:Fin n→I)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "g" => fun i:Fin n=>(d (port i)).val
local notation "modes" => Stock.census (Fin n)

def rotation (grades:Fin n→ℕ)(M:Fin n→ℝ)(f desired:ℕ)(s:(modes).Mode):ℝ:=
  (∏i∈s.val,Motion.orbitCost ((C).labels.level (grades i))*M i)*((β f)^desired)⁻¹

theorem bill (ρ:I→{s:ℝ//0<s ∧ s<δ})(f desired:ℕ)(weak:Fin n→Bool)(v:∀i,S.Field ((g) i))
    (s:(modes).Mode)(M:I→ℝ)(E:I→ℕ)(positive:∀i,1≤M i)
    (pay:∀i,WilsonOriginalTwoFlatPublicFare.charge F ((books (ρ (port i))).rows (d (port i))) f (weak i) (v i)
       ≤M (port i)*(β f)^(E (port i))):
    directPrice F d books port ρ f (desired+∑i,E (port i)) weak v s≤rotation (R:=R) (g) (M∘port) f desired s:=by
  let k(i:Fin n):=Motion.orbitCost ((C).labels.level ((g) i))
  let char(i:Fin n):=WilsonOriginalTwoFlatPublicFare.charge F ((books (ρ (port i))).rows (d (port i))) f (weak i) (v i)
  let cash:=∏i∈s.val,k i*M (port i)
  let charge:=∑i∈s.val,E (port i)
  have bk:1≤β f:=((C).path.levels.fits.delayed f).le
  have bp:=zero_lt_one.trans_le bk
  have kp(i:Fin n):0≤k i:=zero_le_one.trans (Motion.orbitCost_one_le _)
  have cashPos:0≤cash:=prod_nonneg fun i _=>mul_nonneg (kp i) (zero_le_one.trans (positive _))
  have total:(∏i∈s.val,k i*char i)≤cash*(β f)^charge:=by
    calc
      _ ≤ ∏i∈s.val,(k i*M (port i))*(β f)^(E (port i)):=by
        apply prod_le_prod
        · exact fun i _=>mul_nonneg (kp i) (zero_le_one.trans (le_max_left ..))
        · intro i _
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (pay i) (kp i)
      _ = _:=by rw [prod_mul_distrib,prod_pow_eq_pow_sum]
  have mask:charge≤∑i,E (port i):=Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have oneBill:(β f)^(desired+charge)≤(β f)^(desired+∑i,E (port i)):=
    pow_le_pow_right₀ bk (Nat.add_le_add_left mask desired)
  unfold directPrice rotation
  calc
    _ ≤ (cash*(β f)^charge)*((β f)^(desired+∑i,E (port i)))⁻¹:=
      mul_le_mul_of_nonneg_right total (inv_nonneg.mpr (pow_nonneg bp.le _))
    _ ≤ (cash*(β f)^charge)*((β f)^(desired+charge))⁻¹:=
      mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos bp _) oneBill) (mul_nonneg cashPos (pow_nonneg bp.le _))
    _ = _:=by change _=cash*((β f)^desired)⁻¹;rw [pow_add];field_simp [bp.ne']

def debit (grades:Fin n→ℕ)(M:Fin n→ℝ)(f desired:ℕ)(s:(modes).Mode):ℝ:=
  rotation (R:=R) grades M f desired s+WilsonOriginalGeneralRosterFile.price (R:=R) grades M f desired s

theorem nonneg (grades:Fin n→ℕ)(M:Fin n→ℝ)(one:∀i,1≤M i)(f desired:ℕ)(s:(modes).Mode):
    0≤debit (R:=R) grades M f desired s:=by
  have heat:0≤β f:=zero_le_one.trans ((C).path.levels.fits.delayed f).le
  have rate:=inv_nonneg.mpr (pow_nonneg heat desired)
  exact add_nonneg (mul_nonneg (prod_nonneg fun i _=>mul_nonneg (zero_le_one.trans (Motion.orbitCost_one_le _))
    (zero_le_one.trans (one i))) rate)
    (mul_nonneg (prod_nonneg fun i _=>(mul_nonneg zero_le_two (zero_le_one.trans (one i))).trans (le_max_left ..)) rate)

theorem receipt {f K N per u desired:ℕ}(fk:f<K)(cut:K≤N)(uf:u≤f)(file:Filed R (g) K)
    (Y:∀i,(C).label ((g) i))(turn:Fin n→Motion)(loc:Fin n→Site ((C).side f per))(s:(modes).Mode)(M:Fin n→ℝ)
    (front:‖gap (R:=R) d port uf (fk.trans_le cut) s Y turn loc‖≤rotation (R:=R) (g) M f desired s)
    (back:‖WilsonMeasuredPublicEntranceCutoffHearing.difference R (g) file fk.le cut (uf.trans fk.le) Y turn loc s‖≤
      WilsonOriginalGeneralRosterFile.price (R:=R) (g) M f desired s):
    ‖(C).omega N per (physical R (g) (N:=N) Y turn loc s)-
      actualTransport (C) (N:=N) (submitted R (g) (N:=N) file fk.le Y turn loc s) (uf.trans fk.le) 1‖
      ≤debit (R:=R) (g) M f desired s:=
  (norm_sub_le_norm_sub_add_norm_sub _ (actualTransport (C) (N:=N) (physical R (g) (N:=N) Y turn loc s)
    (uf.trans (fk.le.trans cut)) 1) _).trans (add_le_add front back)

end YM.Integration.WilsonOriginalGeneralRosterFare
end
