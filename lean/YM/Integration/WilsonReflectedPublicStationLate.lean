import YM.Integration.WilsonReflectedPublicStationSpan

/-! Both previously chosen reporting dates pass a prescribed finite floor at
small radius, uniformly over the actual dated physical pool. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicStationLate
open Lattice Wilson RG Source Extraction Maxwell Maxwell.Free RG05Readout
open PhysicalNext.Repeat.Legato FVA2 FVA2.Register MS MS.Land
open Function Filter Set Table Spec Climb GapsContact GapsContact.Seams OPE Trace.Pilot
open Next.Rank Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open scoped Topology Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) {l : Ultrafilter (ℕ×ℕ)} {z : Trace.Terrace.Arch R.family}
    {H : (Bel R.family.book).Hierarchy}
local notation "mesh" => R.family.S.a

theorem original (simple : G.Simple) (bliss : Bliss F l z H) (T floor : ℕ) :
    ∀ᶠ r in trail, ∀ {D d k : ℕ}
      {stock : Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {cap : d ≤ D} {W : Vane R.family k} {fits : D ≤ k} {U : Spin.change S d}
      (P : Pair F stock cap W fits U r), W.checked f H k → W.wheel.r = r →
      ∀ b : Bool, floor ≤ station F P b := by
  obtain ⟨c,cc,finance⟩ := WilsonThermometerUnitFilingFourPoolClock.invoice F simple bliss T
  have cp : 0 < c := zero_lt_one.trans_le cc
  have link := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have small : ∀ᶠ r : ℝ in trail, r ≤ mesh floor/c :=
    (ge_mem_nhds (div_pos (R.family.S.a_pos floor) cp)).filter_mono nhdsWithin_le_nhds
  filter_upwards [finance, small, self_mem_nhdsWithin, link.positive,
    (link.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r ready thin rp gp gu
  change 0 < r at rp
  intro D d k stock cap W fits U P check stamp
  have rc : r*c ≤ mesh floor := (le_div_iff₀ cp).mp thin
  let s := WilsonThermometerUnitFilingFourPoolShell.radius z T r
  let B := dock s^T
  let g := wilson z r
  have Bfee : B*g^(2*T) ≤ c := ready.2
  have last : g^4 ≤ 1 := pow_le_one₀ gp.le gu
  have rb : s*B ≤ mesh floor := calc
    _ = r*((B*g^(2*T))*g^4) := by dsimp only [s,WilsonThermometerUnitFilingFourPoolShell.radius,g];rw [pow_add];ring
    _ ≤ r*c := mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_right (mul_nonneg (pow_nonneg ready.1.le _) (pow_nonneg gp.le _)) last).trans Bfee) rp.le
    _ ≤ _ := rc
  let dept := stock.department d cap
  let slot := dept.print (0 : S.Field d)
  have eqj : slot.j = stock.j := (dept.dated _).1
  have late_of (j : ℕ) (hj : mesh j ≤ mesh floor) : floor ≤ j :=
    R.family.S.strictAnti.le_iff_ge.mp hj
  intro b
  cases b with
  | false =>
    apply late_of stock.j
    rw [←eqj]
    exact ((R.family.S.strictAnti.antitone slot.fore).trans slot.front.le).trans rb
  | true =>
    apply late_of W.k
    exact (WilsonReflectedPublicBulbBerth.mesh R W check).trans
      (stamp.le.trans ((le_mul_of_one_le_right rp.le cc).trans rc))

end YM.Integration.WilsonReflectedPublicStationLate
end
