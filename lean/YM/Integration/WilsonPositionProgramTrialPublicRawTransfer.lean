import YM.Integration.WilsonPositionProgramTrialPublicRawFare

/-! Cost of the actual covered transfer on all measured corners in the
original lattice coupling, with the unmarked transfer included. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicRawTransfer
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG17 PhysMS EveryPhase OPE.Orbits OPE.Log MS MS.Land FVA2 FVA2.Register Pert.Asymptotics
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntranceTransferLocatedPanel (cost)
open WilsonAddressedHomeDose (ceiling)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
variable (J:ℝ→tower S)(Z:WilsonPrescription G)
local notation "C₀" => R.family
local notation "β" => (C₀).path.levels.clock.hatBeta

theorem original {n:ℕ}[Nonempty (Fin n)](simple:G.Simple)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F J)
    (obeys:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (D T h:ℕ)(d:Fin n→Fin (D+1))(y:∀i,(Spin.comparator (C₀).book).Field (d i).val)
    (x:∀i,RG17.Free C₀ (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (admit:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃A:Fin n→ℝ,∃E:Fin n→ℕ,(∀i,1≤A i) ∧ ∀p:ℕ,∀ᶠr in trail,
    ∀ρ:Fin n→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r) →
    let f:=reporter F books ρ
    ∀(M:Fin n→ℝ)(_one:∀i,1≤M i)(q desired:ℕ),
    (∑i:↥(Stock.final (Fin n)).val,E i.val)+2*p≤q → 2*p≤desired →
    ∀(mode arm:Fin n→Bool),let name:=fun i v=>WilsonReflectedMixedMasterSchool.field F J Z D T d y x books i (ρ i) (mode i) v
    cost F d books ρ f q desired M name arm ≤
      ((∏i:↥(Stock.final (Fin n)).val,A i.val)+(∏i,ceiling (R:=R) (d i).val (M i)))*(wilson z r)^p:=by
  classical
  obtain ⟨A,E,one,rows⟩:=WilsonPositionProgramTrialPublicRawFare.original F J Z simple bliss slow lead obeys D T h d y x books admit
  refine ⟨A,E,one,?_⟩
  intro p
  let link:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [rows,WilsonOriginalTwoFlatPublicOuter.original F simple bliss p,link.positive] with r measured gp pos
  intro ρ span near f M own q desired enough rest mode arm name
  obtain ⟨i₀,eq⟩:=near
  have small:(C₀).S.a f≤r:=by
    have past:=WilsonMovingForkOpticalBook.station_le F books ρ i₀ (d i₀) true
    change (books (ρ i₀)).W.k≤f at past
    exact ((C₀).S.strictAnti.antitone past).trans (((WilsonReflectedPublicBulbBerth.mesh R _ (books (ρ i₀)).checked).trans (books (ρ i₀)).active.le).trans eq.le)
  have scale:((wilson z r)⁻¹)^p≤(β f)^(2*p):=by
    apply (mul_le_mul_iff_of_pos_left gp.1).mp
    simpa only [outer,mul_comm ((β f)^(2*p)) r] using gp.2.2 f small
  have rate:((β f)^(2*p))⁻¹≤(wilson z r)^p:=by
    simpa only [←inv_pow,inv_inv] using inv_anti₀ (pow_pos (inv_pos.mpr pos) p) scale
  let F₀:=↥(Stock.final (Fin n)).val
  let B:=∏i:F₀,A i.val
  let e:=∑i:F₀,E i.val
  let bill (i:Fin n):=Motion.orbitCost ((C₀).labels.level (d i).val)*charge F ((books (ρ i)).rows (d i)) f (arm i) (name i (arm i))
  have bp:1≤β f:=((C₀).path.levels.fits.delayed f).le
  have bpos:0<β f:=zero_lt_one.trans_le bp
  have product:(∏i:F₀,bill i.val)≤B*(β f)^e:=by
    calc
      _ ≤ ∏i:F₀,A i.val*(β f)^(E i.val):=Finset.prod_le_prod
        (fun i _=>mul_nonneg (zero_le_one.trans (Motion.orbitCost_one_le _)) (zero_le_one.trans (le_max_left ..)))
        (fun i _=>measured ρ span ⟨i₀,eq⟩ i.val (mode i.val) (arm i.val))
      _ = _:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have B₀:0≤B:=Finset.prod_nonneg fun i _=>zero_le_one.trans (one i.val)
  have heat:((β f)^desired)⁻¹≤(wilson z r)^p:=(inv_anti₀ (pow_pos bpos _) (pow_le_pow_right₀ bp rest)).trans rate
  have nonnegative (i:Fin n):0≤ceiling (R:=R) (d i).val (M i):=
    le_trans (mul_nonneg (by norm_num) (zero_le_one.trans (own i))) (le_max_left ..)
  unfold WilsonMeasuredPublicEntranceTransferLocatedPanel.cost
  rw [add_mul]
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left heat (Finset.prod_nonneg fun i _=>nonnegative i))
  calc
    (∏i:F₀,bill i.val)*((β f)^q)⁻¹ ≤ B*(β f)^e*((β f)^(e+2*p))⁻¹:=mul_le_mul product
      (inv_anti₀ (pow_pos bpos _) (pow_le_pow_right₀ bp enough))
      (inv_nonneg.mpr (pow_nonneg bpos.le _)) (mul_nonneg B₀ (pow_nonneg bpos.le _))
    _ = B*((β f)^(2*p))⁻¹:=by rw [pow_add,mul_inv_rev];field_simp [bpos.ne']
    _ ≤ _:=mul_le_mul_of_nonneg_left rate B₀

end YM.Integration.WilsonPositionProgramTrialPublicRawTransfer
end
