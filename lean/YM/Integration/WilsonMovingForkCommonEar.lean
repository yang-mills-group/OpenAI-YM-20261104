import YM.Integration.WilsonMovingForkGridHearing
import YM.Integration.WilsonOriginalTwoFlatPublicReindex

/-! One original flat pays every addressed phase comparison for the selected
full public product and every finite determining subrow on that same book. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkCommonEar
open Function Filter Finset Set Metric Lattice Extraction Table Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent Contacts.Mat WilsonSeparatedGridDesign WilsonSeparatedGridTree WilsonSeparatedBranchStencil
open OPE RG16 RG16.Literal RG17 FVA2 FVA2.Register MS MS.Land PhysicalNext.Repeat.Legato
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonReflectedPublicStationFare (station)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMovingForkHeterogeneousCut (Filed Heard Invoice)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}{l:Ultrafilter (ℕ×ℕ)}
  (J:ℝ → tower S)(Z:WilsonPrescription G){I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "a" => R.family.S.a

theorem original (order:(l:Filter _) ≤ f.fuse)(fac:Facilities R.family f S)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F H (J r) d)
    (D T B:ℕ)(d:I → Fin (D+1))(x:∀i,Free R.family (d i).val){δ η M:ℝ}(dp:0 < δ)(ep:0 < η)(mp:0 ≤ M)
    (books:(s:{s:ℝ // 0 < s ∧ s < δ}) → Book F (l:=l) H z D T s.val)
    (priced:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃J₀ u:ℕ,Stop R.family 0 J₀ u ∧ ∀P q:ℕ,∀face:Finset I,face.Nonempty →
    ∀n:ℕ,∀index:Fin n ≃ ↥face,∀E:Type,∀[Fintype E],
    ∃m:ℕ,∃C₀ D₀:ℝ,0 ≤ C₀ ∧ 0 < D₀ ∧ ∀ᶠr in trail,∀rp:0 < r,∀ρ:I → {s:ℝ // 0 < s ∧ s < δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z B r) → (∃i,(ρ i).val=r) →
      let j:=reporter F books ρ
      let dp:=div_pos (R.family.S.a_pos j) rp
      let select:=fun i:Fin n=>(index i).val
      let di:=fun i=>(d (select i)).val
      ∃_uj:u ≤ j,∀weak:Fin n → Bool,
      let v:=fun i=>homogeneous F J Z (ρ (select i)).val (di i) (x (select i))
      let book:=fun i=>(books (ρ (select i))).rows (d (select i))
      let arms:=fun i=>(book i).arm (weak i) (v i)
      ∀K:ℕ,∀jK:j ≤ K,∀b:Filed R di K,(∀i,b.station i=station F (book i) (weak i)) →
      ∀t c:ℕ,∀ut:u ≤ t,∀tc:t ≤ c,∀ck:c ≤ K,
      ∀pred:Points n → ℂ,∀w:Invoice,0 ≤ w.total t c K →
      let good:=fun o:Fin n → Cover=>(∀i,‖R.family.S.gridPoint j (o i)‖ ≤ (M+1)*outer z B r) ∧
        (Pairwise fun i k=>(η/2)*r ≤ ‖R.family.S.gridPoint j (o i)-R.family.S.gridPoint j (o k)‖)
      (∀o,good o → Heard (f:=f) b ut tc ck jK arms o pred w) →
      ∀ref:E → E4,∀X:Points n,(∀i,‖r • X i‖ ≤ M*outer z B r) → (∀i k,i≠k → η ≤ dist (X i) (X k)) →
      let prog:=sold m ref dp X
      let values:=fun y:Points n=>pred (r • y)
      (∀N per, K < N → ∀i,
        b.A N per i (WilsonMovingForkMixedSeed.doses R di b.station (N:=N) (per:=per) (b.A N per)
          (fun h=>(arms h).source (N,per)) i)=WilsonOriginalMicroscopicGuardedPage.full R (di i) N per
          (station F (book i) (weak i)) ((arms i).source (N,per))) ∧
      ‖S.classMoment S di (r • X) v-pred (r • X)‖ ≤ C₀*(∏i:Fin n,‖x (select i)‖)*(wilson z r)^P+
        (total n m E)^levels n*(D₀*(wilson z r)^q+w.total t c K)+‖read prog values-values X‖:=by
  obtain ⟨J₀,u,hstop,purchase⟩:=WilsonOriginalTwoFlatPublicSameField.selected F J Z fac bliss slow lead owed
    D T B d x (M:=M+1) (η:=η/2) (by linarith) (half_pos ep) dp books priced
  refine ⟨J₀,u,hstop,?_⟩
  intro P q face occupied n index E inst
  let select:=fun i:Fin n=>(index i).val
  obtain ⟨m,C₀,cn,grid⟩:=WilsonMovingForkGridHearing.original F J Z order fac.simpleGate bliss slow lead owed
    D T B d ep books select E P (M:=M)
  obtain ⟨D₀,positive,phase⟩:=WilsonOriginalTwoFlatPublicReindex.sampled F J Z fac.simpleGate D T B d x
    (M+1) (η/2) δ books u purchase q face occupied index
  refine ⟨m,C₀,D₀,cn,positive,?_⟩
  have gpos:=(wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies).positive
  filter_upwards [grid,phase,gpos] with r sites passed gp
  intro rp ρ span anchor j mesh selector di
  obtain ⟨uj,originalPhase⟩:=passed.2.2 ρ span anchor
  refine ⟨uj,?_⟩
  intro weak v book arms K jK b names t c ut tc ck pred w wn good wage ref X cost separate prog values
  apply sites rp ρ span anchor (fun i=>x (select i)) weak K jK b names u t c uj ut tc ck pred
    (D₀*(wilson z r)^q) w (add_nonneg (mul_nonneg positive.le (pow_nonneg gp.le _)) wn)
  · intro o h N per live
    exact (originalPhase N per live o h.1 h.2 weak).1
  · exact wage
  · exact cost
  · exact separate

end YM.Integration.WilsonMovingForkCommonEar
