import YM.Integration.WilsonPublicOutputSmooth
import YM.Integration.WilsonPublicOutputFrame

/-! One reflected family for every requested two-scale accuracy. The outer
source is the original physical field on its own date. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicForkTightPivot
open Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits PhysMS Trace.Pilot Climb
open FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Theater
open RG12 SharpGram OPE.Log PhysicalNext.Repeat.Legato
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open WilsonMatrixTicketLanesSmearedPivot WilsonMacroscopicRichPositionRows
open WilsonMacroscopicRichSignedAmplitude WilsonMSDictionaryVector

open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)

theorem original {Y:(Bel R.family.book).Hierarchy}
    (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(simple:G.Simple)(h:ℕ):
    ∃ B:Profiles R h,∃w:B.probes.index→Atom (R:=R) h,
    ∃issued:∀j,B.probes.shell j=WilsonMatrixTicketLanesTwoSites.shell R.family.book.grid h (w j),
    ∀ε:ℝ,0<ε →∃K:ℝ,0≤K ∧ ∀g:ℝ→ℝ,Coupling G g → ∀m:ℕ,∀ᶠr in trail,
      let ρ:=((g r)^m)^2
      let t:=r/ρ
      ∃tp:0<t,∀y:S.Field h,
      ‖(homogeneous F J Z r h).symm y‖ ≤ K*ρ^(-(h:ℝ)-ε)*
        ‖fun j=>(WilsonPublicOutputSmooth.exterior F J Z B w issued tp j).charge F h y‖:=by
  obtain ⟨B,offered,measured⟩:=WilsonMacroscopicRichTwoDatePivot.original F J Z lead owed simple h
  choose w issued using offered
  refine ⟨B,w,issued,fun ε ep=>?_⟩
  obtain ⟨K,kp,decoder⟩:=measured ε ep
  refine ⟨2*K,by positivity,fun g hg m=>?_⟩
  have towards:Tendsto (fun r=>r/((g r)^m)^2) trail trail:=by
    have equal:(fun r=>r/((g r)^m)^2)=WilsonThermometerWeakPairClock.scale g (m*2):=
      funext fun r=>by rw [WilsonThermometerWeakPairClock.scale,pow_mul]
    exact equal ▸ WilsonThermometerWeakPairClock.small simple g hg (m*2)
  filter_upwards [towards.eventually decoder,WilsonPublicOutputFrame.normalized F J Z lead owed simple h,
    hg.positive,length_rate.pos,(hg.conforms simple).eventually (ge_mem_nhds zero_lt_one)] with r paid field gp rp cap
  intro ρ t
  have sp:0<ρ:=pow_pos (pow_pos gp m) 2
  have tp:0<t:=div_pos rp sp
  have bounds:ρ∈Ioc (0:ℝ) 1:=⟨sp,pow_le_one₀ (pow_nonneg gp.le _) (pow_le_one₀ gp.le cap)⟩
  have close:ρ*t=r:=by dsimp only [t];field_simp [sp.ne']
  refine ⟨tp,fun y=>?_⟩
  have measured:=paid ρ bounds y
  rw [close] at measured
  have returns:(fun j=>(WilsonPublicOutputSmooth.exterior F J Z B w issued tp j).charge F h y)=
      row F J Z B t y:=funext fun j=>WilsonPublicOutputSmooth.charge F J Z B w issued tp y j
  rw [returns]
  exact (field y).trans ((mul_le_mul_of_nonneg_left measured zero_le_two).trans_eq (by ring))

end YM.Integration.WilsonPublicForkTightPivot
