import YM.Integration.WilsonOriginalGeneralRosterHomeLedger
import YM.Integration.WilsonOriginalGeneralRosterHomeBank

/-! Every weak, pooled or mixed source receives its genuine original
station quota. The public campus has paid both branches before cutoff and
geometry, while the original label frame counts the columns at that station. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalGeneralRosterHomeAllSources
open Function Filter Set Finset Lattice RG Wilson Source Labels Climb Trace.Pilot Extraction Table Spec PhysMS
open WilsonLimitConstruction PhysicalNext.Repeat.Legato GapsContact GapsContact.Ascent Pert.Asymptotics
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMovingForkOpticalBook (reporter)
open WilsonReflectedPublicStationFare (station fee)
open WilsonOriginalObservedRoseMeshHeight (variation)
open WilsonOriginalObservedRosePooledWrap (allowance)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{o:Extraction.Order}{S:Table R.family.book}(F:Final R.family o S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][Nonempty I]{D T:ℕ}{δ:ℝ}
local notation "β" => R.family.path.levels.clock.hatBeta

def cost (R:Run G)(d:ℕ)(pay:ℝ):ℝ:= (2*orbitCost (R.family.labels.level d)*allowance R d)*pay

theorem original {axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}{simple:G.Simple}
    {campaign:Campaign R}{pillars:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign pillars)
    (bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)(h:ℕ)(d:I→Fin (D+1))
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)(before:ℕ):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∀(M:I→ℝ)(E:I→ℕ),(∀i,1≤M i)→
    (∀mode:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>field i s mode) M E ρ f)→
    ∀(n:ℕ)(tag:Fin n→I)(mode branch:Fin n→Bool),
    let k:=fun i=>(d (tag i)).val
    let book:=fun i=>books (ρ (tag i))
    let L:=fun i=>(book i).rows (d (tag i))
    let v:=fun i=>field (tag i) (ρ (tag i)) (mode i) (branch i)
    ∀i,let j:=station F (L i) (branch i)
      before≤j ∧ j≤f ∧ ∀(N per K:ℕ),j<N→f≤K→
      variation R k j N per i (((L i).arm (branch i) (v i)).source (N,per)) ≤
        cost R (k i) (M (tag i))*(β K)^(E (tag i)+1):=by
  classical
  obtain ⟨onset,columns⟩:=eventually_atTop.mp (WilsonReflectedOpticalStock.columns R simple slow)
  filter_upwards [WilsonAddressedMixedStationRange.original F simple bliss slow D T h (max before onset) d books] with r dates
  intro ρ range root f M E positive cash n tag mode branch k book L v i j
  have dated:=(dates ρ range root).2 (tag i) (branch i)
  refine ⟨(le_max_left ..).trans dated.1,dated.2.1,?_⟩
  intro N per K live top
  have growth:=WilsonReflectedOpticalStock.monotone R simple
  have stock:(R.family.path.levels.params j).columns≤β K:=
    (columns j ((le_max_right ..).trans dated.1)).trans (growth (dated.2.1.trans top))
  have receipt:=(WilsonReflectedPublicStationFare.original F (L i) (book i).checked (branch i) (v i)).2 N per live
  have salary:fee F (L i) (branch i) (v i)≤M (tag i)*(β K)^(E (tag i)):=
    ((cash (mode i) (tag i) (branch i)).2.1).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (R.family.path.levels.fits.delayed f).le) (growth top) _)
      (zero_le_one.trans (positive (tag i))))
  have cap(a:ℕ):(R.family.path.levels.budget a).supportExponent≤100:=by rw [paid.support]
  have margin:0≤2*orbitCost (R.family.labels.level (k i))*allowance R (k i):=mul_nonneg
    (mul_nonneg (by norm_num) (zero_le_one.trans (orbitCost_one_le _)))
    (zero_le_one.trans (WilsonOriginalObservedRosePooledWrap.positive R (k i)))
  calc
    _≤(2*orbitCost (R.family.labels.level (k i))*allowance R (k i))*(β K)*fee F (L i) (branch i) (v i):=
      WilsonOriginalObservedRosePooledWrap.original R k i j N per K _ (cap _) stock receipt
    _≤(2*orbitCost (R.family.labels.level (k i))*allowance R (k i))*(β K)*(M (tag i)*(β K)^(E (tag i))):=
      mul_le_mul_of_nonneg_left salary (mul_nonneg margin (zero_le_one.trans (R.family.path.levels.fits.delayed K).le))
    _=_:=by unfold cost;rw [pow_succ];ring

end YM.Integration.WilsonOriginalGeneralRosterHomeAllSources
end
