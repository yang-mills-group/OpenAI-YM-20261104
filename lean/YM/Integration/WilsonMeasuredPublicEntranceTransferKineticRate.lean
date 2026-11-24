import YM.Integration.WilsonMeasuredPublicEntranceTransferSurveyRate
import YM.Integration.WilsonMeasuredPublicEntranceTransferNamedReturn
import YM.Integration.WilsonMeasuredPublicEntranceTransferElectedFees
import YM.Integration.WilsonMeasuredPublicEntranceTransferSpent
/-! Genuine own-station and thermal-room costs on the signed cofinal survey, priced on both original regulator tails and at its named smooth continuum target. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferKineticRate
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Labels Cells
open Extra.Histories PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonReflectedPublicOrientedFaces (displayed)
open OPE Next.Rank Overlay Bid Push.GridApprox MergeProof Ribbons Accent ManyCopies
open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted physical)
open WilsonMeasuredPublicEntranceOrderedPins (Release publicValue)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open Table Climb Next.UVStress
open Extraction Spec PertExtension PertExtension.LatticePT Trace.Pilot Trace.Terrace
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open scoped Classical BigOperators Topology
open Trace.Physical.GermGraph (Opened)
open WilsonMeasuredPublicEntranceBookedSurvey (Press model)
open WilsonMeasuredPublicEntranceTransferProfileMass (tested phase size)
open WilsonMeasuredPublicEntranceTransferLocatedPanel (cost)
open WilsonMeasuredPublicEntranceBookedRegulators (moving)
open WilsonMeasuredPublicEntranceMarkedNode (turned field)
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
variable {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Arch R.family}
local notation "C₀" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonMeasuredPublicEntranceTransferKnotBoard (At)
open RG16 RG16.Literal PhysicalNext.Repeat.Mallow Bandage
local notation "full" => Stock.final (Fin n)




open WilsonMeasuredPublicEntranceTransferCampusSurvey (submittedWord)
variable {D T n:ℕ}{d:Fin n→Fin (D+1)}{e:Fin n→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val}
    {names:(i:Fin n)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:Fin n→ℝ}{E:Fin n→ℕ}{tuition:ℝ}{power target t:ℕ}
    {ρ:Fin n→{s:ℝ //0<s ∧ s<δ}}{f K j u apron q:ℕ}
    {m:ℕ}{B:Type}[Fintype B]{ref:B→E4}{φ:Test n}{r:ℝ}{rp:0<r}
local notation "grade" => fun i=>(d i).val


open WilsonMeasuredPublicEntranceTransferCofinalSurvey (Invoice)

open WilsonAddressedHomeDose (ceiling)
open WilsonMeasuredPublicEntranceTransferNamedReturn (Released)
open WilsonMeasuredPublicEntranceTransferSurveyRate (Paid)
open WilsonMeasuredPublicEntranceTransferLocatedPanel (cost)
open WilsonOriginalTwoFlatPublicFare (charge)

def amount (d:Fin n→Fin (D+1))(M:Fin n→ℝ):ℝ:=
  (∏i:↥(Stock.final (Fin n)).val,Motion.orbitCost ((C₀).labels.level (d i.val).val)*M i.val)+
   ∏i,ceiling (R:=R) (d i).val (M i)

theorem kinetic (f p N per:ℕ)(fine:f≤N):((β f)^p)⁻¹≤(2*(Pert.Asymptotics.regulatorRun (C₀) N per f)^2)^p:=by
  have hp:0<β f:=zero_lt_one.trans_le ((C₀).path.levels.fits.delayed f).le
  have actual:0<(C₀).path.β N per f:=Overlay.beta_positive R.makes.wilson fine
  have born: (C₀).path.β N per f≤2*β f:=(R.makes.wilson.represents N per f fine).band.2
  have first:(β f)⁻¹≤2*(Pert.Asymptotics.regulatorRun (C₀) N per f)^2:=by
    rw [Pert.Asymptotics.regulatorRun,inv_pow,Real.sq_sqrt actual.le,←one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ hp actual).mpr (by simpa only [one_mul] using born)
  rw [←inv_pow]
  exact pow_le_pow_left₀ (inv_nonneg.mpr hp.le) first p

theorem fees (name:∀i,Bool→S.Field (d i).val)(mode:Fin n→Bool)
    (read:(i:Fin n)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (eq:∀i,name i=read i (ρ i) (mode i))(one:∀i,1≤M i)
    (board:∀k:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>read i s k) M E ρ f)
    (p desired:ℕ)(source:(∑i:↥(Stock.final (Fin n)).val,E i.val)+p≤q)(room:p≤desired)(b:Fin n→Bool):
    cost F d books ρ f q desired M name b≤amount (R:=R) d M*((β f)^p)⁻¹:=by
  classical
  have bp:1≤β f:=((C₀).path.levels.fits.delayed f).le
  have hp:0<β f:=zero_lt_one.trans_le bp
  let S:=(Stock.final (Fin n)).val
  let O:=fun (i:Fin n)=>Motion.orbitCost ((C₀).labels.level (d i).val)
  let money:=fun i=>charge F ((books (ρ i)).rows (d i)) f (b i) (name i (b i))
  let A:=∏i:↥S,O i.val*M i.val
  let E':=∑i:↥S,E i.val
  have op(i):0≤O i:=zero_le_one.trans (Motion.orbitCost_one_le _)
  have nonneg(i):0≤O i*money i:=mul_nonneg (op _) (zero_le_one.trans (le_max_left ..))
  have each(i):O i*money i≤(O i*M i)*(β f)^(E i):=by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (op i)
    dsimp only [money]
    rw [eq i]
    exact (board (mode i) i (b i)).2.2
  have ap:0≤A:=Finset.prod_nonneg fun i _=>mul_nonneg (op _) (zero_le_one.trans (one _))
  have amt:(∏i:↥S,O i.val*money i.val)≤A*(β f)^E':=by
    calc _ ≤ ∏i:↥S,(O i.val*M i.val)*(β f)^(E i.val):=Finset.prod_le_prod (fun i _=>nonneg _) (fun i _=>each _)
         _ = _:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  have base:(∏i:↥S,O i.val*money i.val)*((β f)^q)⁻¹≤A*((β f)^p)⁻¹:=by
    calc _ ≤ (A*(β f)^E')*((β f)^(E'+p))⁻¹:=mul_le_mul amt
               (inv_anti₀ (pow_pos hp _) (pow_le_pow_right₀ bp source)) (inv_nonneg.mpr (pow_nonneg hp.le _)) (mul_nonneg ap (pow_nonneg hp.le _))
         _ = _:=by rw [pow_add,mul_inv_rev];field_simp [hp.ne']
  have ro:0≤∏i,ceiling (R:=R) (d i).val (M i):=Finset.prod_nonneg fun i _=>
        (mul_nonneg (by norm_num) (zero_le_one.trans (one i))).trans (le_max_left ..)
  unfold cost amount
  rw [add_mul]
  exact add_le_add base (mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hp _) (pow_le_pow_right₀ bp room)) ro)

theorem original (P:Press R φ r rp f m ref)(mode:Fin n→Bool)
    (read:(i:Fin n)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    (past:u≤j)(height:j+2≤f)(marked:Fin n→Bool)(ε:ℝ)(one:∀i,1≤M i)
    (board:∀k:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>read i s k) M E ρ f)
    (quoted:((Fin n→Bool)→ℂ)→ℂ)(penalty:((Fin n→Bool)→ℂ)→ℝ)(p:ℕ)
    (source:(∑i:↥(Stock.final (Fin n)).val,E i.val)+p≤q):
    let name:=fun i=>read i (ρ i) (mode i)
    Released (e:=e) (K:=K) F books ρ name M E q apron t power tuition P past height marked ε quoted penalty →
    Paid (e:=e) (K:=K) F books ρ name E p apron t power tuition P past height marked (amount (R:=R) d M*((β f)^p)⁻¹) ε quoted penalty:=by
  intro name released
  exact WilsonMeasuredPublicEntranceTransferSurveyRate.cash F P name past height marked _ ε quoted penalty p
    (fun desired lim b=>fees F name mode read (fun _=>rfl) one board p desired source lim b) released

end YM.Integration.WilsonMeasuredPublicEntranceTransferKineticRate
end
