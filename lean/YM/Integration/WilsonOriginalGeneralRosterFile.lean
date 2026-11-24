import YM.Integration.WilsonOriginalGeneralRosterDensity
import YM.Integration.WilsonPhysicalMovingForkPinnedMaster
import YM.Integration.WilsonMeasuredPublicEntranceFullCampus
import YM.Integration.WilsonReceivedChronologicalFixedRoseVariation

/-! Choose one measured inverse for a finite menu before the physical regulators.
The submitted K product, the earlier rows of any prescribed programme and every
original marked density use this same inverse. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterFile
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReflectedMixedSharedAxis (Pinned)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonMeasuredPublicEntrancePanel (Panel Reading accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker
open Climb Maxwell Maxwell.Free Trace.Terrace Trace.Physical Trace.Physical.Germ GapsContact
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    {books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E e:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ//0<s ∧ s<δ}}
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool)
local notation "g" => fun v:Fin n=>(d (port v)).val
local notation "slots" => fun v:Fin n=>WilsonReflectedPublicStationFare.station F ((books (ρ (port v))).rows (d (port v))) (branch v)
local notation "names" N:max per:max => fun v:Fin n=>
  (((books (ρ (port v))).rows (d (port v))).arm (branch v) (field (port v) (ρ (port v)) (mode v) (branch v))).source (N,per)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "reg" => Stock.census (Fin n)

def price (d:Fin n→ℕ)(M:Fin n→ℝ)(f desired:ℕ)(s:(reg).Mode):ℝ:=
  (∏v∈s.val,WilsonAddressedHomeDose.ceiling (R:=R) (d v) (M v))*((β f)^desired)⁻¹

def Fee (A:(i:Fin n)→ℝ)(v:Fin n→ℕ)(request desired:ℕ):Prop:=
  (∀i,1≤A i) ∧ ∀s:(reg).Mode,desired+∑i∈s.val,v i≤request

structure Issued {f K N per u j request desired:ℕ}{fk:f≤K}{cut:K≤N}
    (file:Filed R (g) K)(φ:Test n)(r:ℝ)
    (turn:cells R φ r (f,per)→Fin n→Motion)
    (panels:cells R φ r (f,per)→Panel R (g) N per f K fk cut request power t (capital R D tuition)):Prop where
  slotsEq : ∀a,(panels a).slot=file.station
  axesEq : ∀a,(panels a).axis=file.A N per
  namesEq : ∀a,(panels a).names=names N per
  salary : ∀a,(panels a).M=M∘port
  location : ∀a,(panels a).loc=a.val
  motion : ∀a,(panels a).turn=turn a
  spent : ∀a i,Next.Rank.Spindle.paid (C) ((g) i) f N per ((panels a).names i)≤M (port i)*(β f)^(E (port i))
  density : ∀a,WilsonOriginalGeneralRosterDensity.Restored (panels a)
  hearing : ∀a v,u≤v→v≤j→∀vf:v≤f, Reading R (g) (panels a) vf
  cell : ∀v,u≤v→v≤j→∀vk:v≤K,∀s:(reg).Mode,∀a:cells R φ r (f,per),
    ‖WilsonMeasuredPublicEntranceCutoffHearing.difference R (g) file fk cut vk (names N per) (turn a) a.val s‖≤
      price (R:=R) (g) (M∘port) f desired s
  tested : ∀v,u≤v→v≤j→∀vk:v≤K,∀s:(reg).Mode,
    ‖signed R φ r (f,per) (fun a=>WilsonMeasuredPublicEntranceCutoffHearing.difference R (g)
      file fk cut vk (names N per) (turn a) a.val s)‖≤(∫x,‖φ x‖)*price (R:=R) (g) (M∘port) f desired s

def Sold (f K u j request desired:ℕ)(φ:Test n)(r:ℝ):Prop:=
  ∀program:Program R (g) K,∃fk:f<K,∃file:Filed R (g) K,
    file.station=slots ∧ file.target=target ∧
    (∀N per w pins age,age<K→file.row N per w pins age=WilsonMovingForkPrintedFile.row program N per w pins age) ∧
    (∀N per (_:K≤N) w pins,file.row N per w pins K=WilsonMovingForkMixedSeed.product R (g) (N:=N) pins w) ∧
    ∀N per (cut:K≤N)(turn:cells R φ r (f,per)→Fin n→Motion),
      ∃panels:cells R φ r (f,per)→Panel R (g) N per f K fk.le cut request power t (capital R D tuition),
        Issued (F:=F) (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (u:=u) (j:=j)
          (desired:=desired) port mode branch file φ r turn panels

theorem original {f K u j request desired:ℕ}{φ:Test n}{r:ℝ}
    (campus:School F D T t d e books field M E tuition power target ρ f K)
    (pinned:Pinned F D T h t d e books field M tuition power target ρ f K)
    (fit:∀i,accuracy (g) request i≤e (port i))(fee:Fee (M∘port) (E∘port) request desired)
    (jf:j≤f)
    (apart:∀N per, K≤N→∀a:cells R φ r (f,per),
      Pairwise fun i k=>(R.family.path.levels.budget f).B^2<separation (a.val i) (a.val k))
    (hears:∀N per (cut:K≤N)(fk:f≤K) (a:cells R φ r (f,per))
      (P:Panel R (g) N per f K fk cut request power t (capital R D tuition)),P.slot=slots→P.loc=a.val→
      ∀v,u≤v→v≤j→∀vf:v≤f, Reading R (g) P vf):
    Sold F (books:=books) (field:=field) (ρ:=ρ) (M:=M) (E:=E) (tuition:=tuition) (power:=power)
      (target:=target) (t:=t) port mode branch f K u j request desired φ r:=by
  classical
  obtain ⟨up,_,_,_,registered⟩:=WilsonPhysicalMovingForkPinnedMaster.original F pinned
  obtain ⟨_,axes,_,offer⟩:=campus
  intro program
  obtain ⟨old,stations,aim,_,word⟩:=registered port branch program
  let matrix:=fun per i=>axes per (port i) (branch i)
  let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R (g) old matrix
  refine ⟨up,file,stations,aim,?_,?_,?_⟩
  · intro N per w pins age below
    change dite (age=K) _ (fun _=>old.row N per w pins age)=_
    rw [dif_neg (Nat.ne_of_lt below),word]
  · intro N per cut w pins
    exact WilsonMeasuredPublicEntranceCutoffFile.original R (g) old matrix cut per w pins
  intro N per cut turn
  obtain ⟨_,_,_,_,issued⟩:=offer N per cut
  have get(a:cells R φ r (f,per)):=issued n port mode branch old stations request fit (turn a) a.val (fun i k hne=>apart N per cut a hne)
  choose panels entries using get
  have locate(a:cells R φ r (f,per)): (panels a).loc=a.val:=(entries a).2.2.2.2.2.2.2.1
  have heard(a:cells R φ r (f,per)):=hears N per cut up.le a (panels a) ((entries a).1.trans stations) (locate a)
  have bound(v:ℕ)(uv:u≤v)(vj:v≤j)(vk:v≤K)(s:(reg).Mode)(a:cells R φ r (f,per)):
      ‖WilsonMeasuredPublicEntranceCutoffHearing.difference R (g) file up.le cut vk (names N per) (turn a) a.val s‖≤
        price (R:=R) (g) (M∘port) f desired s:=by
    obtain ⟨slot,axis,name,amount,_,_,phase,place,_,_,_,refs,cash⟩:=entries a
    have minCost(i:Fin n):1≤(panels a).M i:=by rw [amount];exact fee.1 i
    have paid:=WilsonMeasuredPublicEntranceCellWords.paid R (g) (panels a) file slot axis (vj.trans jf)
      (heard a v uv vj (vj.trans jf)) minCost (E∘port) refs cash s desired (fee.2 s)
    rw [WilsonMeasuredPublicEntranceCutoffHearing.original,name,phase,place,amount] at paid
    exact paid
  refine ⟨panels,?_⟩
  constructor
  · exact fun a=>(entries a).1
  · exact fun a=>(entries a).2.1
  · exact fun a=>(entries a).2.2.1
  · exact fun a=>(entries a).2.2.2.1
  · exact locate
  · exact fun a=>(entries a).2.2.2.2.2.2.1
  · intro a i
    obtain ⟨_,_,_,amount,_,_,_,_,_,_,_,_,cash⟩:=entries a
    simpa only [amount,Function.comp_apply] using cash i
  · intro a
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,refs,_⟩:=entries a
    exact WilsonOriginalGeneralRosterDensity.original (panels a) refs
  · exact heard
  · exact bound
  · intro v uv vj vk s
    apply WilsonReceivedChronologicalFixedRoseVariation.original _ _ _ _ _ _ _ (bound v uv vj vk s)
    unfold price
    apply mul_nonneg (prod_nonneg fun i _=>?_) (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans ((C).path.levels.fits.delayed f).le) _))
    exact (mul_nonneg zero_le_two (zero_le_one.trans (fee.1 i))).trans (le_max_left ..)

end YM.Integration.WilsonOriginalGeneralRosterFile
end
