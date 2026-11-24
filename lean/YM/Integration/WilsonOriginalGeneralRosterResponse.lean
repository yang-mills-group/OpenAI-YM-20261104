import YM.Integration.WilsonOriginalGeneralRosterFare
import YM.Integration.WilsonOriginalGeneralRosterSale
import YM.Integration.WilsonMovingForkElectedPhase

/-! Two distinct original appointed flats, and the unrestricted finite-volume
Wilson expectation, are billed on one filed K product. The actual finite signed
quadrature acts on the whole product with all its pre-meeting correlations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterResponse
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Climb Maxwell Maxwell.Free Trace.Terrace GapsContact
open OPE PhysMS MS MS.Land FVA2 FVA2.Register Next.Extract GapsContact.Seams GapsContact.Ascent
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy Panel)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Sold Issued)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG16 RG16.Literal RG05Readout RG05Readout.Address RG05Readout.Records Marker
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool){ρ:I→{s:ℝ//0<s ∧ s<δ}}
local notation "C" => R.family
local notation "reg" => Stock.census (Fin n)
local notation "g" => fun v:Fin n=>(d (port v)).val
local notation "names" N:max per:max => fun i:Fin n=>
  (((books (ρ (port i))).rows (d (port i))).arm (branch i) (field (port i) (ρ (port i)) (mode i) (branch i))).source (N,per)

def difference {d₀:Fin n→ℕ}{K N per f v:ℕ}(file:Filed R d₀ K)(fk:f≤K)(vk:v≤K)
    (Y:∀i,(C).label (d₀ i))(turn:Fin n→Motion)(site:Fin n→Site ((C).side f per))(s:(reg).Mode):ℂ:=
  (C).omega N per (physical R d₀ (N:=N) Y turn site s)-
    actualTransport (C) (N:=N) (submitted R d₀ (N:=N) file fk Y turn site s) vk 1

def Returned (M:I→ℝ)(E:I→ℕ)(tuition:ℝ)(power target t:ℕ)(f K m j u v request desired:ℕ)
    (φ:Test n)(r:ℝ):Prop:=
  ∀program:Program R (g) K,∃fk:f<K,∃file:Filed R (g) K,
    file.station=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ (port i))).rows (d (port i))) (branch i)) ∧
    file.target=target ∧
    (∀N per w pins e,e<K→file.row N per w pins e=WilsonMovingForkPrintedFile.row program N per w pins e) ∧
    (∀N per (_:K≤N) w pins,file.row N per w pins K=WilsonMovingForkMixedSeed.product R (g) (N:=N) pins w) ∧
    ∀N per (kn:K≤N)(turn:cells R φ r (f,per)→Fin n→Motion),
      ∃A:cells R φ r (f,per)→Panel R (g) N per f K fk.le kn request power t (capital R D tuition),
      Issued (F:=F) (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (u:=m) (j:=j) (desired:=desired)
        port mode branch file φ r turn A ∧
      ∀b:ℕ,b=u∨b=v→∀bk:b≤K,∀s:(reg).Mode,
      (∀a:cells R φ r (f,per),
        ‖difference (N:=N) file fk.le bk (names N per) (turn a) a.val s‖≤debit (R:=R) (g) (M∘port) f desired s) ∧
      ‖signed R φ r (f,per) (fun a=>difference (N:=N) file fk.le bk (names N per) (turn a) a.val s)‖≤
        (∫x,‖φ x‖)*debit (R:=R) (g) (M∘port) f desired s

def Phase (M:I→ℝ)(_E:I→ℕ)(u f desired:ℕ)(φ:Test n)(r:ℝ):Prop:=
  ∃uf:u≤f,∀N per (fine:f<N)(s:(reg).Mode)(mode weak:Fin n→Bool)(a:cells R φ r (f,per))(turn:Fin n→Motion),
    let Y:=fun i=>(((books (ρ (port i))).rows (d (port i))).arm (weak i)
      (field (port i) (ρ (port i)) (mode i) (weak i))).source (N,per)
    ‖WilsonOriginalGeneralRosterScalar.gap (R:=R) d port uf fine s Y turn a.val‖ ≤ rotation (R:=R) (g) (M∘port) f desired s

omit [Fintype I] [Nonempty I] in
theorem assemble {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target f K m j u v request desired:ℕ}{φ:Test n}{r:ℝ}
    (one:∀i,1≤M i)(mu:m≤u)(uv:u≤v)(vj:v≤j)
    (first:Phase F books field (ρ:=ρ) port M E u f desired φ r)
    (second:Phase F books field (ρ:=ρ) port M E v f desired φ r)
    (sold:Sold F (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (tuition:=tuition) (power:=power)
      (target:=target) (t:=t) port mode branch f K m j request desired φ r):
    Returned F books field (ρ:=ρ) port mode branch M E tuition power target t f K m j u v request desired φ r:=by
  intro program
  obtain ⟨fk,file,station,aim,before,seed,rows⟩:=sold program
  refine ⟨fk,file,station,aim,before,seed,?_⟩
  intro N per kn turn
  obtain ⟨A,issued⟩:=rows N per kn turn
  refine ⟨A,issued,?_⟩
  intro b atEar bk s
  have bounds:m≤b ∧ b≤j:=atEar.elim (fun eq=>eq ▸ ⟨mu,uv.trans vj⟩) (fun eq=>eq ▸ ⟨mu.trans uv,vj⟩)
  have p:Phase F books field (ρ:=ρ) port M E b f desired φ r:=atEar.elim (fun eq=>eq ▸ first) (fun eq=>eq ▸ second)
  obtain ⟨bf,free⟩:=p
  have cell (a:cells R φ r (f,per)):‖difference (N:=N) file fk.le bk (names N per) (turn a) a.val s‖≤
      debit (R:=R) (g) (M∘port) f desired s:=
    WilsonOriginalGeneralRosterFare.receipt d port fk kn bf file (names N per) (turn a) a.val s (M∘port)
      (free N per (fk.trans_le kn) s mode branch a (turn a)) (issued.cell b bounds.1 bounds.2 bk s a)
  exact ⟨cell,WilsonReceivedChronologicalFixedRoseVariation.original R φ r (f,per) _ _
    (WilsonOriginalGeneralRosterFare.nonneg (R:=R) (g) (M∘port) (fun i=>one (port i)) f desired s) cell⟩

def Register (h t:ℕ)(d:I→Fin (D+1))
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val):Prop:=
  ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀n:ℕ,0<n→∀(port:Fin n→I)(desired target:ℕ),
    let request:=desired+∑i,E (port i)
    let grades:=fun i=>(d (port i)).val
    let pwr:=univ.sup (accuracy grades request)+1
    let reserve:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let tuition:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h reserve D
    ∀ φ : Test n, ∀ lo : ℕ, ∃ (base j₀ ear₀ j₁ ear₁ : ℕ), lo ≤ base ∧ base ≤ j₀ ∧ j₀ ≤ ear₀ ∧ ear₀ < ear₁ ∧ j₁ ≤ ear₁ ∧ Stop (C) 0 j₀ ear₀ ∧ Stop (C) 0 j₁ ear₁ ∧
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    let K:=berth R reserve f
    ∃j:ℕ,ear₁≤j ∧ j+2≤f ∧ ∀mode branch:Fin n→Bool,
      Returned F books field (ρ:=ρ) port mode branch M E tuition power target t f K base j ear₀ ear₁ request desired φ r

theorem original (fac:Facilities (C) order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (grant:WilsonOriginalGeneralRosterSale.Register F books h t d field):WilsonOriginalGeneralRosterResponse.Register F books h t d field:=by
  classical
  obtain ⟨M,E,one,issue⟩:=grant
  refine ⟨M,E,one,?_⟩
  intro n np port desired target request grades pwr reserve tuition power φ floor
  obtain ⟨m,store,fm⟩:=((issue n np port desired target φ).and (eventually_ge_atTop floor)).exists
  obtain ⟨J,u,mj,ju,stop⟩:=WilsonMovingForkElectedPhase.fixed fac m
  obtain ⟨J',v,old,jv,other⟩:=WilsonMovingForkElectedPhase.fixed fac (u+1)
  have uv:u<v:=old.trans jv
  have mv:=mj.trans (ju.trans uv.le)
  have intake (b tag:ℕ)(licensed:Stop (C) 0 tag b):=WilsonOriginalGeneralRosterScalar.original F d books port
    (h:=h) fac bliss slow licensed φ request
  refine ⟨m,J,u,J',v,fm,mj,ju,uv,jv,stop,other,?_⟩
  filter_upwards [store v mv,intake u J stop,intake v J' other] with r provided early late
  intro ρ span near f K
  obtain ⟨j,vj,height,charges,cohort⟩:=provided ρ span near
  have installed(b:ℕ)(source:∃bf:b≤f,∀N per (fine:f<N)(s:(Stock.census (Fin n)).Mode)
      (weak:Fin n→Bool)(x:∀i,S.Field ((d (port i)).val))(a:cells R φ r (f,per))(turn:Fin n→Motion),
        let Y:=fun i=>(((books (ρ (port i))).rows (d (port i))).arm (weak i) (x i)).source (N,per)
        ‖WilsonOriginalGeneralRosterScalar.gap (R:=R) d port bf fine s Y turn a.val‖ ≤
          WilsonOriginalGeneralRosterScalar.directPrice F d books port ρ f request weak x s):
      Phase F books field (ρ:=ρ) port M E b f desired φ r:=by
    obtain ⟨bf,funded⟩:=source
    refine ⟨bf,?_⟩
    intro N per fine s mode weak a motion
    let x:=fun i=>field (port i) (ρ (port i)) (mode i) (weak i)
    exact (funded N per fine s weak x a motion).trans (WilsonOriginalGeneralRosterFare.bill F d books port
      ρ f desired weak x s M E one (fun i=>(charges (mode i) (port i) (weak i)).2.2))
  exact ⟨j,vj,height,fun mode branch=>assemble F books field port mode branch one (mj.trans ju) uv.le vj
    (installed u (early ρ span near)) (installed v (late ρ span near)) (cohort mode branch)⟩

end YM.Integration.WilsonOriginalGeneralRosterResponse
end
