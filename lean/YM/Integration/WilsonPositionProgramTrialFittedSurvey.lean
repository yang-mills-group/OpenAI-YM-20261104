import YM.Integration.WilsonPositionProgramTrialFittedIntake
import YM.Integration.WilsonMaxwellThermometerSurveyCourse
import YM.Integration.WilsonOriginalPublicTwoTopJoined

/-! The same offered vector is enrolled on both ends of the two-top test.
Different filed raw catalogues each issue their own actual thermal coordinate. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialFittedSurvey
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard WilsonCoeffUV.Embroider Source Source.Drops Labels
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open WilsonMaxwellThermometerSurveyCourse (shelf)
open WilsonMaxwellThermometerSurveyIncome (prices)
open scoped BigOperators Classical
variable {G:Gauge}{a h D k u e:ℕ}

def stamp (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(m K:ℕ)(v:Herit Q):Herit Q:=
  fun i=>ticket L O (Q i) K m K (v i)

def Hearing (L:Levels G)(O:ChartRatio G)(Q:Fin (a+1)→SealR G)(clock:ℕ→ℝ)(j e u:ℕ)(C C':Credit):Prop:=
  ∀(m K N i:ℕ)(v:Herit Q)(φ:Wilt Q)(B:Fin (a+1)→ℝ)(Z y:ℝ)(o:CellR),
    j ≤ m → m ≤ K → K ≤ N → m ≤ i → clock m ≤ Z → Bough Q φ y Z B →
    let X:=stamp L O Q m K v
    let T:=normalized L O Q X m
    let A:=∏b,B b*(C'.buy (clock m)*fee X e b)
    (∀s,centralL L O K m K (Q s) (T K s)=Shrine (Peaks L O (Q s).ans (Q s).path K K) (v s)) ∧
    Fringed (capP Q) e u 1 (C.buy Z*A) (trailC L.S m K)
      (loadK L O φ (T N) m (min i N) N y o) (loadK L O φ (T K) m (min i K) K y o)

theorem original (R:Run G)(W:XSpace.Initialize G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
    (simple:G.Simple)(s:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices s R.kit)
    (survey:prices W R.kit)(big:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) l d fit) ≤ k):
    ∃C C':(Fin (a+1)→Bool)→Credit,∀ᶠ j:ℕ in atTop,∀tag,
      Hearing R.family.path.levels R.metals.O (shelf W l d fit tag) (zz R.family.path.levels) j e u (C tag) (C' tag):=by
  choose C joint using fun tag=>topDay (hol G) (shelf W l d fit tag) Credit.leanC Credit.leanC Credit.leanC Credit.leanC Credit.leanC e u
  choose wallet paid using fun tag=>steering (hol G) (shelf W l d fit tag) e Credit.leanC Credit.leanC Credit.leanC Credit.leanC
  refine ⟨C,wallet,?_⟩
  filter_upwards [WilsonMaxwellThermometerSurveyCourse.original R W l d fit simple s funded survey big rails cap] with j sale
  obtain ⟨_,Y,levels,cash,clock,home,_,quiet,spring,all⟩:=sale
  intro tag
  let Q:=shelf W l d fit tag
  obtain ⟨frames,ready⟩:=all tag
  have heard:Hearing Y.L.V.draws Y.L.V.paid Q Y.L.V.y Y.L.V.anchor e u (C tag) (wallet tag):=by
    intro m K N i v φ B Z y o late before live visiting room bough X T invoice
    have both:=paid tag Y.L.V frames m late (fee X e) (fun _=>X) (WilsonPositionProgramNormalizedMaster.shipped X e Y.L.V.draws.S m)
    refine ⟨?_,?_⟩
    · intro s
      let b:=(frames s).some
      have entered:b.p.f.arch.V.anchor ≤ m:=b.p.tap.trans_le late
      have approved:=(WilsonPositionProgramTrialFittedLens.original _ (Q s) b.p.f.arch entered before le_rfl (v s)).2.2
      simpa only [T,X,stamp,normalized,b.p.lands,b.p.modes] using approved
    exact joint tag Y.L.V ready spring quiet m i K N K φ (T N) (T K)
      (fun s=>(wallet tag).buy (Y.L.V.y m)*fee X e s) B Z y (trailC Y.L.V.draws.S m K) o
      late visiting before live le_rfl room bough le_rfl (both N K K before live le_rfl)
  rwa [levels,cash,clock,home] at heard

end YM.Integration.WilsonPositionProgramTrialFittedSurvey
