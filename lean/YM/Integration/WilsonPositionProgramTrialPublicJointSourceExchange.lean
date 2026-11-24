import YM.Integration.WilsonPositionProgramTrialPublicJointSourceFaculty

/-! The two genuine fresh sections have the same one-source transfer before projection onto either frame. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceExchange
open Function Finset Matrix Lattice Wilson RG Precision Source Labels
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonIndependentMatchedFiledIncome (plate)
open scoped BigOperators Classical
variable {G:Gauge}{h D k e:ℕ}{F:Frame G h}{H:Hol G}{E W:Credit}
variable (J S:SectionData F)(fit:h<D)

def change (L:Levels G)(O:ChartRatio G)(m K:ℕ)(c:Verse F):Verse F:=
  steep L O J fit K m (K-m) (street L O S fit K m (K-m) c)

theorem carried (T:Theatre H S fit e E W)(m K:ℕ)(paid:T.V.anchor ≤ m)(before:m ≤ K)
    (cap:h ≤ k)(c:Verse F):
    opal F (spools T.V.draws T.V.paid K k h m (K-m) (Shrine (plate S fit) c))=
      street T.V.draws T.V.paid S fit K m (K-m) c:=by
  have step:=spooled (N:=K) (i:=K-m) T c paid cap (by omega)
  rw [Nat.add_sub_of_le before] at step
  change spools T.V.draws T.V.paid K k h m (K-m)
    (Shrine (Peaks T.V.draws T.V.paid S fit K K) c)=_ at step
  rw [Peak_initial] at step
  rw [plate,step,Shrine_read _ _ (production T before paid).1]

theorem undo (T:Theatre H J fit e E W)(m K:ℕ)(paid:T.V.anchor ≤ m)(before:m ≤ K)(c:Verse F):
    steep T.V.draws T.V.paid J fit K m (K-m) (street T.V.draws T.V.paid J fit K m (K-m) c)=c:=by
  have reach:m+(K-m) ≤ K:=by omega
  apply street_up T paid reach
  exact Street_up T _ paid reach

theorem original {H':Hol G}{e':ℕ}{E' W':Credit}
    (T:Theatre H J fit e E W)(U:Theatre H' S fit e' E' W')
    (levels:U.V.draws=T.V.draws)(clock:U.V.paid=T.V.paid)(m K:ℕ)
    (paid:T.V.anchor ≤ m)(sold:U.V.anchor ≤ m)(before:m ≤ K):
    let L:=T.V.draws
    let O:=T.V.paid
    (∀c,street L O J fit K m (K-m) (change J S fit L O m K c)=street L O S fit K m (K-m) c) ∧
    (∀c,change S J fit L O m K (change J S fit L O m K c)=c) ∧
    (∀c,change J S fit L O m K (change S J fit L O m K c)=c) ∧
    ∀c (r:ℕ),h ≤ r →
      opal F (spools L O K r h m (K-m) (Shrine (plate S fit) c))=
      opal F (spools L O K r h m (K-m) (Shrine (plate J fit) (change J S fit L O m K c))):=by
  intro L O
  have reach:m+(K-m) ≤ K:=by omega
  have restoreJ (c:Verse F):street L O J fit K m (K-m) (steep L O J fit K m (K-m) c)=c:=
    Street_up T c paid reach
  have restoreS (c:Verse F):street L O S fit K m (K-m) (steep L O S fit K m (K-m) c)=c:=by
    simpa only [levels,clock] using Street_up U c sold reach
  have undoS (c:Verse F):steep L O S fit K m (K-m) (street L O S fit K m (K-m) c)=c:=by
    simpa only [levels,clock] using undo S fit U m K sold before c
  refine ⟨fun c=>restoreJ _,fun c=>?_,fun c=>?_,?_⟩
  · simp only [change,restoreJ,undoS]
  · simp only [change,restoreS]
    exact undo J fit T m K paid before c
  · intro c r cap
    have source:=carried S fit U m K sold before cap c
    rw [levels,clock] at source
    rw [source,carried J fit T m K paid before cap,change,restoreJ]

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceExchange
