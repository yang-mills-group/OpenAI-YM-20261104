import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerTicket
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerHorizon
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerDiagonal
import YM.Integration.WilsonMeasuredPublicEntranceNativeLowerZero
import YM.Integration.WilsonMeasuredPublicEntranceRecordedPort
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRefined
open Function Filter Finset Set Lattice Wilson RG Source Cells GapsContact.Seams Trace.Terrace
open PhysicalNext.Repeat.Legato Extraction RG17 Spec Table Table.Pairing Climb Trace.Pilot PhysMS PhysMS.Frame
open Maxwell Maxwell.Wick XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Menus MS.Theater Local.Physical
open WilsonOriginalPublicRelativeGramFreePanel (named pointsAt incidence)
open WilsonPositionProgramPublicWickGram (reading nodes)
open WilsonPhysicalStationGradedLowerPanel (left right frame)
open WilsonMeasuredPublicEntranceNativeLowerMoment (free)
open WilsonMeasuredPublicEntranceNativeLowerLeft (ears coefficients representative)
open WilsonMeasuredPublicEntranceNativeLowerFrame (panel row pivot vote)
open scoped Classical Topology BigOperators Matrix Matrix.Norms.Operator
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    (B:Deck G)(e:ℕ)(a:Axis)
local notation "I" => Glyph B e
local notation "D" => Table.Field (Bel R.family.book)

open Extra.FD
open WilsonMeasuredPublicEntranceNativeLowerTicket (entered Ticket)
variable {A:Type*}
def Refined {A:Type*}(l:Filter A)(U:ℝ→tower S)(r t:A→ℝ)(s:ℝ)(d:ℕ)(u v:(R.family.labels.level d).Index):Prop:=
  ∃(pick:A→A)(l':Filter A),NeBot l' ∧ Tendsto pick l' l ∧ ∃c:ℝ,0≤c ∧ Ticket R F l' U (r∘pick) (t∘pick) s d ((Bel R.family.book).project d (Pi.single u 1))
    ((R.family.labels.level d).grades u).2 ((R.family.labels.level d).grades v).2 c

theorem original {U J:ℝ→tower S}(lead:Leading F J)(aligned:localCost trail U J){l:Filter A}[NeBot l]
    {r t:A→ℝ}{s:ℝ}(near:Tendsto r l trail)(ht:Tendsto t l (𝓝 s))(hs:0<s)(pos:∀i,0<t i)
    {k:ℕ}(top:Module.End ℂ (D k))(heard:∀v,Tendsto (fun i=>PhysMS.Frame.cocycle k J (r i) (t i) (pos i) v) l (𝓝 (top v)))
    (earned:∀d,0<d→d≤k→let T:=R.family.labels.level d
      ∀u v:T.Index,(T.grades u).1=d→(T.grades v).1=d→(T.grades u).2≤(T.grades v).2→Refined R F l U r t s d u v):
    top=1:=by
  apply WilsonMeasuredPublicEntranceNativeLowerHorizon.original lead near ht hs pos top heard
  intro d hd Z limit
  cases d with
  | zero =>
    have fixed:Z=1:=WilsonMeasuredPublicEntranceNativeLowerZero.original Z
      (WilsonMeasuredPublicEntranceBranchGap.income F J lead near hs ht pos Z limit).1
    refine ⟨fun _=>1,fun _=>zero_le_one,?_⟩
    intro i j _
    dsimp only
    intro _
    simp only [fixed,Module.End.one_apply,Complex.ofReal_one,one_smul,sub_self,map_zero]
  | succ n =>
    apply WilsonMeasuredPublicEntranceNativeLowerDiagonal.original
    intro i j watch
    dsimp only
    intro top
    let P:=recorded R.family.labels (n+1)
    obtain ⟨u,ustamp,realU⟩:=WilsonMeasuredPublicEntranceRecordedPort.selected R.family.labels (n+1) P j
    obtain ⟨v,vstamp,_⟩:=WilsonMeasuredPublicEntranceRecordedPort.selected R.family.labels (n+1) P i
    have hi:(P.w i).1=n+1:=watch.2.1.trans top
    obtain ⟨pick,l',live,below,price,positive,tab⟩:=earned (n+1) (Nat.succ_pos n) hd u v
      (by rw [ustamp];exact top) (by rw [vstamp];exact hi) (by rw [ustamp,vstamp];exact watch.2.2)
    letI:=live
    refine ⟨price,positive,?_⟩
    apply entered R F lead aligned (near.comp below) (ht.comp below) hs (fun i=>pos (pick i)) Z (fun w=>(limit w).comp below) P i j hi watch.2.2
    simpa only [ustamp,vstamp,realU] using tab

end YM.Integration.WilsonMeasuredPublicEntranceNativeLowerRefined
end
