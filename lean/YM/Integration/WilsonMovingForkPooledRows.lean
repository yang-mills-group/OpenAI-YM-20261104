import YM.Integration.WilsonMovingForkNamedGate
import YM.Integration.WilsonPublicForkPooledHearing

/-! Both incoming measurements use the field book whose original joint portions and
true measured inverses were funded before the numerical test. The far insertion is already
a physical slot of the microscopic ordinary product. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkPooledRows
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extraction Table Spec
open OPE OPE.Orbits RG17 Trace.Physical.GermGraph WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonPublicForkPooledHearing (markedCut)
open WilsonPositionProgramPublicStations
open PhysicalNext PhysicalNext.Repeat.Legato Trace.Pilot Trace.Physical Trace.Physical.Germ GapsContact Climb Maxwell Maxwell.Free Next.Rank Next.Rank.Station
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T:ℕ}{δ:ℝ}(book:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
local notation "C" => R.family
local notation "Time" => {s:ℝ // 0<s ∧ s<δ}

def arms {n:ℕ}(tag:Fin n→S.Tag)(caps:∀i,(tag i).1 < D+1)
    (age:Fin n→Time)(weak:Fin n→Bool):∀i,Arm C S (l:Filter _) (tag i).1 (tag i).2:=
  fun i=>((book (age i)).rows ⟨(tag i).1,caps i⟩).arm (weak i) (tag i).2

/-- One fresh smear of the actual product in the independent physical directions.
The values in the sum are the original full ensembles at the actual lattice sites. -/
theorem finite {n:ℕ}(v:Fin n→S.Tag)(caps:∀i,(v i).1<D+1)(age:Fin n→Time)(weak:Fin n→Bool)
    (φ:Test n)(N per:ℕ):
    markedCut v (arms F book v caps age weak) φ (N,per)=
      ((C).S.a N:ℂ)^(4*n)*∑o:Fin n→Site ((C).side N per),
       φ (Order.cells C N per o)*(C).numeric N per
        (fun i=>⟨(v i).1,(((book (age i)).rows ⟨(v i).1,caps i⟩).arm (weak i) (v i).2).source (N,per)⟩) o:=rfl

/-- Put the complete original near product and all far insertions into one joint
measurement, and each Gram entry into its own two-slot measurement of these same fields. -/
theorem original (order:(l:Filter _) ≤ f.fuse){n h:ℕ}{d:Caps n}{B:Type}
    (near:Labels S d)(out:B→S.Field h)(X:External C S)(r t:Time)(ψ:Test n)
    (covered:packs X r.val ψ)(whole:Integrable (fun u:Points (X.n+1)=>X.test u*query F near (X.offset u) X.labels none r.val ψ))
    (dnear:∀i,d i<D+1)(dout:h<D+1)(dx:∀j,(X.tags j).1<D+1)
    (branch:Fin n→Bool)(column:B→Bool)(far:Fin X.n→Bool):
    let all:=Fin.append (tags near) X.tags
    let two:=fun k=>Fin.cons (α:=fun _=>S.Tag) ⟨h,out k⟩ X.tags
    ∃wholeCaps:∀i,(all i).1<D+1, ∃gramCaps:∀k i,((two k) i).1<D+1,
      Tendsto (markedCut all (arms F book all wholeCaps (Fin.append (fun _:Fin n=>r) (fun _:Fin X.n=>t))
        (Fin.append branch far)) (shape X r.val ψ)) (l:Filter _) (𝓝 (appeared F near X r.val ψ)) ∧
      ∀k,Tendsto (markedCut (two k) (arms F book (two k) (gramCaps k) (Fin.cons r (fun _:Fin X.n=>t))
        (Fin.cons (column k) far)) X.test) (l:Filter _) (𝓝 (X.charge F h (out k))):=by
  dsimp only
  have wcap:∀i,((Fin.append (tags near) X.tags) i).1 < D+1:=by
    intro i;induction i using Fin.addCases with
    | left i=>simpa only [Fin.append_left,Orbits.tags] using dnear i
    | right i=>simpa only [Fin.append_right] using dx i
  have gcap(k):∀i,(Fin.cons (α:=fun _=>S.Tag) ⟨h,out k⟩ X.tags i).1 < D+1:=by
    intro i;induction i using Fin.cases with
    | zero=>simpa only [Fin.cons_zero] using dout
    | succ i=>simpa only [Fin.cons_succ] using dx i
  exact ⟨wcap,gcap,WilsonPublicForkPooledHearing.whole F order near X r.property.1 ψ covered whole _,
    fun k=>WilsonPublicForkPooledHearing.gram F order (out k) X _⟩

end YM.Integration.WilsonMovingForkPooledRows
