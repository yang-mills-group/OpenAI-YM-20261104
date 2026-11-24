import YM.Integration.WilsonCenteredNestedPairHaar
import YM.Integration.WilsonCenteredNestedPairRead

/-! Read the joint original rotation on the actual ternary source with
one deep child.  The nodes, held parent, unit channel and centered
placements are those of the original Nesting kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedPairChord
open Set Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom
open OPE.Nesting.Tree OPE.Nesting.Composite OPE.Log OPE.Prescription
open WilsonCenteredNestedRawRows WilsonCenteredNestedRawPair WilsonCenteredNestedPairHaar
open WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairRead WilsonCenteredNestedGross WilsonCenteredNestedEdge
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

abbrev near (v : full.Leaf→S.Tag) (i : Fin 2) := v ⟨0,⟨i,()⟩⟩
abbrev other (v : full.Leaf→S.Tag) := v ⟨1,()⟩

theorem chord (h d : ℕ) (c : Q.channels h) (z : full.Plot) (v : full.Leaf→S.Tag) :
    held F Q d h c (near v) (other v) (skyline (childPlace 0 z)) (skyline z) (anchor z) =
    Kernel.chord F Q z v c (caps h d) := by
  have parent := WilsonCenteredNestedProgram.chord F Q (fun _=>0) (dates 1 1) z v (caps h d) h c
  have pair := WilsonCenteredNestedPairRead.deposited F Q (WilsonCenteredNestedProgram.measured F Q) (fun _=>0) h d v z 1 1 h c
  apply Eq.trans _ (pair.symm.trans parent)
  unfold held
  refine Finset.sum_congr rfl fun t _=>congrArg (_ * ·) ?_
  change _ = express Q h c (skyline z) (echoTags F Q v ((branches F Q h d).symm t)) (anchor z)
  refine congrArg (fun w=>express Q h c (skyline z) w (anchor z)) ?_
  funext i
  fin_cases i
  · exact (heldTags F Q h d v t).1.symm
  · exact (heldTags F Q h d v t).2.symm

private lemma accepts {n : ℕ} {t : Fin n→Tree} {M η : ℝ} {s : (fork n t).Inner→ℝ} {z : (fork n t).Plot}
    (h : (fork n t).Relative M η s z) :
    WithinRoom (s (.inl ())) M η (skyline z) (anchor z) :=
  ⟨fun i=>h.1 (.inr ⟨i,(t i).topSeat⟩),fun i j ne=>h.2.1 i j (t i).topSeat (t j).topSeat ne⟩

theorem original (fac : Facilities C f S) (foundation : Foundation F Q) {u : Filter (ℕ×ℕ)} [u.NeBot]
    (lo : u ≤ f.fuse) (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (h d : ℕ)
    (c : Q.channels h) (v : full.Leaf→S.Tag) (four : ∀ i,(v i).1=4) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃(j l:ℕ)(A B:ℝ),0≤A ∧ 0≤B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),Accept r M η (dates r a) z →
      ‖mean (joined F Q Q.port d h h c (near v) (other v) (skyline (childPlace 0 z)) (skyline z) (anchor z)) -
        Kernel.chord F Q z v c (caps h d)‖ ≤
        Fintype.card (Menu.Cut Q d) * (wage j A a * wage l B r * (r^h/(a^8*r^4)) * (a/r)^(d+1)) := by
  obtain ⟨j,l,A,B,An,Bn,paid⟩ := WilsonCenteredNestedPairHaar.original F Q fac foundation lo ticket d h c (near v) (other v) Mn ηp
  refine ⟨j,l,A,B,An,Bn,?_⟩
  filter_upwards [paid] with r cap a z ok
  have dist := ok.relative
  have sub := dist.2.2 (0:Fin 2)
  have datesOK := ok.levels.2.2 (0:Fin 2)
  have little : 0<a := datesOK.1
  have smaller : a≤r := by
    have e : a≤r*1 := datesOK.2.1
    rwa [mul_one] at e
  have rate:=cap a little smaller (skyline (childPlace 0 z)) (skyline z) (anchor z) (accepts sub) (accepts dist)
  rw [←chord F Q h d c z v]
  have grades : degree (near v) = 8 := by simp only [degree,near,Fin.sum_univ_two,four]
  have fourth : (other v).1=4 := four _
  simpa only [grades,fourth,base] using rate

end YM.Integration.WilsonCenteredNestedPairChord
