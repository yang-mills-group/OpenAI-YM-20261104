import YM.Integration.WilsonCenteredNestedPairMargins
import YM.Integration.WilsonCenteredNestedTreePrice
import YM.Integration.WilsonCenteredNestedPairChord

/-! Haar and real-terminal reduction of the sharp signed ticket, with the
same complete child deposited before the outer rotation is integrated. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedTreeMean
open Function Filter Set Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Prescription MeasureTheory
open OPE.Nesting.Tree OPE.Nesting.Composite WilsonCenteredNestedRawRows
open OPE.Log OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedTwoVertex WilsonCenteredNestedPairConvoy
open WilsonCenteredNestedProjectedShadow WilsonCenteredNestedRawPair WilsonCenteredNestedChildEdit
open WilsonCenteredNestedRawDiagram WilsonCenteredNestedTicketSites WilsonCenteredNestedPairHaar
open WilsonCenteredNestedTreeWallet WilsonCenteredNestedLoggedRow
open scoped Classical Topology BigOperators
attribute [local instance] measO borelO YM.Work.A15.compact_ortho
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

lemma child_sites (z:full.Plot) : pair (sites z) 2 3=skyline (childPlace 0 z) := by
  funext i;fin_cases i <;> rfl
lemma root_sites (z:full.Plot) : pair (sites z) 1 4=skyline z := by
  funext i;fin_cases i <;> rfl

lemma node_room {n : ℕ} {t : Fin n→Tree} {M η : ℝ} {s : (fork n t).Inner→ℝ} {z : (fork n t).Plot}
    (h : (fork n t).Relative M η s z) :
    WithinRoom (s (.inl ())) M η (skyline z) (anchor z) :=
  ⟨fun i=>h.1 (.inr ⟨i,(t i).topSeat⟩),fun i j ne=>h.2.1 i j (t i).topSeat (t j).topSeat ne⟩

private lemma margins (D m:ℕ) {M η:ℝ} (Mn:0≤M) (ηp:0<η) : ∀ᶠr:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),
    Accept r M η (dates r a) z → orbitMargin Q.port D (pair (sites z) 2 3) (sites z 1) ∧
    orbitMargin Q.port m (pair (sites z) 1 4) (sites z 0) := by
  have enter := Orbits.admissible_separated (I:=Fin 2) F Q Mn ηp D
  have exit := Orbits.admissible_separated (I:=Fin 2) F Q Mn ηp m
  obtain ⟨ε,εp,armed⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp enter
  filter_upwards [exit,mem_nhdsWithin_of_mem_nhds (ge_mem_nhds εp)] with r atR tight a z ok
  have little : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have smaller : a≤r := by
    have e :a≤r*1 := (ok.levels.2.2 (0:Fin 2)).2.1
    rwa [mul_one] at e
  rw [child_sites,root_sites]
  exact ⟨armed (show a∈Ioc 0 ε from ⟨little,smaller.trans tight⟩) _ _ (node_room (ok.relative.2.2 (0:Fin 2))) D le_rfl,
    atR _ _ (node_room ok.relative) m le_rfl⟩

private lemma sums {T:Type} [Fintype T] (X Y:T→Ortho→ℂ) (x:∀i,Integrable (X i) haar) (y:∀i,Integrable (Y i) haar) :
    AEStronglyMeasurable (fun k=>∑i,X i k*Y i k) haar := by
  let W:=fun i=>X i * Y i
  change AEStronglyMeasurable (fun k=>∑i,W i k) haar
  exact Finset.aestronglyMeasurable_fun_sum _ (fun i _=>(x i).aestronglyMeasurable.mul (y i).aestronglyMeasurable)

private lemma scaled (X Y:Ortho→Bool→ℂ) (p E:ℝ) (pos:0<p) (pay:∀k b,p*‖Y k b-X k b‖≤E)
    (mx:∀b,AEStronglyMeasurable (fun k=>X k b) haar) (iy:∀b,Integrable (fun k=>Y k b) haar) :
    p*‖mean Y-mean X‖≤E := by
  have filed := difference X Y (E:=E/p) (fun k b=>(le_div_iff₀ pos).mpr (by
    rw [mul_comm,norm_sub_rev];exact pay k b)) mx iy
  rw [norm_sub_rev] at filed
  exact (mul_comm ..).le.trans ((le_div_iff₀ pos).mp filed)

theorem original (fac : Facilities C f S) {u : Filter (ℕ×ℕ)} [u.NeBot] (lo : u ≤ f.fuse)
    (ticket : MatrixTicket (C:=C) S F.sector.derivatives u) (v:Fin 3→S.Tag) (D m:ℕ) (c:Q.channels m)
    {M η:ℝ} (Mn:0≤M) (ηp:0<η) : ∃(j:ℕ)(A:ℝ),0≤A ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀(a:ℝ)(z:full.Plot),
      Accept r M η (dates r a) z→WilsonCenteredNestedTreeWallet.toll (degrees v) m a r *
        ‖express Q m c (trio (sites z)) v (sites z 0) -
          mean (joined F Q Q.port D m m c (head v) (v 2) (pair (sites z) 2 3) (pair (sites z) 1 4) (sites z 0))‖ ≤
      A*((shell r * shell a)^j * (a/r)^(D+1)) := by
  obtain ⟨j,A,An,paid⟩ := WilsonCenteredNestedTreePrice.original F Q fac lo ticket v D m c Mn ηp
  refine ⟨j,A,An,?_⟩
  filter_upwards [paid,WilsonCenteredNestedPairMargins.original F Q m M η ηp,margins F Q D m Mn ηp]
    with r atR raw faces a z ok
  have e := WilsonCenteredNestedRootMean.original F Q m c (trio (sites z)) (sites z 0) (raw a z ok) (voices v)
  change _ * ‖Q.coef m c _ (voices v) _ - _‖≤_
  rw [e]
  have rp : 0<r := ok.levels.1
  have ap : 0<a := (ok.levels.2.2 (0:Fin 2)).1
  have pos : 0<WilsonCenteredNestedTreeWallet.toll (degrees v) m a r := by unfold WilsonCenteredNestedTreeWallet.toll;positivity
  apply scaled _ (face F Q Q.port m m c (trio (sites z)) v (sites z 0)) _ _ pos (atR a z ok)
  · intro b
    apply sums (T:=Menu.Cut Q D)
      (fun i k=>face F Q Q.port D i.1.val i.2 (pair (sites z) 2 3) (head v) (sites z 1) k b)
      (fun i k=>face F Q Q.port m m c (pair (sites z) 1 4) (placed F Q i (v 2)) (sites z 0) k b)
    · exact fun i=>leaf F Q D i.1.val i.2 (head v) _ _ (faces a z ok).1 b
    · exact fun i=>leaf F Q m m c (placed F Q i (v 2)) _ _ (faces a z ok).2 b
  · exact fun b=>leaf F Q m m c v _ _ (raw a z ok) b

end YM.Integration.WilsonCenteredNestedTreeMean
