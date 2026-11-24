import YM.Integration.WilsonMarkedIndependentNormalizedSingleton

/-! Keep the separated-source resource on the very same elected realm that
issues the moving-cutoff normalized fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedEnrollment
open Function Filter Lattice RG RG.Supply Wilson Precision Next.Foundations PowerSeries
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open WilsonLimitConstruction
open scoped Classical BigOperators Topology
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonMarkedIndependentNormalizedEntrance (Rent)
open WilsonConditionalTaylorSeparatedPurchase (fee fee_pos)
variable {G:Gauge}{a:ℕ}

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ):
    let F:=deck (G:=G) l d h
    let L:=R.family.path.levels
    ∃C B:Credit,∀ᶠ m:ℕ in atTop,∃Q:Realm G (e+1) Credit.leanC,
      Q.draws=L ∧ Q.paid=R.metals.O ∧ Q.y=zz L ∧ Q.anchor=m ∧
      Cloze d l Q Credit.leanC ∧
      (∀j,m ≤ j → ∀hj:Q.anchor ≤ j,∃z:5 ≤ L.clock.J (j+1),
        (Q.mint j hj).σ=crestM L j z ∧
        v (L.clock.J (j+1)) (Q.mint j hj).gear ≤ Q.cash Credit.leanC j) ∧
      ∀X:Herit F,∀N:ℕ,m ≤ N →
        let Y:=normalized Q.draws Q.paid F X m N
        let z:=zz L m + ∑ i,C.buy (zz L m)*fee (F i) (X i) e
        Borealis Q d l l (coatA Q.draws Q.paid N m F Y) m N B z:=by
  intro F L
  obtain ⟨C,active⟩:=WilsonMarkedIndependentNormalizedSingleton.fields R simple v funded l d h e
  obtain ⟨B,offer⟩:=dictated (hol G) F Credit.leanC Credit.leanC Credit.leanC Credit.leanC e
  refine ⟨C,B,?_⟩
  filter_upwards [active,FundedMarkedCoverRows.realm R simple v funded (a+1) l d h e 0 0] with m budget official
  obtain ⟨Q,level,ratio,clock,date,funds,_,⟨tribe⟩,crest⟩:=official
  refine ⟨Q,level,ratio,clock,date,funds,crest,?_⟩
  intro X N cut
  let Y:=normalized Q.draws Q.paid F X m N
  let A:=fun i=>C.buy (zz L m)*fee (F i) (X i) e
  let z:=zz L m+∑ i,A i
  have rent:Rent F Q.draws Q.paid (zz L) e m C X (fun i=>fee (F i) (X i) e):=by
    rw [level,ratio]
    exact budget X
  have table:=rent N N m le_rfl cut cut
  have pos(i):0 ≤ A i:=table.stock i
  have base:1 ≤ zz L m:=by rw [←clock];exact Q.depth m date.le
  have cost:Q.y m ≤ z:=by rw [clock];exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _=>pos i)
  refine offer Q tribe m N Y z date.le cut cost ?_
  intro i j hj u
  rw [Credit.lean_cost]
  have bound:‖coeff j (Y i u)‖ ≤ A i:=(table.track i j hj u).main
  have add:A i ≤ ∑ b,A b:=Finset.single_le_sum (fun i _=>pos i) (Finset.mem_univ i)
  exact bound.trans (add.trans (le_add_of_nonneg_left (by linarith)))

end YM.Integration.WilsonMarkedIndependentMixedEnrollment
end
