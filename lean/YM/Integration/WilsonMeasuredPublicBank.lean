import YM.Integration.WilsonMeasuredPublicSlots

/-! The same genuine station and change of frame for all public coordinates of one grade and date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicBank
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams GapsContact.Stamps PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land Trace.Terrace MergeProof.East
open WilsonMeasuredPublicSlots WilsonThermometerUnitFilingFourPoolShell
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (l : Ultrafilter (ℕ×ℕ))

structure Department (d j m : ℕ) (s B : ℝ) where
  calendar : ∀ n,Vane R.family n
  station : ℕ
  high : d ≤ station
  frame : Spin.change S d
  located : (calendar station).k = j
  aperture : purchaseWidth (calendar station) = m
  print (v : S.Field d) : Slot F l d v s B
  dated v : (print v).j=j ∧ (print v).m=m
  original (v : S.Field d) (q : ℕ×ℕ) : (print v).arm.source q =
    (calendar station).wheel.atCut q ⟨d,Nat.lt_succ_of_le high⟩ (frame.symm v)

structure Bank (D : ℕ) (s B : ℝ) where
  j : ℕ
  m : ℕ
  department (d : ℕ) (cap : d≤D) : Department F l d j m s B

theorem purchased {j m D : ℕ} {s B : ℝ}
    (pool : WilsonThermometerUnitFilingFourPool.Receipt F l s j m D B) :
    ∃ stock : Bank F l D s B, stock.j=j ∧ stock.m=m := by
  have issue (d : ℕ) (cap : d≤D) : Nonempty (Department F l d j m s B) := by
    let card := pool.budget d cap
    obtain ⟨V,n,hn,T,hj,hm,depot⟩ := WilsonThermometerUnitFilingFourPoolArms.sharp card
    choose arm joined num cards using depot
    let print (v:S.Field d) : Slot F l d v s B :=
      ⟨j,m,card.owns,pool.fore,pool.breadth,pool.front,arm v,V,n,hn,T,hj,hm,joined v,
        fun N p live => by simpa only [mul_assoc] using num v N p live,cards v⟩
    exact ⟨⟨V,n,hn,T,hj,hm,print,fun _=>⟨rfl,rfl⟩,joined⟩⟩
  exact ⟨⟨j,m,fun d cap=>(issue d cap).some⟩,rfl,rfl⟩

theorem before {z : Trace.Terrace.Arch R.family} {H : (Bel R.family.book).Hierarchy}
    (simple : G.Simple) (bliss : Bliss F l z H) (D:ℕ) :
    ∃ T : ℕ, ∀ (A : Type) [Fintype A] (dates : A→ℝ→ℝ),
    (∀a,Tendsto (dates a) trail trail) → ∀ᶠ r in trail,Nonempty
      (∀a,Bank F l D (radius z T (dates a r)) (dock (radius z T (dates a r))^T)) := by
  obtain ⟨T,pools⟩ := WilsonThermometerUnitFilingFourPool.original F simple bliss D
  refine ⟨T,?_⟩
  intro A _ dates tend
  filter_upwards [eventually_all.mpr fun a=>(tend a).eventually ((smaller F simple bliss T).eventually pools)] with r booked
  refine ⟨fun a=>?_⟩
  exact (purchased F l (booked a).choose_spec.choose_spec).choose

end YM.Integration.WilsonMeasuredPublicBank
