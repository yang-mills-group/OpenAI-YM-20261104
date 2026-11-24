import YM.Integration.WilsonReceivedCompactQRadiused

/-! Translations on the reporting torus move each of the two physical birth samplers
by the corresponding fine-grid translation without changing any child residue. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedCompactQOrbitSites
open Function Filter Lattice Wilson RG Extraction Cells MeasureTheory XSpace
open PhysicalNext.Repeat.Legato Finset WilsonReceivedCompactPriorIntegral
open WilsonReceivedCloseCompactStations
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) {i b:ℕ} (ib:i≤b) (per:ℕ)
local notation "Sites" d:max => Fin 3 → Site (R.family.side d per)
local notation "Bins" => (Sites ((b+1)+1))×(Sites (b+1))

def shift (y:Site (R.family.side i per)) (o:Bins):Bins :=
  (fun v=>o.1 v+(R.family.S.toDepth (ib.trans ((Nat.le_succ b).trans (Nat.le_succ (b+1)))) per).embed y,
   fun v=>o.2 v+(R.family.S.toDepth (ib.trans (Nat.le_succ b)) per).embed y)

def back (y:Site (R.family.side i per)) (o:Bins):Bins :=
  (fun v=>o.1 v-(R.family.S.toDepth (ib.trans ((Nat.le_succ b).trans (Nat.le_succ (b+1)))) per).embed y,
   fun v=>o.2 v-(R.family.S.toDepth (ib.trans (Nat.le_succ b)) per).embed y)

theorem shift_back (y:Site (R.family.side i per)) (o:Bins) : shift R ib per y (back R ib per y o)=o :=
  Prod.ext (funext fun _=>sub_add_cancel ..) (funext fun _=>sub_add_cancel ..)

theorem back_shift (y:Site (R.family.side i per)) (o:Bins) : back R ib per y (shift R ib per y o)=o :=
  Prod.ext (funext fun _=>add_sub_cancel_right ..) (funext fun _=>add_sub_cancel_right ..)

def sample (r:ℝ) (y:Site (R.family.side i per)) : Points 3→Bins := shift R ib per y ∘ cells R b per r

theorem measurable (r:ℝ) (y:Site (R.family.side i per)) : Measurable (sample R ib per r y) :=
  (measurable_of_countable (shift R ib per y)).comp (measurable_cells R b per r)

theorem weight (test:Test 3) (r:ℝ) (y:Site (R.family.side i per)) (o:Bins) :
    WilsonSeparatedOriginalThermometerCells.weight test (sample R ib per r y) (shift R ib per y o)=
    WilsonSeparatedOriginalThermometerCells.weight test (cells R b per r) o := by
  have injects:Injective (shift R ib per y):=LeftInverse.injective (back_shift R ib per y)
  have setEq:(sample R ib per r y ⁻¹' {shift R ib per y o})=(cells R b per r ⁻¹' {o}) := by
    ext x
    exact ⟨fun h=>injects h,fun h=>congrArg (shift R ib per y) h⟩
  unfold WilsonSeparatedOriginalThermometerCells.weight
  rw [setEq]

theorem address {d:ℕ} (it:i≤d) (y:Site (R.family.side i per)) (z:Site (R.family.side d per)) :
    let A:=R.family.S.toDepth it per
    A.parent (z+A.embed y)=A.parent z+y ∧ A.residue (z+A.embed y)=A.residue z := by
  let A:=R.family.S.toDepth it per
  have eq:A.assemble (A.parent z+y,A.residue z)=z+A.embed y:=by
    change A.embed (A.parent z+y)+wrap _ (lift (A.residue z))=z+A.embed y
    rw [show A.embed (A.parent z+y)=A.embed (A.parent z)+A.embed y from A.root.map_add ..]
    calc _=(A.embed (A.parent z)+wrap _ (lift (A.residue z)))+A.embed y:=by abel
         _=z+A.embed y:=by rw [A.unpack_at]
  have invoice:A.splitSites (A.assemble (A.parent z+y,A.residue z))=(A.parent z+y,A.residue z):=A.splitSites.apply_symm_apply _
  rw [eq] at invoice
  exact ⟨congrArg Prod.fst invoice,congrArg Prod.snd ((A.unpack _).trans invoice)⟩

theorem roots (y:Site (R.family.side i per)) (old:Finset (Fin 3)) (o:Bins) (v:Fin 3) :
    WilsonReceivedCompactMixedSites.roots R ib per old (shift R ib per y o) v =
      WilsonReceivedCompactMixedSites.roots R ib per old o v+y := by
  simp only [WilsonReceivedCompactMixedSites.roots,shift]
  split_ifs
  · exact (address R per _ y _).1
  · exact (address R per _ y _).1

theorem original (simple:G.Simple) (test:Test 3) (late:WilsonReceivedCompactQRadiused.floor R simple test ≤ i)
    (r:ℝ) (fit:|r|≤R.family.S.a i) (y:Site (R.family.side i per)) (old:Finset (Fin 3)) (o:Bins)
    (live:WilsonSeparatedOriginalThermometerCells.weight test (sample R ib per r y) o≠0) :
    Nonempty (Housing (R.family.path.levels.budget i).B y (WilsonReceivedCompactMixedSites.roots R ib per old o)) := by
  let s:=back R ib per y o
  have eq:shift R ib per y s=o:=shift_back R ib per y o
  have paid:WilsonSeparatedOriginalThermometerCells.weight test (cells R b per r) s≠0:=by
    rwa [←weight R ib per test r y s,eq]
  have filed:=Classical.choose_spec (eventually_atTop.mp (WilsonReceivedCompactMixedSites.original R simple test))
  obtain ⟨H⟩:=filed i late b per ib r fit old s paid
  let B:=(R.family.path.levels.budget i).B
  have near (v:Fin 3) : separation (WilsonReceivedCompactMixedSites.roots R ib per old o v) y≤B := by
    rw [←eq,roots]
    have translated:=separation_translate (WilsonReceivedCompactMixedSites.roots R ib per old s v) 0 y
    exact (show separation (WilsonReceivedCompactMixedSites.roots R ib per old s v+y) y =
      separation (WilsonReceivedCompactMixedSites.roots R ib per old s v) 0 by simpa only [zero_add] using translated).le.trans ((H.close v).trans H.bound)
  refine ⟨⟨halo B {y},?_,?_,B,near,le_rfl,fun _ h=>h⟩⟩
  · exact YM.Lattice.halo_subset B {y} (Finset.mem_singleton_self _)
  · intro v
    exact halo_spec.mpr ⟨y,mem_singleton_self _,by simpa only [separation_comm y] using near v⟩

end YM.Integration.WilsonReceivedCompactQOrbitSites
