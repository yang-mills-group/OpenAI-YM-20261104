import YM.MS.ScaleForest.ColumnSums
/-!
# Picking out terms from the actual forest sums, retaining the others

For reporting. Here we have taken UV limits at fixed
log-length and specialize four-series readout at that scale after the
subtractions. Later limits on projected physical readers can require further
sums, convolutions etc; don't assert those limits on individual subgraphs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Mach Halo Emit Local.Physical
open Land Outlook
open scoped Topology ContDiff
variable {G : Gauge} {h k n m : ℕ} {b : Bool} {P : Palette G} {x : GraphSum G b h}
  {u : GraphSum G true 4} {v : GraphSum G b h} {K : LineRule G} {L : Hist G b h}

theorem stay_history (T : Hist G b h) : Stay h (forest T) := by
  have he : Stay h (renHistory T) := by
    induction T with
    | nil => exact Joint.zero.toll
    | cons i T ih=> rw [ren_cons]; exact Stay_add i.accepted.after.toll ih
  exact fun y s=> Live.congr (he y s) (Train.prom (panel_sum T) h s y)

/-- Means a limit of Laurent germs. Junk at 0 is never evaluated. -/
theorem finite_read (H : Hist G b h) (l : Legs (Shore G 0)) (y s : ℝ) : Tendsto
    (fun z => Parade (forest H) h y s z 0 l) dotty (𝓝 (four h (forest H) (y,s) l)) :=
  Lift.wind (Rub (stay_history H y s) 0) 0 l

-- If an entry has been demonstrated, report the amount from it plus the rest.
def afterTaking (L : Hist G b h) (x : GraphSum G b h) := open Classical in L.erase x

theorem including (hx : x∈L) : Pact (forest L) (x.instructions.renorm+forest (afterTaking L x)) ∧
    poleHistory L=x.instructions.pole+poleHistory (afterTaking L x) := by
  classical
  unfold afterTaking
  have he : List.Perm (x::L.erase x) L := (List.perm_cons_erase hx).symm
  have hv : renHistory L=renHistory (x :: L.erase x) := (he.map (fun x : GraphSum G b h=>x.instructions.renorm)).sum_eq.symm
  refine ⟨ pact_comp (pact_sym (panel_sum L)) ?_,(he.map (fun x : GraphSum G b h => x.instructions.pole)).sum_eq.symm⟩
  have hu : renHistory L= x.instructions.renorm+renHistory (L.erase x) := hv
  rw [hu]; exact common (same_pact _) (panel_sum _)

theorem final_including (hx : x∈L) : four h (forest L)=four h x.instructions.renorm+four h (forest (afterTaking L x)) := by
  funext ⟨y,s⟩ l; refine congr_fun (congr_fun (Lift.unique (H:=ruby (Parade x.instructions.renorm h y s) 0 + ruby (Parade (forest (afterTaking L x)) h y s) 0) (Rub (stay_history L y s) 0) ?_) 0) l
  refine Lift.congr (Lift.add (Rub (x.accepted.after.toll y s) 0) (Rub (stay_history (afterTaking L x) y s) 0)) ?_
  rw [ ← page_add ]; exact Train.prom (pact_sym (including hx).1) h s y

theorem closed_mem (x : GraphSum G b h) (P : Palette G) (n : ℕ) : x∈allLoops P n x := by cases n <;> simp [allLoops]

theorem loop_mem {n : ℕ} (ht : x∈ allLoops P n (loop K v)) (hK : K∈ P.lines) : x∈allLoops P (n+1) v := by
  rw [allLoops]; exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨ K,hK,ht⟩)

theorem every_mem {L : Hist G true 4} {M : Hist G b h} (hu : u∈L) (hv : v∈M) (hK : K∈P.lines) (hm : x∈spiraling P (bridge K u v)) :
    x∈everyBridge P L M := List.mem_flatMap.mpr ⟨ _,hu,List.mem_flatMap.mpr ⟨ _,hv,List.mem_flatMap.mpr ⟨ _,hK,hm⟩⟩⟩

theorem convolution_mem {L : T (Hist G true 4)} {M : T (Hist G b h)} (hu : (n,m)∈ parts b k) (hm : x∈everyBridge P (L n) (M m)) :
    x∈allBridges P L M k := List.mem_flatMap.mpr ⟨ (n,m),Finset.mem_toList.mpr hu,hm⟩

theorem bulk_node (ht : 0<n) (hm : u∈ spiraling P (vertex (interaction G n))) : u∈bulks P n := by
  rw [bulb, if_neg ht.ne']; exact List.mem_append_left _ hm

theorem bulk_branch (hu : (n,m)∈ parts true k) (hm : u∈everyBridge P (bulks P n) (bulks P m)) :
    u∈ bulks P k := by
  obtain h := (parts_mem ..).mp hu; rw [bulb,if_neg (by omega)]; exact List.mem_append_right _ (convolution_mem hu hm)

theorem mark_node {W : T (LocalVertex G false h)} {v : GraphSum G false h} (ht : v∈ spiraling P (vertex (W n))) :
    v∈marked P W n := by rw [single_p]; exact List.mem_append_left _ ht

theorem mark_branch {W : T (LocalVertex G false h)} {v : GraphSum G false h} (hu : (n,m)∈ parts false k)
    (hv : v∈ everyBridge P (bulks P n) (marked P W m)) : v∈ marked P W k:= by
  rw [single_p]; exact List.mem_append_right _ (convolution_mem hu hv)
end YM.MS.ScaleForest
