import YM.MS.ScaleForest.LineSums
/-!
# Complement loops at fixed order

How many? For n remaining free legs loop at most floor(n/2) times. Include
the trivial (zero-sized) extension at all steps, always count each entry of
the palette once, doing oriented Wick contractions with `loop`. For each verified family
these closures, not a cutoff on coupling order, achieve the requisite
`Bob`. Prove it per sum-family, including families which themselves use
something specific rather than the whole sum of lower-order graphs. We'll
also combine results with COMPLETE lower-order graph sums with pole/prepared
aggregation in the same convention.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {h n : ℕ} {b : Bool} {r u : ℤ} {X Y J L : Flats G} {f g p q : Coat G}

-- Histogram operations
abbrev Hist (G : Gauge) (b : Bool) (h : ℕ) := List (GraphSum G b h)

def renHistory (H : Hist G b h) := (H.map (fun F => F.instructions.renorm)).sum
def poleHistory (H : Hist G b h) := (H.map (fun F=> F.instructions.pole)).sum
/-- Also the genuinely distributed sum; count all choices of subtractions
along with graph multiplicities. -/
def forest (H : Hist G b h) := (H.flatMap GraphSum.quotients).sum

theorem ren_cons (a : GraphSum G b h) (H : Hist G b h) : renHistory (a::H)= a.instructions.renorm + renHistory H := rfl

theorem pole_cons (a : GraphSum G b h) (H : Hist G b h) : poleHistory (a::H)= a.instructions.pole + poleHistory H := rfl
@[simp] theorem ren_nil : renHistory ([] : Hist G b h) = 0 := rfl
@[simp] theorem pole_nil : poleHistory ([] : Hist G b h) = 0 := rfl

theorem ren_append (L M : Hist G b h) : renHistory (L++M)= renHistory L + renHistory M := by simp [renHistory]
theorem pole_append (L M : Hist G b h) : poleHistory (L++M)= poleHistory L + poleHistory M := by simp [poleHistory]
theorem forest_cons (a : GraphSum G b h) (H : Hist G b h) : forest (a::H)= a.quotients.sum+forest H:= by simp [forest]

theorem panel_sum (H : Hist G b h) : Pact (renHistory H) (forest H) := by
  induction H with
  | nil=> exact same_pact _
  | cons i H ih=> rw [forest_cons,ren_cons]; exact common i.forest_summed ih

theorem block_plus (hr : Bob b h 0 r J X f p) (ht : Bob b h 0 r L Y g q) : Bob b h 0 r (J+L) (X+Y) (f+g) (p+q) := by
  refine ⟨?_,Cap0.heap.plus hr.2.1 ht.2.1,hr.2.2.add ht.2.2⟩
  rw [map_add]; convert (hr.1.plus ht.1) using 1; abel

theorem block_raise (hr : Bob b h 0 r J X f p) (he : r ≤ u) : Bob b h 0 u J X f p :=
  ⟨hr.1,clockTrans hr.2.1 he,hr.2.2.collects he⟩

theorem block_zero (b : Bool) (h : ℕ) (r : ℤ) : Bob b h 0 r 0 (0:Flats G) 0 0 := by
  rw [Bob,map_zero,add_zero]; exact ⟨Joint.zero,(coal_zero b h 0 r).eye,Cap0.zero⟩

theorem block_accept (he : Bob b h 0 r J X f p) (hu : Pact J L) : Bob b h 0 r L X f p :=
  ⟨he.1.via (common hu (same_pact _)),he.2⟩

theorem joint_snapshot (hJ : Joint h J X f p) (he : Pact X Y) : Joint h J Y f p :=
  { hJ with
    advance := vibe_trans hJ.advance he (same_pact _)
    toll := fun y s=> Live.congr (hJ.toll y s) (prom he h s y)
    wet := fun i => (hJ.wet i).congr (he i)
    sip := return_congr hJ.sip he }

theorem block_snapshot (he : Bob b h 0 r J X f p) (hu : Pact X Y) : Bob b h 0 r J Y f p :=
    ⟨(joint_snapshot he.1 hu).via (common (same_pact _) (Cycle_t hu)),
      clockWind he.2.1 hu, he.2.2⟩

theorem block_sum {I : Type} (F : I → Hist G b h) (Z : I → Flats G) (P : I→Coat G)
    (L : List I) (hr : ∀ i∈L, Bob b h 0 r (Z i) (renHistory (F i)) (P i) (poleHistory (F i))) :
    Bob b h 0 r (L.map Z).sum (renHistory (L.flatMap F)) (L.map P).sum (poleHistory (L.flatMap F)) := by
  induction L with
  | nil=> exact block_zero ..
  | cons i L ih=>
    simp only [List.map_cons, List.sum_cons,List.flatMap_cons,ren_append,pole_append]
    exact block_plus
          (hr i (by simp)) (ih (fun x hx=> hr x (List.mem_cons_of_mem _ hx)))

/-- Close with any line, zero to k times. -/
def allLoops (P : Palette G) : ℕ → GraphSum G b h → Hist G b h
| 0, A => [A]
| n+1, A => A :: P.lines.flatMap (fun K=> allLoops P n (loop K A))

def spiraling (P : Palette G) (A : GraphSum G b h) := allLoops P (A.slots.toNat /2) A

theorem close_all (P : Palette G) (k : ℕ) (A : GraphSum G b h) (hf : A.slots < 2 + 2*(k:ℤ)) :
    Bob b h 0 A.slots A.instructions.force (renHistory (allLoops P k A)) A.instructions.classicalTerm (poleHistory (allLoops P k A)) := by
  let V:= step0 G
  induction k generalizing A with
  | zero=>
    let E:= V A.instructions.renorm
    have he := A.accepted
    have HH := mine he.usable.clock he.after.toll
    have ht : Pact E 0 := pact0 ⟨A.slots-2,by omega,clockCap HH.eye⟩
    have hv := common (same_pact A.instructions.force) (pact_sym ht)
    rw [add_zero] at hv
    simp only [allLoops,ren_cons,pole_cons,ren_nil,pole_nil,add_zero]; exact ⟨he.after.via hv,he.usable.clock,he.poleShape⟩
  | succ k ih=>
    let L(K:LineRule G):= allLoops P k (loop K A)
    obtain ht:= block_sum L (fun K=> (loop K A).instructions.force) (fun _=>0) P.lines (r:=A.slots-2)
      (fun K _=> ih (loop K A) (show _ from (by change A.slots-2<2+2*(k:ℤ); omega)))
    have he : ((P.lines.map (fun _=> (0:Coat G))).sum)=0 := by simp
    rw [he] at ht
    have hP:= block_accept (block_raise ht (show A.slots-2≤ A.slots by omega))
                    (combine_loop P _ (clockMoon A.accepted.usable.clock))
    simp only [allLoops,ren_cons,pole_cons]
    refine ⟨?_, Cap0.heap.plus A.accepted.usable.clock hP.2.1,A.accepted.poleShape.add hP.2.2⟩
    rw [map_add]; simpa only [add_zero] using A.accepted.after.plus hP.1

theorem spire_block (P : Palette G) (A : GraphSum G b h) : Bob b h 0 A.slots
    A.instructions.force (renHistory (spiraling P A)) A.instructions.classicalTerm (poleHistory (spiraling P A)) :=
  close_all P _ A (by omega)
end YM.MS.ScaleForest
