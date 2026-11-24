import YM.MS.ScaleForest.BridgeBlock
import YM.MS.ScaleForest.Inputs
/-!
# All-orders Laurent calculation as explicit forest sums

Keep the diagrams as in `Ordered`. Collect prior orders before gluing bridge
edges. Loops already closed with Rank estimate in `CloseBlock`. We may keep
entries even with not enough legs (their germs are 0). Use a shared palette
also when examining individual marks. `bulkSeries` and `atMark` are the
series independently defined with the UV scale regularized graph integrals
and the sign-weighted forest expansion, even BEFORE specialization to those
of four physical dimensions.

This already handles infrared regularization for ZERO and ONE marks at a
RETAINED length endpoint. Compare these Laurent series in that convention,
not the limit of each kernel as length→∞ (which need not make sense).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Mach Halo Emit Local.Physical
open scoped Topology ContDiff
variable {G : Gauge} {h n : ℕ} {b : Bool}

/-- Include all order partitions at bridges. In bulk both sides need
positive coupling-order, otherwise just the left (unmarked) side. -/
def parts (b : Bool) (n : ℕ) := (Finset.antidiagonal n).filter fun v=>0<v.1 ∧ (b=false ∨ 0<v.2)

theorem parts_mem (b : Bool) (n i j : ℕ) : (i,j) ∈ parts b n ↔ (i+j=n) ∧ (0 < i) ∧ (b=false ∨ 0 < j) := by simp [parts]

theorem allb (n : ℕ) : parts true n= shortB n := by
  ext p; simp only [parts,shortB,Finset.mem_filter,Finset.mem_antidiagonal,Bool.true_eq_false,false_or]; omega

theorem allm (n : ℕ) : parts false n= shortM n:= by
  ext p; simp only [parts,shortM,Finset.mem_filter,Finset.mem_antidiagonal,true_or,and_true]; omega

variable (P : Palette G)

def allBridges (L : T (Hist G true 4)) (R : T (Hist G b h)) (n : ℕ) :=
  (parts b n).toList.flatMap fun v=> everyBridge P (L v.1) (R v.2)

-- unfold/assembly

theorem bridges_compute (L : T (Hist G true 4)) (R : T (Hist G b h)) (n : ℕ) :
    Computes (allBridges P L R n) ((factor b:ℂ) • ∑ i∈ parts b n, drive0 G (renHistory ∘ L <| i.1) (renHistory (R i.2))) 0 := by
  have he := Computes.sums _ (parts b n).toList (fun i _ => every_computes P (L i.1) (R i.2))
  unfold allBridges; rw [Finset.smul_sum]
  simpa only [Function.comp, id_eq, Finset.sum_map_toList,Finset.sum_const_zero] using he

def through (A : T (Hist G b h)) (n : ℕ) (f : ∀ i (_:i<n), Hist G b h) : T (Hist G b h) :=
  fun i=> if he : i<n then f i he else A i

def bulks (P : Palette G) (n : ℕ) : Hist G true 4 := Nat.strongRecOn n (motive := fun _ => Hist G true 4) (fun n f=>
  if n=0 then [] else
    spiraling P (vertex (interaction G n)) ++ allBridges P (through (fun _ => []) n f) (through (fun _=> []) n f) n)

theorem flat_from {I V : Type} (f g : I → List V) (L : List I) (h : ∀ i∈L, f i=g i) : L.flatMap f=L.flatMap g := by
  induction L with
  | nil=> rfl
  | cons i L ih=> rw [List.flatMap_cons,List.flatMap_cons,h i (by simp),ih (fun i hi=> h _ (List.mem_cons_of_mem _ hi))]

theorem bulb (n : ℕ) : bulks P n= if n=0 then [] else
    spiraling P (vertex (interaction G n)) ++ allBridges P (bulks P) (bulks P) n := by
  unfold bulks; rw [Nat.strongRecOn_eq]; split; rfl; apply congr_arg ( _ ++ · ); unfold allBridges; apply flat_from
  intro i hi; obtain ⟨hi,hI⟩ := Finset.mem_filter.mp (show i∈shortB n from allb _ ▸ Finset.mem_toList.mp hi)
  rw [through, dif_pos hI.1,through,dif_pos hI.2]

def bulkSeries (P : Palette G) : T (Flats G) := fun n=> forest (bulks P n)
def bulkPoles (P : Palette G) : T (Coat G) := fun n=> poleHistory (bulks P n)

theorem hist_program (n : ℕ) : Computes (bulks P n) (Dock.program G n (renHistory ∘ bulks P))
    (gloss (pulseX G) n) := by
  rw (occs:=.pos [1]) [bulb P n]
  split; next h=>
    subst n; obtain ht : gloss (pulseX G) 0=0 := funext (fun _=>Up0 G); rw [ht];
    rw [show Dock.program G 0 (_ ∘ bulks P) =0 from (show program G 0 (renHistory ∘ bulks P) = 0 by simp [program, shortB])]
    exact Computes.nil ..
  rw [program]; have he:= Computes.app (primary_computes P (interaction G n)) (bridges_compute P (bulks P) (bulks P) n)
  rw [allb] at he
  unfold gloss
  simpa only [zero_add,add_zero,factor,if_true, gloss, Function.comp, interaction,Complex.ofReal_inv, Complex.ofReal_ofNat] using he

theorem bulk_path (n : ℕ) : PathD (Dock.program G) (bulkSeries P) (gloss (pulseX G)) (bulkPoles P)
    (fun i => i=0) true 0 4 n := by
  obtain ⟨r,hp⟩:=hist_program P n
  constructor
  · exact ⟨ r, block_accept (block_snapshot hp (panel_sum (bulks P n)))
        (pb_u _ _ _ (fun _ _=> panel_sum _))⟩
  rintro rfl
  rw [bulkSeries,bulb]; simp [forest]

theorem calculates_bulk : leader G (bulkSeries P) (gloss (pulseX G)) (bulkPoles P) := bulk_path P

-- For marks the same forest evaluator uses the nominated optics. General here
-- for use with components of labels and sums on the same height.
variable (V : T (LocalVertex G false h))

def marked (n : ℕ) : Hist G false h := Nat.strongRecOn n (motive := fun _ => Hist G false h) (fun n f =>
  spiraling P (vertex (V n)) ++ allBridges P (bulks P) (through (fun _=> []) n f) n)

theorem single_p (n : ℕ) : marked P V n = spiraling P (vertex (V n)) ++ allBridges P (bulks P) (marked P V) n := by
  unfold marked; rw [Nat.strongRecOn_eq]; apply congr_arg (_++·); unfold allBridges; apply flat_from
  intro i hi; obtain ht := Finset.mem_filter.mp (show i ∈ shortM n from allm _ ▸ Finset.mem_toList.mp hi)
  rw [through,dif_pos ht.2]

def atMark : T (Flats G) := fun n=> forest (marked P V n)
def markPoles : T (Coat G) := fun n=> poleHistory (marked P V n)

theorem hist_platform (n : ℕ) : Computes (marked P V n) (Dock.platform (renHistory ∘ bulks P) n (renHistory ∘ marked P V))
    (gloss (fun x=> (V x).symbol) n) := by
  rw [single_p]; have he:= Computes.app (primary_computes P (V n)) (bridges_compute P (bulks P) (marked P V) n)
  rw [allm] at he
  unfold gloss
  simpa only [zero_add,add_zero,gloss,platform, Function.comp, factor,Bool.false_eq_true,if_false,
    Complex.ofReal_one,one_smul] using he

theorem mark_path (n : ℕ) : PathD (platform (bulkSeries P)) (atMark P V) (gloss (fun x=>(V x).symbol)) (markPoles P V)
    (fun _=> False) false 0 h n := by
  obtain ⟨r,hp⟩:= hist_platform P V n
  exact ⟨⟨ r, block_accept (block_snapshot hp (panel_sum (marked P V n)))
     (pm_u (fun _=> panel_sum _) _ _ _ (fun _ _=> panel_sum _)) ⟩,fun h=> h.elim⟩

theorem computes_mark : comet h 0 (bulkSeries P) (gloss (fun x => (V x).symbol)) (atMark P V) (markPoles P V) := mark_path P V
end YM.MS.ScaleForest
