import YM.MS.Graphical.Leading
import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.Enumeration
import YM.Integration.FVA1Physical.Exchange.CalibratedExpansionExternalMSRecursion

/-!
# Assembly into the filed MS-bar programs

Now add the ordered sector families with their forest insertions. From our
own pole and integrals we derive `Dock.leader` (driven by `program`) and
`Dock.comet` (driven by `platform` on the bulk we calculated): the `PathD`
recursions at *every* perturbative order. We calculate on the native bare
exponent and, for the client result on physical marks, on precisely the
indicated opticked seeds, not assuming equality of graph operands with any
other streams of solutions. Thus we can apply the library germ theorems;
no common *lattice* trajectory hypothesis is used in this argument.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open Lattice Cylinder Motif Literal Halo Outlook Mach Emit Local.Physical Land Menus
open scoped Topology ContDiff BigOperators
namespace Diagram
variable {G : Gauge} {a : ℕ→ Mob G} {h n j k : ℕ} {g : Diagram} {b : Bool} {f : Coat G}
    {X : Flats G} {p : ℤ}

lemma bob_total {u : Multiset Diagram} (J F : Diagram → Flats G)
    (p q : Diagram → Coat G) (hd : ∀ i∈ u, Bob b h 0 (k:ℤ) (J i) (F i) (p i) (q i)) :
    Bob b h 0 (k:ℤ) (total u J) (total u F) (total u p) (total u q) := by
  induction u using Multiset.induction with
  | empty=> simp only [total, Multiset.map_zero,Multiset.sum_zero]; unfold Bob; rw [map_zero,add_zero]; exact ⟨ Joint.zero, fun _=> Cap0.zero, Cap0.zero ⟩
  | cons g u ih=>
    simp only [total, Multiset.map_cons, Multiset.sum_cons]; exact bob_add _ (hd g (by simp))
      (ih fun i hi=> hd i (Multiset.mem_cons_of_mem hi))

lemma all_bases (u : Multiset Diagram) (hr : Is b n u) (he : ∀ i, VertexOK false h (a i)) :
    Bob b (dimTarget h b) 0 (rankRoom h b n : ℕ)
      (total u (fun i => input a h i b))
      (allPages h a (tower b h n u) b)
      (total u (fun i=> initialVertex a i b)) (allCT h a (tower b h n u) b) := by
  unfold allPages allCT tower; rw [total_bind,total_bind]; apply bob_total
  intro i hi; obtain ⟨ht,hp⟩:= hr i hi; exact wide_ladder h a b i (rankRoom h b n) hp (by rw [ht]) he

lemma total_junction {u v : Multiset Diagram} :
    total (u.bind fun i=> v.map (fun j=>merge i j)) (fun k=>input a h k b)=
       fee b • drive0 G (allPages h a u true) (allPages h a v b) := by
  rw [total_bind]; unfold allPages;
  let p := fun g => (evaluate G a h g true).pages; let q := fun g => (evaluate G a h g b).pages
  have H (i : Diagram) (l : Multiset Diagram) :
      total (l.map (fun j=>merge i j)) (fun k=>input a h k b) = fee b • drive0 G (p i) (total l q) := by
    induction l using Multiset.induction with
    | empty => simp [total]
    | cons k l ih =>
       unfold total; simp only [Multiset.map_cons,Multiset.sum_cons,map_add,smul_add]
       exact congr_arg₂ (·+·) (by rw [input,bridgeForce_eq]) ih
  simp_rw [H]
  induction u using Multiset.induction with
  | empty => simp [total]
  | cons i u ih =>
    simp only [total,Multiset.map_cons,Multiset.sum_cons,map_add,LinearMap.add_apply,smul_add]
    exact congr_arg₂ (·+·) rfl ih

lemma all_total_forcing (S : Finset (ℕ×ℕ)) (L R : ℕ→ Multiset Diagram) :
    total (distributeS S L R) (fun k=> input a h k b) =
      fee b • ∑ p∈S, drive0 G (allPages h a (L p.1) true) (allPages h a (R p.2) b) := by
  unfold distributeS
  rw [total_bind]; simp_rw [total_junction]; simp only [Finset.smul_sum]; rfl
lemma all_tree_seeds (S : Finset (ℕ×ℕ)) (L R : ℕ→ Multiset Diagram) :
    total (distributeS S L R) (fun k=> initialVertex a k b) = 0 := by
  unfold distributeS; rw [total_bind]; simp_rw [total_bind]; simp [total,initialVertex]

variable (G)
lemma eval_ambient (q : ℕ→Mob G) (j : ℕ) (g : Diagram) : evaluate G a h g true=evaluate G q j g true:= by
  induction g with
  | lit n=> rw [evaluate,evaluate]; rfl
  | close g ih => rw [evaluate,evaluate,ih]; rfl
  | merge g f ih h => rw [evaluate,evaluate,ih,h]; rfl


/-- Pole table for the unmarked exponent, with **counterterm sign** included. -/
def bulkCT (n : ℕ) := allCT 4 (0:ℕ→ Mob G) (ambient n) true
lemma bulk_P (a : ℕ→Mob G)(n h : ℕ) : allPages h a (ambient n) true = bulk G n:= by
  unfold bulk allPages; exact total_congr _ _ _ (fun i hi=> congr_arg _ (eval_ambient G ..))

theorem ambient_bob (n : ℕ) :
   Bob true 4 0 (↑(rankRoom 4 true n)) (program G n (bulk G)) (bulk G n)
      (gloss (pulseX G) n) (bulkCT G n) := by
  by_cases ht : n = 0
  · subst n; unfold program bulkCT bulk allPages allCT shortB; rw [ambient_zero];
    rw [show gloss (pulseX G) 0 = 0 from funext (fun _=> (Up0 G))]
    simp only [Nat.antidiagonal_zero, total, Multiset.map_zero,Multiset.sum_zero]
    rw [Finset.filter_false_of_mem (by simp)] -- false filter
    rw [Finset.sum_empty,smul_zero,Bob,map_zero,zero_add]; exact ⟨Joint.zero, fun i=> Cap0.zero,Cap0.zero⟩
  let S := shortB n; let u := {lit n}+distributeS S ambient ambient
  obtain h : Is true n u := Is.sum (Is.litV (fun _=> by omega))
    (Is.dist (fun i _=> is_ambient i.1) (fun i _=> is_ambient i.2) (Finset.filter_subset ..))
  have hz := all_bases u h (show ∀ i, VertexOK false 4 ((0:ℕ→ Mob G) i) from
     fun _=> ⟨fun _=>Home.zero _,Cap0.zero⟩)
  unfold u at hz; rw [total_add,total_add,all_total_forcing,all_tree_seeds] at hz
  have he : tower true 4 n u=ambient n := (ambient_unfold (by omega : 0<n)).symm
  rw [he] at hz
  simp only [total,Multiset.map_singleton,Multiset.sum_singleton,input,initialVertex,zero_add,
        add_zero] at hz; exact hz

/-- Bulk recursion realized by the graph operands. -/
theorem preparation : leader G (bulk G) (gloss (pulseX G)) (bulkCT G) := fun n=>
  ⟨⟨_,ambient_bob G n⟩, fun hn=> hn.symm ▸ (show bulk G 0 = 0 from by
      unfold bulk allPages; rw [ambient_zero]; simp [total])⟩


/-- Marked pole table with the same signs as `bulkCT`. -/
def sectorCT (h : ℕ) (a : ℕ → Mob G) (n : ℕ) : Coat G := allCT h a (insertions h n) false

lemma mark_bob (hp : ∀ i, VertexOK (G := G) false h (a i)) (n : ℕ) :
    Bob false h 0 (↑(rankRoom h false n)) (platform (bulk G) n (sectorMark G h a)) (sectorMark G h a n)
      (gloss a n) (sectorCT G h a n) := by
  let S := shortM n; let u := {lit n}+distributeS S ambient (insertions h)
  have he : Is false n u := Is.sum (Is.litV (by simp))
    (Is.dist (fun i _=> is_ambient i.1) (fun i _=> is_insertions h i.2) (Finset.filter_subset ..))
  obtain hv:= all_bases u he hp
  unfold u at hv; rw [total_add,total_add,all_total_forcing,all_tree_seeds] at hv
  rw [show tower false h n u = insertions h n from (mark_unfold h n).symm] at hv
  simp only [total,Multiset.map_singleton,Multiset.sum_singleton,input,initialVertex,zero_add,
        add_zero,fee,Bool.false_eq_true,↓reduceIte,one_smul] at hv
  simp_rw [bulk_P G a _ h] at hv
  exact hv

/-- Marked recursion, height-h, with the actual bulk series in `platform`. -/
theorem contracted (a : ℕ → Mob G) (hp : ∀ i, VertexOK false h (a i)) :
    comet h 0 (bulk G) (gloss a) (sectorMark G h a) (sectorCT G h a) := fun n=>
  ⟨⟨_,mark_bob G hp n⟩,fun h=>h.elim⟩

variable {G}

theorem income_bulk {D : Deck G} {A : Booked D} (T : MS_Data G A) :
    bulkCT G = T.poleS ∧ ∀ i, Pact (bulk G i) (T.bulk i) :=
  original_external_bulk_germ T (preparation G)

theorem contracts_seed {D : Deck G} (A : Booked D) (h : ℕ) (v : Plaid D h) (n : ℕ) :
    VertexOK false h (sectorSeed A h v n) := mark_ok _ _ _ (A.law h v) n

/-- Every nominated physical mark, with exact pole (as a function) and
germ equality for every page. Does *not* assert equality at z=0 on
representatives of punctured-regulator germs. -/
theorem income_mark {D : Deck G} {A : Booked D} (T : MS_Data G A) (h : ℕ) (v : Plaid D h) :
    let s := sectorSeed A h v
    sectorCT G h s = T.poles h v ∧ ∀ i, Pact (sectorMark G h s i) (T.marks h v i) :=
  original_external_marked_germ T (preparation G) h v
    (contracted G (sectorSeed A h v) (fun i=>contracts_seed A h v i))
end Diagram
end YM.MS.Graphical
