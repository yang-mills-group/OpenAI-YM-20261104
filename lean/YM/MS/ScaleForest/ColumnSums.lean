import YM.MS.ScaleForest.Reaching

/-!
# Real-linear source specification (and hence its columns can be evaluated)

`comet` is specified with reality properties. Prove the lemma directly for
real linear combinations, using the Laurent symbols themselves. Complex
coefficients in a physical multilinear reading can of course later use the
same sums (Laurent identity and finite-part evaluation really are linear over
the complex numbers). We will not assume `comet`'s additional (e.g. reality)
laws for a non-real linear combination.

Can be used on **all** allowed height/slot columns including lower and unit.
In particular this is still a comparison at the unconverted vertex level;
it doesn't say that a prescription is just this linear rule. Finite field
changes need the other comparisons too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Mach Halo Emit Local.Physical
open Land Outlook FVA2.Position FVA2.Position.OpenAxis
open scoped Topology ContDiff
variable {G : Gauge} {h n : ℕ} {D : Deck G} {A : Land.Booked D} {BULK : T (Flats G)}
  {X Y : T (Flats G)} {p q U V : T (Coat G)}

theorem sums_comet (ht : comet h 0 BULK U X p) (hv : comet h 0 BULK V Y q) : comet h 0 BULK (U+V) (X+Y) (p+q) := by
  intro i; obtain ⟨⟨u,hU⟩,_⟩:= ht i; obtain ⟨⟨v,hV⟩,_⟩:= hv i
  refine ⟨⟨max u v,?_⟩, fun h=>h.elim⟩
  rw [show platform BULK i (X+Y)= platform BULK i X+platform BULK i Y from ?_]
  exact block_plus (block_raise hU (le_max_left u v)) (block_raise hV (le_max_right u v))
  unfold platform; simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]

theorem scales_comet (ht : comet h 0 BULK U X p) (x : ℝ) : comet h 0 BULK ((x:ℂ) • U) ((x:ℂ) • X) ((x:ℂ) • p) := by
  intro i; obtain ⟨⟨u,hU,hA,hP⟩,_⟩:= ht i
  refine ⟨⟨u,?_⟩, fun h=>h.elim⟩; obtain hz : star (x:ℂ)=(x:ℂ) := by simp
  have he := hU.scale (x:ℂ)
  simp only [Bob,platform,Pi.smul_apply,map_smul,← Finset.smul_sum]
  exact ⟨smul_add (x:ℂ) (platform BULK i X) (step0 G (X i)) ▸ he,fun j=>(hA j).smul hz,hP.smul hz⟩

theorem finite_comet {I : Type} {X : I → T (Flats G)} {u p : I→ T (Coat G)} (S : Finset I)
    (ht : ∀ i∈S, comet h 0 BULK (u i) (X i) (p i)) :
    comet h 0 BULK (∑ i∈S,u i) (∑ i∈S,X i) (∑ i∈S,p i) := by
  classical
  induction S using Finset.induction with
  | empty=> simp only [Finset.sum_empty]; intro i; rw [PathD,show platform BULK i 0=0 from ?_]; exact zero_sing _; simp [platform]
  | insert i x hx ih=> simp only [Finset.sum_insert hx]; exact sums_comet (ht i (by simp)) (ih (fun j hj=> ht j (Finset.mem_insert_of_mem hj)))

/-- Put heights in `Nat` convention. Slot count r does not name n in the
coupling graph expansion. -/
def nameColumn (r : Fin (h+1)) (i : D.BIndex h r.val) : Plaid D h := ⟨r,i⟩
section physical
variable (P : Palette G) (r : Fin (h+1))
local notation "ι"=> D.BIndex h r.val
local notation "R"=> D.carries (h:ℤ) r.val
variable (z : D.carries (h:ℤ) r.val)

abbrev coords (i : (D.BIndex h r.val)) := (Module.finBasis ℝ (D.carries (h:ℤ) r.val)).repr z i

def nominated := invoice G h r.val (Theater.Resume D h r.val z)

def byColumn (x : Land.Plaid D h → T (Flats G)) : T (Flats G) :=
  ∑ i:ι, (coords r z i:ℂ) • x ⟨r,i⟩
def poleColumn (x : Land.Plaid D h → T (Coat G)) : T (Coat G) :=
  ∑ i:ι, (coords r z i:ℂ) • x ⟨r,i⟩

theorem linear_coord : nominated r z= ∑ i:ι, (coords r z i:ℂ) • (Plot D).optics h ⟨r,i⟩ := by
  have hA : z=∑ i:ι, (coords r z i : ℝ) • (Module.finBasis ℝ R) i := ((Module.finBasis ℝ R).sum_repr z).symm
  unfold nominated
  nth_rw 1 [hA]
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl; intro i _; -- need real→ℂ
  rw [← IsScalarTower.algebraMap_smul ℂ (coords r z i)]
  rfl

theorem bill_column : gloss (Literal.linear _ (nominated r z)) =
    ∑ i:ι, (coords r z i:ℂ) • gloss (Literal.linear _ ((Plot D).optics h ⟨r,i⟩)) := by
  rw [linear_coord]; unfold gloss; ext k f m l; simp only [map_smul,map_sum, Finset.sum_apply,Pi.smul_apply]

variable (F : Land.MS_Data G (Plot D))

theorem summed_plane : comet h 0 F.bulk (gloss (Literal.linear _ (nominated r z)))
    (byColumn r z (F.marks h)) (poleColumn r z (F.poles h)) := by
  rw [bill_column]; exact finite_comet Finset.univ (fun i _=> scales_comet (F.markOK h ⟨r,i⟩) (coords r z i))

def columnV : T (LocalVertex G false h) := withSource (nominated r z) (invoiceC (Theater.Resume D h r.val z))

theorem column_id : markPoles P (columnV r z)=poleColumn r z (F.poles h) ∧
    ∀ n, Pact (atMark P (columnV r z) n) (byColumn r z (F.marks h) n) :=
  unique_M (computes_mark P (columnV r z)) (summed_plane r z F) (germ_bulk P F).2

theorem column_arch : Archive h (atMark P (columnV r z))= Archive h (byColumn r z (F.marks h)) := by
  funext n ⟨y,s⟩; refine congr_fun (Lift.unique ?_ (Rub ((gang (summed_plane r z F n)).dost y s) 0)) 0
  exact Lift.congr (Rub ((gang (computes_mark P (columnV r z) n)).dost y s) 0) (prom ((column_id P r z F).2 n) h s y)

-- Specialization is linear over ℂ, even when taking columns in different slots.
theorem specializes {I : Type} (x : I → Flats G) (S : Finset I) (c : I→ℂ) (F : Flats G) (he : ∀ i∈S,Stay h (x i))
    (ht : Pact F (∑ i∈S, c i • x i)) : four h F=∑ i∈S, c i•four h (x i) := by
  funext ⟨y,s⟩
  obtain hp := Pick.fin S (fun i hi=> ( Rub (he i hi y s) 0).static (c i))
  have hv : ∑ i∈S, c i • Parade (x i) h y s=Parade (∑ i∈S,c i • x i) h y s := by
    rw [page_sum]; refine Finset.sum_congr rfl fun i _ => ?_;
    rw [page_smul]
  have hy := (hp.congr (hv.symm ▸ (prom (pact_sym ht) h s y)))
  have hz := congr_fun (chosen hy) 0; simp_rw [Finset.sum_apply,Pi.smul_apply] at hz ⊢
  exact hz.symm

theorem column_read : Archive h (atMark P (columnV r z)) = ∑ i:ι,(coords r z i:ℂ) • Archive h (F.marks h ⟨r,i⟩) := by
  funext n; obtain ht:= column_id P r z F|>.2 n
  unfold byColumn at ht
  simp_rw [ Finset.sum_apply,Pi.smul_apply ] at ht ⊢
  exact specializes _ Finset.univ _ _ (fun i _=> (gang (F.markOK h ⟨r,i⟩ n)).dost) ht
end physical
end YM.MS.ScaleForest
