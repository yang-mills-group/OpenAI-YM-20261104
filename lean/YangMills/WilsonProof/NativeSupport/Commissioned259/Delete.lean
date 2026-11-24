import YangMills.WilsonProof.NativeSupport.Commissioned259.Matched

/-!
# Empty and subarray conventions

Preserve ordinary product rows including empty = 1. Prove explicit *subarray* identities
using the genuine operators. As in bbcb's argument after F.O, pass the unit assertion first
from the independently solved regulator through its OWN Gate limit and only then do the
rest of the proof with the adjusted formal book, respecting unit and lower levels.
Selection here by arbitrary slot injections (includes permutations and empty).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries MeasureTheory Maxwell
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus XSpace.Rose
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {n m k h : ℕ}

section Tally
variable (f : Fin m ↪ Fin n)

abbrev restrictPt (x : Points n) : Points m := points fun i => x (f i)
lemma restrict_cont : Continuous (restrictPt f) := by
  unfold restrictPt points
  apply (PiLp.continuous_toLp _ _).comp
    (show Continuous (fun p : Points n => fun i : Fin m => p (f i)) from continuous_pi fun i=> by fun_prop)
lemma restrict_conf {x : Points n} (hx : x ∈ conf n) : restrictPt f x ∈ conf m := hx.comp f.injective
lemma day_in (a : Days m) : a.embDomain f.optionMap ∈ Normalize.tally k n ↔ a ∈ Normalize.tally k m := by
  rw [totaled,totaled] 
  rw [← Fintype.sum_of_injective (⇑f.optionMap) f.optionMap.injective (⇑a) (⇑(a.embDomain f.optionMap))
    (fun i => Finsupp.embDomain_notin_range _ _ i) (fun i=> (Finsupp.embDomain_apply_self _ _ _).symm)]
private lemma offRange (i:Fin n) (h:i∉range f) : some i∉range f.optionMap := by
  rintro ⟨_|j,e⟩; contradiction
  exact h ⟨j,Option.some.inj e⟩

variable {d : Fin n → ℕ} (F : (i : Fin n) → Guard G (d i))
abbrev pulse (a : Days n) (v : Slots G d) : Slots G d :=
  fun i => coeff (a (some i)) (F i) (v i)
def padLeaf (u : Slots G d) := ∀ i ∉ range f, u i = leaf G (d i)

variable (X : ℕ → MLA G d) (Y : ℕ → MLA G (d ∘ f))

/-- General tally bridge (also mixed caps). Mark ONLY these n inputs by F; deleting true
unit slots gives exactly the smaller marked series, on precisely the corresponding points. -/
lemma tally_shrink (u : Slots G d) (h : padLeaf f u) (k : ℕ)
    (H : ∀ u : Slots G d, padLeaf f u → ∀ j, X j u = Y j (fun i => u (f i)))
    (hv : ∀ i k, coeff k (F i) (leaf G (d i)) = if k=0 then leaf G (d i) else 0) :
    ∑ a∈Normalize.tally k n, X (a none) (pulse F a u) =
      ∑ a∈Normalize.tally k m, Y (a none) (pulse (d:=d ∘ f) (fun i=> F (f i)) a (fun i=> u (f i))) := by
  symm
  let A (a:Days m) := a.embDomain f.optionMap
  refine Finset.sum_of_injOn A (Finsupp.embDomain_injective _ |>.injOn)
    (fun i hi => (day_in f i).mpr hi) ?_ ?_
  · intro i hi hn
    by_contra ne
    have hey : i ∈ range A := by
      refine (Finsupp.mem_range_embDomain_iff _ _).mpr ?_
      rintro (_|j) hj
      · exact ⟨none,rfl⟩
      by_contra! he
      apply ne (MultilinearMap.map_coord_zero _ j ?_)
      have hj0 : j ∉ range f := by
        rintro ⟨r, e⟩; subst j; exact he ⟨some r,rfl⟩
      rw [pulse,h j hj0,hv,if_neg (Finsupp.mem_support_iff.mp hj)]
    obtain ⟨x,rfl⟩ := hey
    exact hn ⟨x,(day_in f x).mp hi,rfl⟩
  intro a _; have hn : A a none = a none := Finsupp.embDomain_apply_self f.optionMap a none
  rw [H (pulse F (A a) u) ?_,hn]
  · apply congr_arg (Y (a none)); funext i
    unfold pulse; rw [show A a (some (f i)) = a (some i) from Finsupp.embDomain_apply_self f.optionMap a (some i)]; rfl
  intro i hi; unfold pulse; rw [h i hi, hv, if_pos (Finsupp.embDomain_notin_range f.optionMap a _ (offRange f i hi))]
end Tally

lemma vacant_tally (k : ℕ) : Normalize.tally k 0 = {Finsupp.single none k} := by
  ext x
  rw [totaled,Fintype.sum_option]
  simp only [Finset.univ_eq_empty,Finset.sum_empty,add_zero,Finset.mem_singleton]
  refine ⟨fun h=> ?_,fun h=> h ▸ Finsupp.single_eq_same⟩
  apply Finsupp.ext; intro u; cases u
  exact h.trans Finsupp.single_eq_same.symm
  exact Fin.elim0 ‹Fin 0›

section Solve
variable (N : WilsonPrescription G)
    (f : Fin m ↪ Fin n)
local notation "R" => N.scheme
local notation "U" => N.criterion
private abbrev subSample (x : Sample n) : Sample m := ⟨x.F,x.layout ∘ f,x.center⟩

private lemma follows (X : Points n) : Tendsto (subSample f) (Gate X) (Gate (restrictPt f X)) := by
  unfold Gate; rw [tendsto_inf,tendsto_inf]
  refine ⟨⟨tendsto_comap_iff.mpr (liftG X),tendsto_comap_iff.mpr ?_⟩,tendsto_principal.mpr (welcomeG X)⟩
  exact ((restrict_cont f).tendsto X).comp (senseG X)

private lemma physical_unit (d k : ℕ) (x : Sample n) (u : Tags G d n) (h : padLeaf (d := fun _=>d) f u) :
    Rose.measureₓ R U d x k u = Rose.measureₓ R U d (subSample f x) k (u ∘ f) := by
  have hb (k : ℕ) (v : Tags G d n) (hp : padLeaf (d := fun _=>d) f v) :
      numberA R d x v Finset.univ = numberA R d (subSample f x) (v ∘ f) Finset.univ := by
    unfold numberA; refine congr_arg (Bare.normalized ..) (Eq.symm ?_)
    exact Fintype.prod_of_injective (⇑f) f.injective _ _ (fun i hi=> by rw [hp i hi, oak]) fun i=>rfl
  have hl (v : Tags G d n) (hp : padLeaf (d:=fun _=>d) f v) (k:ℕ) : live R d x k v = live R d (subSample f x) k (v ∘ f) := by
    rw [lit_up, lit_up, hb k v hp]
  rw [measure_paid,measure_paid]; congr 1; funext k'; rw [cooks,cooks]
  exact tally_shrink (d:=fun _ => d) f (fun _=> deck (N.store.layout R x.F d)) (live R d x) (live R d (subSample f x)) u h k' hl (fun i k=> prime_deck ..)

private lemma raw_empty (d k : ℕ) (x : Sample 0) (u : Tags G d 0) :
    Rose.measureₓ R U d x k u = coeff k (1:PowerSeries ℂ) := by
  have hv : PowerSeries.mk (fun i=> cooked R N.store d x i u) = 1 := PowerSeries.ext fun i => by
    rw [coeff_mk, cooks, vacant_tally, Finset.sum_singleton, lit_up, numberA]; simp [Bare.normalize_unit]
  rw [measure_paid, turn_coins, hv, ←coe_substAlgHom (χday R U x.F), map_one]

variable {sim : G.Simple} (ν : ℝ) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "W" => Scale.Measure.start R U
local notation "V" => Scale.Measure.outlook R U
include H

private lemma starts (x : Stage n) (k d : ℕ) (u : Tags G d n) (hp : padLeaf (d:=fun _=>d) f u) :
    W d n x k u = W d m ⟨restrictPt f x.val,restrict_conf f x.property⟩ k (u ∘ f) := by
  apply tendsto_nhds_unique (H.startsInX d n x k u)
  exact ((H.startsInX d m ⟨restrictPt f x.val,restrict_conf f x.property⟩ k (u ∘ f)).comp (follows f x.val)).congr fun i=> (physical_unit N f d k i u hp).symm

include ν
lemma outlook_delete (x : Stage n) (k d : ℕ) (u : Tags G d n) (hp : padLeaf (d:=fun _=>d) f u) :
    V d n x k u = V d m ⟨restrictPt f x.val,restrict_conf f x.property⟩ k (u ∘ f) := by
  have h : Scale.Base (Scale.Measure.adjust R U d) := (H.details.toServed.toPosted.toQuoted.toContract.joint ν d).2.2.scale
  have hM (i:Fin n) k : coeff k (Scale.Measure.adjust R U d) (leaf G d) = if k=0 then leaf G d else 0 := by
    split; subst k; rw [h.zero,Module.End.one_apply]; exact (h.high _ ‹_›).1
  unfold Scale.Measure.outlook Facets.actMark; rw [Dframe.seen, Dframe.seen];
  exact tally_shrink (d:=fun _=>d) f (fun _=> Scale.Measure.adjust R U d)
    (W d n x) _ u hp k (fun u h k=> starts N f M H x k d u h) hM

omit ν in
lemma outlook_zero (x : Stage 0) (k d : ℕ) (u : Tags G d 0) : V d 0 x k u = coeff k (1:PowerSeries ℂ) := by
  have E (w : Tags G d 0) : W d 0 x k w = coeff k (1:PowerSeries ℂ) := by
    refine tendsto_nhds_unique (H.startsInX d 0 x k w) ?_
    exact tendsto_const_nhds.congr fun i => (raw_empty N d k i w).symm
  unfold Scale.Measure.outlook Facets.actMark
  rw [Dframe.seen,vacant_tally k,Finset.sum_singleton,Finsupp.single_eq_same,E]
end Solve
end YM.FVA2.GradedFar259
