import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.Rows
import YM.FVA2.Main

/-!
# Proper-subarray and empty rows

Here are proofs on the book, not axioms for treating punctured arrays as
unit insertions. FormalDemand: pass to the Gate limit.
Do not use any contact estimate (the configuration in the LARGER arity has to
be admitted too).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set XSpace XSpace.Normalize XSpace.Structure1 PowerSeries
open XSpace.Cirrus XSpace.Rose
open Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m a b d k : ℕ}
section erase
variable (e : Fin a ↪ Fin n)
def positions (x : Points n) : Points a := points (fun i => x (e i))
lemma positions_val (x : Points n) (i : Fin a) : positions e x i = x (e i) := rfl
lemma positions_cont : Continuous (fun x : Points n => positions e x) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  apply continuous_pi; intro i; fun_prop
lemma positions_conf {x : Points n} (hx : x ∈ conf n) : positions e x ∈ conf a :=
  hx.comp e.injective

def sameMesh (z : Sample n) : Sample a := ⟨z.F, z.layout ∘ e, z.center⟩

lemma gate_positions (x : Points n) : Tendsto (sameMesh e) (Gate x) (Gate (positions e x)) := by
  refine tendsto_inf.mpr ⟨tendsto_inf.mpr ⟨tendsto_comap_iff.mpr (liftG x), ?_⟩,
    tendsto_principal.mpr (welcomeG x)⟩
  exact tendsto_comap_iff.mpr (((positions_cont e).tendsto x).comp (senseG x))

def Padded (e : Fin a ↪ Fin n) (v : Fin n → Sec G d) := ∀ i : Fin n, i∉Set.range e → v i = leaf G d

def allowDay : Option (Fin a) ↪ Option (Fin n) := ⟨Option.map e, by
  rintro (_|i) (_|j) eq <;> simp only [Option.map_none, Option.map_some] at eq
  · rfl
  · cases eq
  · cases eq
  · exact congrArg some (e.injective (Option.some.inj eq))⟩

def pad : Days a ↪ Days n := ⟨Finsupp.embDomain (allowDay e), Finsupp.embDomain_injective _⟩
lemma pad_none (i : Days a) : (pad e i) none = i none := Finsupp.embDomain_apply_self _ _ none
lemma pad_some (i : Days a) (x : Fin a) : (pad e i) (some (e x)) = i (some x) := Finsupp.embDomain_apply_self _ _ (some x)
lemma pad_off (i : Days a) {j : Fin n} (hj : j∉Set.range e) : (pad e i) (some j) = 0 := by
  apply Finsupp.embDomain_notin_range
  rintro ⟨_|x, h⟩
  · cases h
  · exact hj ⟨x, Option.some.inj h⟩
lemma pad_tally (i : Days a) : pad e i ∈ tally k n ↔ i∈ tally k a := by
  simp only [totaled, Fintype.sum_option, pad_none]; congr! 1
  rw [← Finset.sum_subset (s₁:= Finset.univ.map e) (Finset.subset_univ _) ?_, Finset.sum_map]
  · simp_rw [pad_some]
  · intro j _ hj; exact pad_off e i (by simpa using hj)

/-- The only contributing allocations of perturbative orders to a padded row.
Filter the whole tally, keeping exactly the image of e. -/
lemma sum_padded {A : Type*} [AddCommMonoid A] (F : Days n → A) (k : ℕ)
    (zero : ∀ j ∈ tally k n, ∀ i : Fin n, i∉Set.range e → j (some i) ≠ 0 → F j = 0) :
    ∑ i ∈ tally k n, F i = ∑ i ∈ tally k a, F (pad e i) := by
  rw [← Finset.sum_map]; symm; apply Finset.sum_subset
  · intro i hi; obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hi; exact (pad_tally e v).mpr hv
  intro i hi not_in; by_contra h
  have sub : ↑i.support ⊆ Set.range (allowDay e) := by
    rintro (_|j) hj
    · exact ⟨none,rfl⟩
    · obtain u | ⟨u,rfl⟩ := em' (j∈Set.range e)
      · exact False.elim (h (zero i hi j u (Finsupp.mem_support_iff.mp hj)))
      exact ⟨some u,rfl⟩
  let j := Finsupp.comapDomain (allowDay e) i (allowDay e).injective.injOn
  have h' : pad e j = i := Finsupp.embDomain_comapDomain sub
  exact not_in (Finset.mem_map.mpr ⟨j,(pad_tally e j).mp (by rw [h']; exact hi),h'⟩)

lemma status_padded (f : ℕ → Point G d n) (g : ℕ → Point G d a)
    (h : ∀ i v, Padded e v → f i v = g i (v ∘ e))
    (T : Guard G d) (ht : ∀ i, coeff i T (leaf G d) = if i=0 then leaf G d else 0) (v : Fin n → Sec G d)
    (padV : Padded e v) : status T f k v = status T g k (v ∘ e) := by
  rw [seen, seen, sum_padded e _ k]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [pad_none, h]; congr 1; funext j; simp only [pulseU,pad_some,Function.comp_apply]
    intro j hj; simp only [pulseU,padV j hj,pad_off e _ hj,ht,if_true]
  intro i _ j hj hv; exact (f _).map_coord_zero j (by rw [pulseU, padV j hj,ht,if_neg hv])

variable (W : XSpace.Initialize G) {K : Store G} (Y : Rose.Pick K)

lemma live_padded (i : ℕ) (z : Sample n) (v : Tags G d n) (hv : Padded e v) :
    live W d z i v = live W d (sameMesh e z) i (v ∘ e) := by
  rw [lit_up,lit_up]; apply congrArg; unfold numberA; apply congrArg
  rw [← Finset.prod_subset (s₁:= Finset.univ.map e) (Finset.subset_univ _) ?_, Finset.prod_map]
  · rfl
  · intro j _ hj; rw [hv j (by simpa using hj), oak]

lemma cooked_padded (i : ℕ) (z : Sample n) (v : Tags G d n) (hv : Padded e v) :
    cooked W K d z i v = cooked W K d (sameMesh e z) i (v ∘ e) :=
  status_padded e (live W d z) (live W d (sameMesh e z)) (fun j a ha => live_padded e W j z a ha)
    (deck (K.layout W z.F d)) (prime_deck _) v hv
lemma rose_padded (i : ℕ) (z : Sample n) (v : Tags G d n) (hv : Padded e v) :
    measureₓ W Y d z i v = measureₓ W Y d (sameMesh e z) i (v ∘ e) := by
  simp only [measure_paid]; congr 1; funext k; exact cooked_padded e W k z v hv

lemma blank_tally (k : ℕ) : tally k 0 = {Finsupp.single none k} := by
  ext i; simp only [totaled,Fintype.sum_option,Finset.univ_eq_empty,Finset.sum_empty,add_zero,
    Finset.mem_singleton]; constructor
  · intro h; apply Finsupp.ext; rintro (_|j)
    · simpa using h
    exact j.elim0
  rintro rfl; simp
lemma paddingStatusEmpty122 (f : ℕ → Point G d 0) (T : Guard G d) (k : ℕ) (v : Tags G d 0) :
    status T f k v = f k v := by
  rw [seen, blank_tally, Finset.sum_singleton, Finsupp.single_eq_same]
  exact congrArg (f k) (funext (fun i => i.elim0))
lemma rose_empty (i : ℕ) (z : Sample 0) (v : Tags G d 0) :
    measureₓ W Y d z i v = coeff i 1 := by
  rw [measure_paid, turn_coins]; apply congr_arg
  have empty : PowerSeries.mk (fun i => cooked W K d z i v) = 1 := by
    ext j; rw [coeff_mk, show cooked W K d z j v = live W d z j v from paddingStatusEmpty122 _ (deck (K.layout W z.F d)) _ _,
      lit_up, numberA]; simp only [Finset.univ_eq_empty,Finset.prod_empty, Bare.normalize_unit]
  rw [empty, ← coe_substAlgHom (Rose.χday W Y z.F), map_one]

variable (N : Register.WilsonPrescription G)
    {M : MS.Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {Sms : MS.Land.Prescription (Press.portDeck G)}
    {hG : G.Simple} (matched : Main.Match N hG M Sms true)
local notation "V♪" => Scale.Measure.outlook N.scheme N.criterion
local notation "P♪" => Scale.Measure.start N.scheme N.criterion
include matched
lemma start_padded (i : ℕ) (z : Stage n) (v : Tags G d n) (hv : Padded e v) :
    P♪ d n z i v = P♪ d a ⟨positions e z.val, positions_conf e z.property⟩ i (v ∘ e) := by
  have t := ((matched.startsInX d) a ⟨positions e z.val, positions_conf e z.property⟩ i (v ∘ e)).comp
    (gate_positions e z.val)
  exact tendsto_nhds_unique (matched.startsInX d n z i v) (t.congr (fun j => (rose_padded e N.scheme N.criterion i j v hv).symm))
lemma outlook_padded (i : ℕ) (z : Stage n) (v : Tags G d n) (hv : Padded e v) :
    V♪ d n z i v = V♪ d a ⟨positions e z.val, positions_conf e z.property⟩ i (v ∘ e) := by
  let T := Scale.Measure.adjust N.scheme N.criterion d
  have H : Base T := (matched.details.toServed.toPosted.toQuoted.toContract.joint 0 d).2.2.scale
  apply status_padded e (P♪ d n z) (P♪ d a _) (fun i v h => start_padded e N matched i z v h) T _ v hv
  intro i; split <;> rename_i h
  · subst i; rw [H.zero]; rfl
  rw [(H.high i h).1]
lemma start_empty (k : ℕ) (x : Stage 0) (v : Tags G d 0) : P♪ d 0 x k v = coeff k 1 :=
  tendsto_nhds_unique (matched.startsInX d 0 x k v)
    (tendsto_const_nhds.congr (fun z => (rose_empty N.scheme N.criterion k z v).symm))
lemma paddingOutlookEmpty122 (k : ℕ) (x : Stage 0) (v : Tags G d 0) : V♪ d 0 x k v = coeff k 1 :=
  (paddingStatusEmpty122 (P♪ d 0 x) (Scale.Measure.adjust N.scheme N.criterion d) k v).trans (start_empty N matched k x v)
end erase
end YM.FVA2.GradedFar

