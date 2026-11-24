import YM.GradedFar.Formal
/-!
# Empty/unit convention

M.2 works for all arities. Use the actual lower arities on any proper-subarray
call (and the `FarCoefficients` etc for that call); equivalently the **correlation kernels**
allow literal unit fields at the retained larger arity. The convention isn't vacuum zero,
nor a discount in powers for an absent mark. For convenience, here are verifications of
the convention for these very kernels (using the graded far-field proof). They don't
assert anything about comparing OPE coefficients for *different* Near input lists.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Scale
open Register Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l k : ℕ}
    (e : Fin m ↪ Fin n)

section tally
abbrev extendDay : Days m ↪ Days n := ⟨Finsupp.embDomain e.optionMap, Finsupp.embDomain_injective ..⟩
lemma sum_extendDay (d : Days m) : ∑ i, extendDay e d i = ∑ i, d i := by
  rw [← Finset.sum_subset (f:=fun i => extendDay e d i) (s₁:=Finset.univ.map e.optionMap)
    (Finset.subset_univ _) ?_, Finset.sum_map ]; exact Finset.sum_congr rfl fun i _ =>
      Finsupp.embDomain_apply_self e.optionMap d i
  intro i hi hx; exact Finsupp.embDomain_notin_range _ _ i (by simpa using hx)

-- rotation/field action through `m` slots after deleting unit slots
lemma sum_tally (d : Fin n → ℕ) (B : ∀ i : Fin n, Guard G (d i))
    (hp : ∀ i j, coeff j (B i) (leaf G (d i)) = if j=0 then leaf G (d i) else 0)
    (v : AppointedH140Inputs G d) (hu : ∀ i, i ∉ Set.range e → v i = leaf G (d i))
    (f : ℕ → MultilinearMap ℂ (fun i => Sec G (d i)) ℂ)
    (g : ℕ → MultilinearMap ℂ (fun i => Sec G (d (e i))) ℂ)
    (H : ∀ i (v : AppointedH140Inputs G d), (∀ i, i ∉ Set.range e → v i = leaf G (d i)) → f i v = g i (fun i => v (e i))) :
    ∑ a ∈ Normalize.tally k n, f (a none) (fun i => coeff (a (some i)) (B i) (v i)) =
      ∑ a ∈ Normalize.tally k m, g (a none) (fun i => coeff (a (some i)) (B (e i)) (v (e i))) := by
  classical
  have hm (d : Days m) : extendDay e d ∈ Normalize.tally k n ↔ d ∈ Normalize.tally k m := by
    rw [totaled,totaled,sum_extendDay]
  have hr (i) : some i ∈ Set.range e.optionMap ↔ i ∈ Set.range e := by
    constructor
    · rintro ⟨_|u,h⟩; cases h; exact ⟨u,Option.some.inj h⟩
    rintro ⟨u,rfl⟩; exact ⟨some u,rfl⟩
  let S := (Normalize.tally k m).map (extendDay e)
  have hS : S ⊆ Normalize.tally k n := by
    intro i hi; obtain ⟨j,h,rfl⟩ := Finset.mem_map.mp hi; exact (hm _).mpr h
  rw [← Finset.sum_subset hS ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [H]
    · congr 1
      · exact congrArg g (Finsupp.embDomain_apply_self e.optionMap j none)
      funext i; rw [show extendDay e j (some (e i)) = _ from Finsupp.embDomain_apply_self e.optionMap j (some i)]
    intro i hi; rw [hu i hi, show extendDay e j (some i) = 0 from Finsupp.embDomain_notin_range _ _ _
      (mt (hr i).mp hi), hp i, if_pos rfl]
  intro i hi hx
  have hh : ∃ j : Fin n, i (some j) ≠ 0 ∧ j ∉ Set.range e := by
    by_contra! h
    apply hx
    have ht : ↑i.support ⊆ Set.range e.optionMap := by
      rintro (_|b) hb; exact ⟨none,rfl⟩; exact (hr _).mpr (h _ (Finsupp.mem_support_iff.mp hb))
    obtain ⟨j,rfl⟩ := (Finsupp.mem_range_embDomain_iff ..).2 ht
    exact Finset.mem_map_of_mem _ ((hm _).1 hi)
  obtain ⟨j,hj,hj'⟩ := hh; exact (f _).map_coord_zero j (by rw [hu _ hj', hp, if_neg hj])

-- same as `Integration/WilsonPositionSeparatedProfileEmptyProgram.calendar`
lemma tally_empty (k : ℕ) : Normalize.tally k 0 = {Finsupp.single none k} := by
  have hU : (Finset.univ : Finset (Option (Fin 0)))={none} := by
    ext e; simp only [Finset.mem_univ,Finset.mem_singleton,true_iff]; cases e with
    | none => rfl
    | some i => exact i.elim0
  ext a; rw [totaled, hU, Finset.sum_singleton, Finset.mem_singleton]; constructor
  · intro h; apply Finsupp.ext; intro e; cases e with
    | none => simpa using h
    | some i => exact i.elim0
  rintro rfl; simp

-- generalized arity-only identity for coefficient systems, same cap
lemma status_units (B : Guard G l)
    (hp : ∀ j, coeff j B (leaf G l) = if j=0 then leaf G l else 0) (v : Tags G l n)
    (hu : ∀ i, i ∉ Set.range e → v i = leaf G l)
    (f : ℕ → Structure1.Point G l n) (g : ℕ → Structure1.Point G l m)
    (H : ∀ i (v : Tags G l n), (∀ i, i ∉ Set.range e → v i = leaf G l) → f i v = g i (v ∘ e)) :
    status B f k v = status B g k (v ∘ e) := by
  rw [seen, seen]
  exact sum_tally e (fun _=>l) (fun _=>B) (fun _=>hp) v hu f g H
lemma status_empty (B : Guard G l) (f : ℕ → Structure1.Point G l 0) (v : Tags G l 0) :
    status B f k v = f k v := by
  rw [seen, tally_empty, Finset.sum_singleton, Finsupp.single_eq_same]; congr!
end tally

def keptPoints (x : Points n) : Points m := points (fun i => x (e i))
def keptSample (s : Sample n) : Sample m := ⟨s.F, s.layout ∘ e, s.center⟩
lemma kept_familiar (s : Sample n) : familiar (keptSample e s) = keptPoints e (familiar s) := rfl
lemma kept_continuous : Continuous (keptPoints e) := by unfold keptPoints points; fun_prop
lemma kept_conf {x : Points n} (hp : x ∈ conf n) : keptPoints e x ∈ conf m := hp.comp e.injective
lemma kept_gate (x : Points n) : Tendsto (keptSample e) (Gate x) (Gate (keptPoints e x)) := by
  unfold Gate; rw [tendsto_inf, tendsto_inf]; refine ⟨⟨tendsto_comap_iff.mpr ?_, tendsto_comap_iff.mpr ?_⟩, tendsto_principal.mpr ?_⟩
  · exact liftG x
  · exact ((kept_continuous e).tendsto x).comp (senseG x)
  exact welcomeG x

section kernel
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
variable (N : WilsonPrescription G) {hG : G.Simple}
    {Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {σ : Prescription (Press.portDeck G)}
    (H : Main.Match N hG Z σ true)
local notation "W" => N.scheme
local notation "S₀" => N.store
local notation "Y" => N.criterion
local notation "V" => Measure.start W Y
local notation "A" => Measure.outlook W Y

lemma live_units (k d : ℕ) (v : Tags G d n) (h : ∀ i, i ∉ Set.range e → v i = leaf G d)
    (s : Sample n) : live W d s k v = live W d (keptSample e s) k (v ∘ e) := by
  simp_rw [Rose.lit_up]; apply congrArg; unfold Rose.numberA
  apply congrArg (Bare.normalized ((W).tree s.F.p) G)
  rw [← Finset.prod_subset (f:=fun i=>Rose.regal W d s _ (v i))
    (Finset.subset_univ (Finset.univ.map e)) ?_, Finset.prod_map]; rfl
  intro i _ hi; rw [h i (by simpa using hi), Rose.oak]
lemma cooked_status (s : Sample n) (n' : ℕ) : Rose.cooked W S₀ l s n' =
    status (deck ((S₀).layout W s.F l)) (live W l s) n' := rfl
lemma rose_units (k d : ℕ) (v : Tags G d n) (h : ∀ i, i ∉ Set.range e → v i = leaf G d)
    (s : Sample n) : Rose.measureₓ W Y d s k v = Rose.measureₓ W Y d (keptSample e s) k (v ∘ e) := by
  rw [Rose.measure_paid,Rose.measure_paid]; apply congrArg (fun f:ℕ→ℂ => Rose.turn W Y s.F f k)
  funext j; rw [cooked_status,cooked_status]
  exact status_units e _ (Rose.prime_deck _) v h (live W d s) (live W d (keptSample e s))
    (fun i v hu => live_units e N i d v hu s)

include H
lemma start_units (k d : ℕ) (v : Tags G d n) (h : ∀ i, i ∉ Set.range e → v i = leaf G d) (x : Stage n) :
    V d n x k v = V d m ⟨keptPoints e x.val, kept_conf e x.property⟩ k (v ∘ e) := by
  refine tendsto_nhds_unique (H.startsInX d n x k v) (((H.startsInX d m _ k _).comp
    (kept_gate e x.val)).congr ?_)
  intro s; exact (rose_units e N k d v h s).symm
lemma outlook_units (k d : ℕ) (v : Tags G d n) (h : ∀ i, i ∉ Set.range e → v i = leaf G d) (x : Stage n) :
    A d n x k v = A d m ⟨keptPoints e x.val, kept_conf e x.property⟩ k (v ∘ e) := by
  refine status_units e (Scale.Measure.adjust W Y d) (fun j => ?_) _ h _ _ (fun i v hv => start_units e N H i d v hv x)
  have hp := (H.details.toServed.toPosted.toQuoted.toContract.joint 0 d).2.2.scale
  split_ifs with hh
  · subst j; rw [hp.zero]; rfl
  exact (hp.high j hh).1
-- literal empty kernel
lemma outlook_empty (x : Stage 0) (v : Tags G l 0) : Reg.Point.story (A l 0 x) v = 1 := by
  let f (s : Sample 0) := Rose.measureₓ W Y l s
  have he (s : Sample 0) : Reg.Point.story (Rose.cooked W S₀ l s) v = 1 := by
    ext n; rw [Reg.Point.story, coeff_mk, cooked_status, status_empty, Rose.lit_up]
    simp [Rose.numberA, Bare.normalize_unit]
  have hf (s : Sample 0) : Reg.Point.story (f s) v = 1 := by
    unfold f; rw [Reg.Faith.Rosa, he]
    rw [← PowerSeries.coe_substAlgHom (Rose.χday W Y s.F)]; exact map_one _
  ext k; rw [Reg.Point.story, coeff_mk, Measure.outlook, Facets.actMark, status_empty]
  refine tendsto_nhds_unique (H.startsInX ..) (f:=fun s : Sample 0 => f s k v)
    (tendsto_const_nhds.congr fun y => ?_)
  have hp := congrArg (coeff k) (hf y); simp only [Reg.Point.story, coeff_mk] at hp; exact hp.symm
end kernel

section mixed_delete
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
variable (N : WilsonPrescription G) {hG : G.Simple}
    (Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} (H : Main.Match N hG Z σ true)
    (ν : ℝ)
local notation "A" => Measure.outlook N.scheme N.criterion
local notation "F" => GroupS.gaugeN N.scheme N.criterion Z ν
variable {n' m' : ℕ} {d : Fin n → ℕ} {f : Fin m → ℕ}
    (hd : AppointedH140Through l d) (he : AppointedH140Through l f) (φ : Fin n' ↪ Fin n) (ψ : Fin m' ↪ Fin m)

/-- Embedding of the jointly occupied slots. -/
def jointSlots (φ : Fin n' ↪ Fin n) (ψ : Fin m' ↪ Fin m) : Fin (n'+m') ↪ Fin (n+m) :=
  (finSumFinEquiv.symm.toEmbedding.trans (φ.sumMap ψ)).trans finSumFinEquiv.toEmbedding
@[simp] lemma jointSlots_left (i : Fin n') : jointSlots φ ψ (Fin.castAdd m' i) = Fin.castAdd m (φ i) := by
  simp [jointSlots]
@[simp] lemma jointSlots_right (i : Fin m') : jointSlots φ ψ (Fin.natAdd n' i) = Fin.natAdd n (ψ i) := by
  simp [jointSlots]
lemma forest_kept (x : Points n) (y : Points m) (η : ℝ) :
    forest (keptPoints φ x) (squeeze η (keptPoints ψ y)) = keptPoints (jointSlots φ ψ) (forest x (squeeze η y)) := by
  ext1 i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [keptPoints, O.Score.squeeze]

lemma joint_raised (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G f) :
    Fin.append (raised (fun i : Fin n' => hd (φ i)) (fun i : Fin n' => u (φ i)))
        (raised (fun i : Fin m' => he (ψ i)) (fun i : Fin m' => v (ψ i))) =
      Fin.append (raised hd u) (raised he v) ∘ jointSlots φ ψ := by
  funext i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [raised]

include H
lemma raw_unit_drop (η : ℝ) (x : Points n) (y : Points m) (hp : forest x (squeeze η y) ∈ conf (n+m))
    (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G f)
    (hu : ∀ i, i ∉ Set.range φ → u i = leaf G (d i)) (hv : ∀ i, i ∉ Set.range ψ → v i = leaf G (f i)) :
    rawCoeff A hd he (forest x (squeeze η y)) k u v = rawCoeff A (d:=fun i => d (φ i)) (e:=fun i => f (ψ i))
      (fun i => hd (φ i)) (fun i => he (ψ i)) (forest (keptPoints φ x) (squeeze η (keptPoints ψ y))) k
      (fun i => u (φ i)) (fun i => v (ψ i)) := by
  rw [forest_kept, rawCoeff_apply _ _ _ _ _ _ _ hp,
    rawCoeff_apply _ _ _ _ _ _ _ (kept_conf _ hp), joint_raised]
  apply outlook_units _ N H k l _ _ ⟨_,hp⟩
  intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · intro hi; rw [Fin.append_left, raised]; have hj : j ∉ Set.range φ := by
      rintro ⟨b,rfl⟩; exact hi ⟨Fin.castAdd m' b,jointSlots_left ..⟩
    rw [hu j hj]; rfl
  · intro hi; rw [Fin.append_right, raised]; have hj : j ∉ Set.range ψ := by
      rintro ⟨b,rfl⟩; exact hi ⟨Fin.natAdd n' b,jointSlots_right ..⟩
    rw [hv j hj]; rfl

theorem full_unit_drop (η : ℝ) (x : Points n) (y : Points m) (hp : forest x (squeeze η y) ∈ conf (n+m))
    (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G f)
    (hu : ∀ i, i ∉ Set.range φ → u i = leaf G (d i)) (hv : ∀ i, i ∉ Set.range ψ → v i = leaf G (f i)) :
    fullSeries A F η hd he x y u v =
    fullSeries A F η (d:=fun i => d (φ i)) (e:=fun i => f (ψ i)) (fun i => hd (φ i)) (fun i => he (ψ i))
      (keptPoints φ x) (keptPoints ψ y) (fun i => u (φ i)) (fun i => v (ψ i)) := by
  ext k; simp_rw [fullSeries, coeff_mk, withFar_apply]
  exact sum_tally ψ f (fun i => conversion F η (f i)) (fun _ _ => conversion_leaf (H.dilation ν).check ..) v hv
    (fun i => rawCoeff A hd he _ i u)
    (fun i => rawCoeff A (d:=fun i => d (φ i)) (fun i => hd (φ i))
      (e:=fun i => f (ψ i)) (fun i => he (ψ i)) _ i (fun i => u (φ i)))
    (fun i v hV => raw_unit_drop N Z H hd he φ ψ η x y hp u v hu hV)

-- empty price in applications can also just use this direct value. No positive `m` premise anywhere.
lemma full_empty (d e : Fin 0 → ℕ) (hd : AppointedH140Through l d) (he : AppointedH140Through l e) (u : AppointedH140Inputs G d) (v : AppointedH140Inputs G e)
    (η : ℝ) (x y : Points 0) : fullSeries A F η hd he x y u v = 1 := by
  let p : Points 0 := forest x (squeeze η y); have hp : p ∈ conf 0 := fun i => i.elim0
  ext k
  rw [fullSeries, coeff_mk, withFar_apply, tally_empty, Finset.sum_singleton, Finsupp.single_eq_same]
  change rawCoeff _ hd he p k u _ = _
  rw [rawCoeff_apply A hd he p u _ k hp]
  have h (v : Tags G l 0) := congrArg (coeff k) (outlook_empty N H ⟨p,hp⟩ v)
  simp only [Reg.Point.story, coeff_mk] at h; exact h _
end mixed_delete
end YM.FVA2.GradedFar
