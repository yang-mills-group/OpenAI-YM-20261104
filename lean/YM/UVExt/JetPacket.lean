import YM.UVExt.SolverFlux

/-! Fixed-level sublimit evaluations on the actual unmasked main and loop families. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Paths
open RG Function Filter Wilson Precision Lattice Laurent Bid Exterior Matrix Tensor Set
open Next.Free.UV
open scoped Topology ContDiff BigOperators Classical

variable {ι : Type*}
lemma restrain (u : ℕ→ι→ℝ) {C : ι→ℝ} (h : ∀ i, ∀ᶠ x : ℕ in atTop, ‖u x i‖ ≤ C i) : ∀ i, ∃ D, ∀ x, ‖u x i‖ ≤ D := by
  intro i; obtain ⟨a,H⟩ := eventually_atTop.1 (h i)
  refine ⟨max (C i) (∑ j∈Finset.range a,‖u j i‖),fun x=>?_⟩
  exact if he:a≤x then (H x he).trans (le_max_left ..) else le_trans (Finset.single_le_sum (fun j (_hi : j∈Finset.range a)=>norm_nonneg (u j i)) (Finset.mem_range.mpr (lt_of_not_ge he))) (le_max_right ..)
lemma sequence_extract {u : ℕ→ι→ℝ} (h : ∀ i, ∃ D, ∀ x, ‖u x i‖ ≤ D) [Countable ι] : ∃ g : ι→ℝ, ∃ k : ℕ→ℕ, StrictMono k ∧ Tendsto (u ∘ k) atTop (𝓝 g) := by
  classical
  choose D hD using h
  let v (x : ℕ) (i : ι) := (⟨u x i,show u x i∈Set.Icc (-D i) (D i) from abs_le.mp (hD i x)⟩ : Set.Icc (-D i) (D i)) -- replace
  haveI := fun i => (show CompactSpace (Set.Icc (-D i) (D i)) by infer_instance)
  obtain ⟨g,_,k,hk,ht⟩ := (isCompact_univ_iff.mpr (inferInstance : CompactSpace (∀ i, Set.Icc (-D i) (D i)))).tendsto_subseq (x:=v) (by simp)
  exact ⟨fun i=> (g i).val,k,hk,tendsto_pi_nhds.mpr fun i=> (continuous_subtype_val.tendsto _).comp (tendsto_pi_nhds.mp ht i)⟩

variable {G : Gauge} {Z : Shadow G} {M : ℕ→PathData G} {σ C Λ : ℝ} {p : Clip}
structure Passing (M : ℕ→PathData G) (Z : Shadow G) (σ C Λ : ℝ) (p : Clip) : Prop where
   mask : ∀ᶠ i in atTop, (M i).Bounds p σ C Λ
   width : 0 < σ
   limit : PaidShadow Z C Λ σ
   row b : Tendsto (fun i=> (wick (M i)).row b) atTop (𝓝 (Z.row b))
   three : Tendsto (fun i=> (wick (M i)).cubic) atTop (𝓝 Z.cubic)
   four : Tendsto (fun i=> (wick (M i)).quartic) atTop (𝓝 Z.quartic)
   loop : Tendsto (fun i=> (wick (M i)).loop) atTop (𝓝 Z.loop)

lemma Passing.subseq (h : Passing M Z σ C Λ p) {k : ℕ→ℕ} (ht : Tendsto k atTop atTop) : Passing (M ∘ k) Z σ C Λ p :=
    ⟨ht.eventually h.mask, h.width, h.limit, fun b => (h.row b).comp ht, h.three.comp ht, h.four.comp ht, h.loop.comp ht⟩

section all
variable {W : ℕ→ℕ→PathData G} {C₁ Λ' σ' : ℕ→ℝ} {p' : ℕ→Clip}
lemma late_limit {L : ι→ℝ} {Z : ℕ→ι→ℝ} {u} (h : ∀ᶠ i : ℕ in atTop, Carries C σ L (Z i)) (hu : Tendsto Z atTop (𝓝 u)) : Carries C σ L u := by
  obtain ⟨a,ha⟩ := eventually_atTop.1 h; exact Carries.limit (X:=fun i:ℕ=>Z (a+i)) (fun i=> ha _ (Nat.le_add_right ..)) (fun i=> (tendsto_pi_nhds.mp hu i).comp (tendsto_atTop_mono (f:=id) (fun i:ℕ=> Nat.le_add_left i a) (tendsto_id (x:=atTop)))) -- order lemmas inspect
lemma innkeeper {Ω : Type*} [Countable Ω] {f : ℕ→ℕ→Ω→ℝ} {L : Ω→ℝ} (h : ∀ m,∀ᶠ i : ℕ in atTop, Carries (C₁ m) (σ' m) L (f i m)) (ht : ∀ m, 0<σ' m) : ∃ (g : ℕ→Ω→ℝ),∃ k : ℕ→ℕ, StrictMono k ∧ Tendsto (fun j=> Function.uncurry (f (k j))) atTop (𝓝 (Function.uncurry g)) := by
  obtain ⟨g,k,hk,H⟩ := sequence_extract (u:=fun j=> Function.uncurry (f j)) (restrain _ fun i => (h i.1).mono fun j hj => hj.total (ht _) _)
  exact ⟨fun n p=> g (n,p),k,hk,tendsto_pi_nhds.mpr fun i=>(tendsto_pi_nhds.mp H i)⟩
private lemma multipoint {W : ℕ→ℕ→ι→ℝ} {A : ℕ→ι→ℝ} {f g : ℕ→ℕ} (h : Tendsto (fun i=>Function.uncurry (W (f i))) atTop (𝓝 (Function.uncurry A))) (he : Tendsto g atTop atTop) (i : ℕ) : Tendsto (fun j=> W (f (g j)) i) atTop (𝓝 (A i)) :=
    tendsto_pi_nhds.mpr fun t=> (tendsto_pi_nhds.mp h (i,t)).comp he

/- no map selected here; simultaneous coefficient sublimits test both hypothetical limiting values. -/
set_option maxHeartbeats 300000 in
lemma fleet (h : ∀ m, ∀ᶠ i in atTop,(W i m).Bounds (p' m) (σ' m) (C₁ m) (Λ' m)) : ∃ F : ℕ→Shadow G, (∀ m, PaidShadow (F m) (C₁ m) (Λ' m) (σ' m)) ∧ ∃ k : ℕ→ℕ, StrictMono k ∧ ∀ m,Passing (fun i=>W (k i) m) (F m) (σ' m) (C₁ m) (Λ' m) (p' m) := by
  classical
  let V i m := wick (W i m)
  have hW (m) : ∀ᶠ i in atTop, PaidShadow (V i m) (C₁ m) (Λ' m) (σ' m) := (h m).mono fun i hh=> shadow_pay (W i m) hh
  have hw m := (h m).exists.choose_spec.width
  obtain ⟨A₀,k₀,h₀,H₀⟩ := sequence_extract (u:=fun i (p : ℕ × PlaqAxes × Slot) => (V i p.1).row p.2.1 p.2.2) (restrain _ fun p=> (hW _).mono fun m hm=> (hm.row ..).total (hw _) _)
  obtain ⟨A,k₁,h₁,H₁⟩ := innkeeper (f:=fun i m=> (V (k₀ i) m).cubic) (fun m=>h₀.tendsto_atTop.eventually ((hW m).mono (fun i hi=>hi.coeffThree))) hw
  obtain ⟨B,k₂,h₂,H₂⟩ := innkeeper (f:=fun i m=> (V (k₀ (k₁ i)) m).quartic) (fun m=>(h₀.comp h₁).tendsto_atTop.eventually ((hW m).mono (fun i hi=>hi.coeffFour))) hw
  obtain ⟨D,k₃,h₃,H₃⟩ := innkeeper (f:=fun i m=> (V (k₀ (k₁ (k₂ i))) m).loop) (fun m=>(h₀.comp (h₁.comp h₂)).tendsto_atTop.eventually ((hW m).mono (fun i hi=>hi.coeffTwo))) hw
  let Z m : Shadow G := ⟨fun i a=> A₀ (m,i,a),A m,B m,D m⟩
  let k i := k₀ (k₁ (k₂ (k₃ i)))
  have hY : StrictMono k := h₀.comp <| h₁.comp <| h₂.comp h₃
  have he (m) : ∀ᶠ i in atTop,PaidShadow (V (k i) m) (C₁ m) (Λ' m) (σ' m) := hY.tendsto_atTop.eventually (hW m)
  have hL m : Passing (fun i=>W (k i) m) (Z m) (σ' m) (C₁ m) (Λ' m) (p' m) := by
    refine ⟨hY.tendsto_atTop.eventually (h m), ((h m).exists.choose_spec).width, ?_,?_,?_,?_,?_⟩
    · refine ⟨fun b => late_limit (he m |>.mono fun i hi=>hi.row b) (tendsto_pi_nhds.mpr fun a=> (tendsto_pi_nhds.mp H₀ (m,b,a)).comp (h₁.comp (h₂.comp h₃)).tendsto_atTop),
        late_limit (he m |>.mono fun i hi=>hi.coeffThree) (multipoint (W:=fun i m=>(V i m).cubic) (f:=fun i=>k₀ (k₁ i)) (A:=A) (g:=k₂ ∘ k₃) H₁ (h₂.comp h₃).tendsto_atTop _),late_limit (he m |>.mono fun i hi=>hi.coeffFour) (multipoint (W:=fun i m=>(V i m).quartic) (f:=fun i=> k₀ (k₁ (k₂ i))) (A:=B) (g:=k₃) H₂ h₃.tendsto_atTop _),late_limit (he m |>.mono fun i hi=>hi.coeffTwo) (
        (tendsto_pi_nhds.mpr fun u=> tendsto_pi_nhds.mp H₃ (m,u)) : Tendsto (fun j => (V (k j) m).loop) atTop (𝓝 _))⟩
    · intro b; exact tendsto_pi_nhds.mpr fun a=> (tendsto_pi_nhds.mp H₀ (m,b,a)).comp (h₁.comp (h₂.comp h₃)).tendsto_atTop
    · exact multipoint (W:=fun i m=>(V i m).cubic) (f:=fun i=>k₀ (k₁ i)) (A:=A) (g:=k₂ ∘ k₃) H₁ (h₂.comp h₃).tendsto_atTop _
    · exact multipoint (W:=fun i m=>(V i m).quartic) (f:=fun i=> k₀ (k₁ (k₂ i))) (A:=B) (g:=k₃) H₂ h₃.tendsto_atTop _
    exact tendsto_pi_nhds.mpr fun a=> tendsto_pi_nhds.mp H₃ (m,a)
  exact ⟨Z,fun m=> (hL m).limit,k,hY,hL⟩
end all

end YM.UVExt.Paths
