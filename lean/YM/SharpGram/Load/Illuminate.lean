import YM.SharpGram.Load.Source
/-!
# K-UV physical stress and rotation generators
Returns leading comparison on tents of the all-k level path. No restriction
to any single zoom hidden in supplier receipts.
Warning lengths not every positive real, radius and its prices in Mantle. No
other scales asserted here. Reuses the documented Wick comparator, stress
orientation & normalization. No claim about the interacting coefficient
of the trace or any particular anomaly beyond this leading-order realization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SharpGram.Load
open Function Filter Set Table Climb Ward Org Extraction Analysis Spec Next.UVStress Pert
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G: Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book} {F:Final C f S}
local notation "σ" => F.room.kernel.spin
local notation "E" => F.sector.energy
local notation "V" => F.sector.derivatives
local notation "S'"=> (Bel C.book)
local notation "α"=> F.sector.turns.lie
local notation "T" => F.phase.transport
local notation "H" => F.room.kernel
variable {M:MaxwellData C} {u : Filter (ℕ×ℕ)}
variable (B:Lenses.Mantle F u)
section zoom
variable (hg:OPE.Services C f S) {j:ℕ→ℕ}(hj:Tendsto j atTop atTop)(ha:StrictAnti (B.radius ∘ j)) {P:ℕ→Prop}

-- needed frequency refinement special case for this question.
lemma hovers (hv:∀ t:ℕ→ℕ,Tendsto t atTop atTop→StrictAnti (B.radius ∘ t)→∃ s: Sequence,∀ᶠ i:ℕ in atTop,P (t (s i))) : ∀ᶠ k in atTop,P k := by
  refine B.onFocus P (fun j hj ha => ?_)
  by_contra h
  obtain ⟨v,hv0,hV⟩:= extraction_of_frequently_atTop (by simpa only [Filter.Frequently,not_not] using h : ∃ᶠ i:ℕ in atTop, ¬ P (j i))
  obtain ⟨s,hs⟩:= hv (j ∘ v) (hj.comp hv0.tendsto_atTop) (ha.comp_strictMono hv0)
  obtain ⟨k,hk⟩:= hs.exists
  exact hV (s k) hk

include hg B
lemma universal (W:ℕ→Prop) (hv:∀ M: MaxwellData C,M.T.W=Maxwell.Free.scheme C.labels→M.T.K=Maxwell.Free.gear C.labels→M.T.J = YM.UVNext.FreeStress.torch C.book.grid 1 → ∀ (j:ℕ→ℕ)(hj:Tendsto j atTop atTop)(ha:StrictAnti (B.radius ∘ j))(s:Sequence)(t:ℕ→ℝ)(ht:∀ i,0<t i) (c:ℝ), c≠0 → Pert.Supplier f V M (baser F c) (narrow (B.focuses hj ha) s t ht) → ∀ᶠ i:ℕ in atTop,W (j (s i))) :
   ∀ᶠ k in atTop,W k := by
  refine hovers B ?_
  intro j hj ha
  obtain ⟨M,h1,h2,h3,_,he⟩:= chosen_lit (C:=C) hg.simpleGate
  obtain ⟨s,t,ht,c,hc,hV⟩ := reach F (B.focuses hj ha) (B.approaches hj ha) (by rw [h1]; exact B.stable_focus hj ha) hg.schedule he
  exact ⟨s,hv M h1 h2 h3 j hj ha s t ht c hc hV⟩ -- syntax fix

def lit (k:ℕ) (i j:Axis) := (B.lens k 4).symm (((B.radius k^4:ℝ):ℂ) • E i j)
lemma stress (i j:Axis) : Tendsto (fun k=> lit B k i j) atTop (𝓝 (Pert.freeStress C.labels i j)):= by
    refine Metric.tendsto_nhds.mpr (fun ε he=> universal B hg _ fun M h1 h2 h3 p hp hy s t ht c _ hs=> ?_)
    have hh:= Metric.tendsto_nhds.mp (Pert.meter_physical hs (T).conserved (true_tensor F) (T).charges i j) ε he
    rw [Pert.kappa_eq hg.simpleGate h1 h3, h3, Pert.common_stress, inv_neg, inv_one, neg_one_smul] at hh
    exact hh

lemma turns (d : ℕ) (i : Axis×Axis) : Tendsto (fun k => Spin.transport α (B.lens k d) i) atTop
    (𝓝 (Spin.attach (Maxwell.Free.gear C.labels) d i)) := by
    refine Metric.tendsto_nhds.mpr fun ε hε => universal B hg _ fun M h1 h2 h3 j hj ha s t ht c hc hS=> ?_
    let X:= narrow (B.focuses hj ha) s t ht
    let K:= α
    let q k := Spin.transport α (X.U k d) i
    have hr : leaves (baser F c).p 4=c • leaves (V).deriv 4 := rfl
    have Hx := (ratio hS hr).2.inv₀ M.T.hκ
    have hl := Hx.smul (for_angular hS d i)
    rw [smul_smul, inv_mul_cancel₀ M.T.hκ, one_smul] at hl
    have hu : Tendsto q atTop (𝓝 (Spin.leaf M.T.K.lie d i)):= by
      apply hl.congr; intro k
      have he : Spin.transport (baser F c).Y (X.U k d) i = c • q k := ContinuousLinearMap.ext (fun v=>?_)
      · change ((c/X.xi k)⁻¹) • ((X.xi k)⁻¹ • Spin.transport (baser F c).Y (X.U k d) i)= _
        rw [he, smul_smul,smul_smul,show (c/X.xi k)⁻¹ * (X.xi k)⁻¹ * c =1 from by field_simp [hc,(X.sign k).ne'], one_smul]
      let p:=X.U k d
      exact (p.symm.toLinearMap.restrictScalars ℝ).map_smul c _
    rw [h2] at hu; exact Metric.tendsto_nhds.mp hu ε hε
end zoom

variable (hg:OPE.Services C f S)
include hg
-- sigma packaging. actual Mantle path not necessarily StrictAnti so
-- expose the full theorem before wrapping it in the old API.
def tags {n:ℕ} (k:ℕ) (q : Slots n → (Bel C.book).Tag)
    (isJ : Slots n → Bool) (ab : Slots n → Axis × Axis) :=
  Pert.mixedTag (C:=C) q isJ ab (lit B k) -- mixed FREE label actual stress in coords
omit hg in
lemma pins {n:ℕ} (k:ℕ) (q : Slots n → (Bel C.book).Tag)
    (isJ : Slots n → Bool)(ab : Slots n → Axis × Axis)(i : Fin n):
    panels (Lenses.testLens (B.lens k)) (tags B k q isJ ab i) =
       if isJ i then ⟨4,((B.radius k^4 : ℝ):ℂ) • E (ab i).1 (ab i).2⟩ else ⟨(q i).1,B.lens k _ (q i).2⟩ := by
   unfold tags Pert.mixedTag
   split
   · change Sigma.mk 4 (B.lens k 4 ((B.lens k 4).symm _))= _
     rw [LinearEquiv.apply_symm_apply]
   rfl

-- not every-scale; use on each mantle plaque
lemma together {n:ℕ} (q : Slots n → (Bel C.book).Tag)
    (isJ : Slots n → Bool)(ab : Slots n → Axis × Axis) (j:ℕ) {K : Set (Points n)} (hK : IsCompact K) (hsep : K ⊆ conf n) {ε:ℝ} (he:0<ε) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ j (tested (B.radius k) (Lenses.testLens (B.lens k)) (tags B k q isJ ab)) x -
       iteratedFDeriv ℝ j (disc (Pert.freeWithStress C.labels q isJ ab)) x‖ ≤ ε := by
  let d (i : Slots n) : ℕ := if isJ i then 4 else (q i).1
  let f (i : Slots n) := Pert.freeWithStress C.labels q isJ ab i
  let g (k : ℕ) (i : Slots n) := tags B k q isJ ab i
  have hs i : (f i).1=d i := by cases hq : isJ i <;> simp [f,Pert.freeWithStress,hq,d]
  have ht k i : (g k i).1=d i := by cases hq : isJ i <;> simp [g,tags,Pert.mixedTag,hq,d]
  let u (i : Slots n) : (Bel C.book).Field (d i) := _root_.cast (congrArg _ (hs i)) (f i).2
  let v (k : ℕ) (i : Slots n) : (Bel C.book).Field (d i) := _root_.cast (congrArg _ (ht k i)) ((g k i).2)
  have hu : hang d u=f := funext fun i => Sigma.ext (hs i).symm (show (_root_.cast _ _ ≍ _) from cast_heq ..)
  have hv k : hang d (v k)=g k := funext fun i=>Sigma.ext (ht k i).symm (show (_root_.cast _ _ ≍ _) from cast_heq ..)
  have hl (i : Slots n) : Tendsto (fun k => v k i) atTop (𝓝 (u i)) := by
    have hf (s : Bool):
      let d : ℕ := if s then 4 else (q i).1
      let g(k) := if s then (⟨4,lit B k (ab i).1 (ab i).2⟩ : (S').Tag) else q i
      let f := if s then (⟨4,Pert.freeStress C.labels (ab i).1 (ab i).2⟩ : (S').Tag) else q i
      ∀ (h : f.1=d) (h':∀ k,(g k).1=d), Tendsto (fun k=> _root_.cast (congrArg _ (h' k)) (g k).2) atTop
         (𝓝 (_root_.cast (congrArg (S').Field h) f.2)):=by
      cases s
      · exact fun _ _ => tendsto_const_nhds
      exact fun _ _ => stress B hg _ _
    exact hf (isJ i) (hs i) fun k=>ht k i
  have e:=B.uniformJets v u hl j K hK hsep ε he; simp_rw [hv,hu] at e; exact e

/-- Also ready for FirstExtension demands. Don't infer all-real length from
this theorem. New scope in `turns`, `stress`, `together`.
-/
theorem ready_first {j:ℕ→ℕ} (hj:Tendsto j atTop atTop)(ha:StrictAnti (B.radius ∘ j)) : FirstExtension F (B.focuses hj ha) := by
   let X:=B.focuses hj ha
   obtain ⟨M,h1,h2,h3,_,hd⟩:= chosen_lit (C:=C) hg.simpleGate
   have he : Stable (H).spin M.hT.spin V M.T.W X:= by rw [h1]; exact B.stable_focus hj ha
   refine ⟨B.stable_focus hj ha,?_, (differential_rank (ho:=(T).rights) H M.hT M.T M.lit.hers hd (T).derivatives M.lit.pales X (B.approaches hj ha) he).2,
     fun d=> (by rw [← h1]; exact delivered (M:=M) F X (B.approaches hj ha) d), fun i d => (turns B hg d i).comp hj⟩
   intro n z q h i K hK hr ε he
   filter_upwards [hj.eventually (together B hg q h i z hK hr he)] with k hk x hx
   specialize hk x hx
   rw [show scaledPhysical (B.focuses hj ha) E k q h i = panels (Lenses.testLens (B.lens (j k))) ∘ tags B (j k) q h i from funext (fun l => (pins B _ _ _ _ l).symm)]
   exact hk
end YM.SharpGram.Load
