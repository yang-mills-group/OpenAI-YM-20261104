import YM.GapsContact.Slab.VacGram
/-!
# Short slab normalized estimates along any Trace curve; ratio payments
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Ascent
open Function Filter Set Extraction Table Climb Spec MeasureTheory Trace Trace.Pilot
open Push.FiniteDetection.Free Trace.Terrace Trace.Over Next.UVStress MergeProof.East OPE.Levy
open Analysis Ward
open scoped Topology BigOperators InnerProductSpace Classical NNReal ContDiff

variable {G: Gauge} {C: Family G}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book} {d n : ℕ}
variable (F : Final C f S) (hG:G.Simple)
variable {H:(Climb.Bel C.book).Hierarchy}{J:Scaling S}{W:∀ i,Vane C i}{Z:Trace.Terrace.Arch C}
local notation "S'"=> Climb.Bel C.book
variable (h : StarPath f H J F.room.kernel 𝓛)
set_option quotPrecheck false
open Metric
local notation "D" => (Climb.Bel C.book).Field

include h hG
lemma window_upper (d:ℕ)(a b:ℝ)(ha:0<a):
    ∃ A:ℝ,1 ≤ A ∧ ∀ᶠ i:ℕ in atTop,∀ x:D d, ‖x‖ ≤ 1 →
       ∀ s:ℝ, s∈Icc a b → cost F d (J.r i * s) (J.U i d x) ≤ A := by
  let M:= D d; let z:= closedBall (0:M) 1
  by_contra! hk
  have hi(i:ℕ):∃ m≥i, ∃ (x:M × ℝ), x∈ z ×ˢ Icc a b ∧ sizeHint i < cost F d (J.r m * x.2) (J.U m d x.1):=by
    obtain ⟨m,hm,x,hx,s,hs,hy⟩:= frequently_atTop.mp (hk (sizeHint i) (by unfold sizeHint; simp)) i
    exact ⟨m,hm,(x,s),⟨mem_closedBall_zero_iff.mpr hx,hs⟩,hy⟩
  choose m hm y hv hy using hi
  obtain ⟨Y,hY,t,ht,hT⟩:= (IsCompact.prod (isCompact_closedBall _ _) isCompact_Icc).tendsto_subseq hv
  have hK := cost_seq F d hG h (m:=m ∘ t) ((tendsto_atTop_mono (f:=id) hm tendsto_id).comp ht.tendsto_atTop)
    (u:=(fun i=>(y i).1) ∘ t) (continuous_fst.continuousAt.tendsto.comp hT) (s:=(fun i=>(y i).2) ∘ t) (continuous_snd.continuousAt.tendsto.comp hT) (ha.trans_le hY.2.1)
  obtain ⟨B,hB⟩:= Filter.Tendsto.bddAbove_range hK
  obtain ⟨i,he⟩:= ((size_ascends.comp ht.tendsto_atTop).eventually_gt_atTop B).exists
  exact ((he.trans (hy (t i))).not_ge (hB (mem_range_self i)))

lemma window_lower (d:ℕ) : ∃ A:ℝ, 0 < A ∧ ∀ᶠ i:ℕ in atTop, ∀ x:D d, ‖x‖=1 → A ≤ cost F d (J.r i) (J.U i d x) := by
  by_contra! hu
  choose k hg x hx hv using fun i=> (frequently_atTop.mp (hu (costHint i) (Next.UVStress.cost_pos _)) i)
  have ht:Tendsto k atTop atTop:= tendsto_atTop_mono (f:=id) hg tendsto_id
  let T:= sphere (0:D d) 1
  obtain ⟨y,hY,t,he,hT⟩:= (show IsCompact T from isCompact_sphere _ _).tendsto_subseq (x:=x) (fun i=>by simp [T,hx])
  have hp:y≠0:=by intro h; simp [T,h] at hY
  let z:= reflect (C:=C) d y
  let L:= valTwo (S') d detectors y z
  have hL:L≠0:=by intro hx; exact (free_positive d y hp).ne' (congr_arg Complex.re hx)
  have ha:0<Real.sqrt ‖L‖:=Real.sqrt_pos.2 (norm_pos_iff.mpr hL)
  have hk:Tendsto (fun i=> cost F d (J.r (k (t i))) (J.U (k (t i)) d ((x∘t) i))) atTop (𝓝 (Real.sqrt ‖L‖)):=by
    simpa only [mul_one,one_smul,L,z] using! cost_seq F d hG h (ht.comp he.tendsto_atTop) hT (s:=fun _=>1) tendsto_const_nhds one_pos
  exact ha.not_ge (le_of_tendsto_of_tendsto' hk (cost_clears.comp he.tendsto_atTop) (fun i=> (hv (t i)).le))

lemma window_prices (d:ℕ)(a b:ℝ)(ha:0<a) : ∃ A:ℝ, 1 ≤ A ∧ ∀ᶠ i:ℕ in atTop,
      ∀ x:D d, ‖x‖ ≤ A * cost F d (J.r i) (J.U i d x) ∧
        ∀ s:ℝ, s∈Icc a b → cost F d (J.r i * s) (J.U i d x) ≤ A*‖x‖ := by
  obtain ⟨c,hc,hl⟩:= window_lower F hG h d
  obtain ⟨A,hA,hU⟩:= window_upper F hG h d a b ha
  refine ⟨max A c⁻¹,hA.trans (le_max_left ..),?_⟩
  filter_upwards [hl,hU] with i hl hU x
  rcases eq_or_ne x 0 with rfl|hx
  · simpa only [norm_zero,map_zero,cost_zero,mul_zero] using And.intro (le_refl (0:ℝ)) (show ∀ s:ℝ, s∈Icc a b → (0:ℝ) ≤ 0 from fun _ _=> le_rfl)
  have hX:= norm_pos_iff.mpr hx; let y:=((↑‖x‖⁻¹:ℂ) • x)
  have hy:‖y‖=1:= by unfold y; rw [norm_smul, Complex.norm_real,Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hX.ne']
  have hv(r):cost F d r (J.U i d y)=‖x‖⁻¹*cost F d r (J.U i d x):=by unfold y; rw[map_smul,cost_hom,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have hk:= hl y hy; rw[hv, le_inv_mul_iff₀ hX] at hk
  constructor
  · exact le_trans ((le_inv_mul_iff₀ hc).2 (by rw [mul_comm]; exact hk)) (mul_le_mul_of_nonneg_right (le_max_right ..) (cost_pos ..))
  intro s hs; have hq:= hU y hy.le s hs; rw [hv, inv_mul_le_iff₀ hX,mul_comm ‖x‖ A] at hq
  exact hq.trans (mul_le_mul_of_nonneg_right (le_max_left ..) hX.le)

local notation "I"=> Work.C01.single F.α.unselected F.room.kernel.laws.toSymmetric
structure Lodge (r:ℝ) (d:ℕ)(a b A:ℝ):Prop where
  before (p: ℝ≥0) (hp:0<p) : r*LogV r ≤ p → ∀ x:S.Field d, ‖I hp d x‖ ≤ A*cost F d r x
  advance (x:S.Field d) (s:ℝ) : s∈ Icc a b → cost F d (r*s) x ≤ A*cost F d r x
  definitive (x:S.Field d)(he:x≠0) : 0 < cost F d r x

omit h in
lemma open_lodge (hL:𝓛.toFilter ≤ f.fuse)(hp:Scribe f J W Z F.sector 𝓛 F.room.kernel H)(hV:PostT C.path.levels) (d:ℕ)(a b:ℝ)(ha:0<a):
    ∃ A:ℝ, 1 ≤ A ∧ ∀ᶠ i:ℕ in atTop, Lodge F (J.r i) d a b A := by
  obtain ⟨Y,hY⟩:=hp.meters; obtain ⟨D',hD,hT⟩:= basis_field F hL hY hV hG d
  obtain ⟨c,hc,hK⟩:= window_prices F hG hp.monorail d a b ha; let R:= (D'+c)*c
  have he: c ≤ D'+c:= le_add_of_nonneg_left hD; have hv:1≤R:= one_le_mul_of_one_le_of_one_le (hc.trans he) hc
  refine ⟨R,hv,?_⟩; filter_upwards [hT,hK] with i hi hh
  refine ⟨?_,?_,?_⟩
  · intro p h0 hl x; obtain ⟨x,rfl⟩:= (J.U i d).surjective x
    exact ( (hi p h0 hl x).trans (by gcongr; exact le_add_of_nonneg_right (zero_le_one.trans hc) : _ ≤ (D'+c)*‖x‖)).trans ((mul_le_mul_of_nonneg_left (hh x).1 (zero_le_one.trans (hc.trans he))).trans_eq (mul_assoc ..).symm)
  · intro x s hs; obtain ⟨x,rfl⟩:= (J.U i d).surjective x
    exact (((hh x).2 s hs).trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))).trans ((mul_le_mul_of_nonneg_left (hh x).1 (zero_le_one.trans (hc.trans he))).trans_eq (mul_assoc ..).symm)
  intro x hx; obtain ⟨x,rfl⟩:= (J.U i d).surjective x
  exact pos_of_mul_pos_right ((norm_pos_iff.mpr (show x≠0 from fun h=>hx (h.symm ▸ map_zero _))).trans_le (hh x).1) (zero_le_one.trans hc)
end YM.GapsContact.Ascent
