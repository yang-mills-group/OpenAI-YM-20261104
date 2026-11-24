import YM.Contacts.Power.Costs
import YM.MergeProof.North.Lauder
import YM.MergeProof.North.GraceN

/-! `Gentle`, not bounded-ratio. Tails and costs on arbitrary granularity.
Large schedules always have levels with prescribed running exponent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Power
open Filter Lattice RG Function
open MergeProof.Ribbons
open scoped Topology BigOperators
variable {α:Type*}{P:Pace α}{A:Schedule}{j k:α→ℕ}

/-- Location of any mesh-size quantity in the UV along this same schedule. -/
structure Mesh (P:Pace α)(A:Schedule)(j:α→ℕ)(a:ℝ) : Prop where
  cover : Tendsto j P.net atTop
  grade : Tendsto (fun i=>A.scale (j i)/P.scale i) P.net (𝓝 a)

namespace Mesh
variable {a b:ℝ}
lemma selectMesh (A:Schedule) (g:A.Gentle) (P:Pace α) {c:ℝ}(hc:0<c) : ∃ j, Mesh P A j c := by
  classical
  let y i:= c*P.scale i
  have h(i):∃ m,y i≤ A.scale m:= (A.divergent.eventually_ge_atTop _).exists
  let j i:= Nat.find (h i); have hv(i): y i≤ A.scale (j i):= Nat.find_spec (h i)
  have hM:Tendsto j P.net atTop:= tendsto_atTop.mpr fun k=> (((P.deep.const_mul_atTop hc).eventually_ge_atTop (A.scale k)).mono fun i hi=> (bob A).le_iff_le.mp (le_trans hi (hv i)))
  let u i:= j i-1; have he:Tendsto u P.net atTop:= (tendsto_atTop.mpr fun k=>(hM.eventually_gt_atTop k).mono fun i hi=> by dsimp [u]; omega)
  refine ⟨j,hM,tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun _=>c) (h:=fun i=> c*(A.scale (u i+1)/A.scale (u i))) tendsto_const_nhds ?_ ?_ ?_⟩
  · simpa using! ((barbell A g).comp he).const_mul c
  · filter_upwards [P.eventually_pos] with i hi; exact (le_div_iff₀ hi).mpr (hv i)
  filter_upwards [P.eventually_pos,(A.divergent.comp he).eventually_gt_atTop 0,hM.eventually_gt_atTop 0] with i hi hh ht
  have hx:A.scale (u i) < y i:= lt_of_not_ge (Nat.find_min (h i) (show u i<j i by unfold u; omega))
  have hh : 0 < A.scale (u i):=hh
  have h0 : 0 ≤ A.scale (j i):= hh.le.trans ((bob A).monotone (Nat.sub_le ..))
  rw [show u i+1=j i from (by dsimp [u]; omega), div_le_iff₀ hi,←mul_div_assoc c, div_mul_eq_mul_div, le_div_iff₀ hh]
  change A.scale _ < c*P.scale i at hx
  nlinarith only [h0,hx]

lemma noted (h : Mesh P A j a) {f : ℕ→ℝ}(hf: Note A f b) : P.Rating (b*a) fun i=> f (j i):= by
  refine ⟨Eventually.of_forall fun i=> hf.pos _,((hf.pitch.comp h.cover).mul h.grade).congr' ?_⟩
  filter_upwards [(A.divergent.comp h.cover).eventually_gt_atTop 0,P.eventually_pos] with i hi hx
  have hi: 0<A.scale (j i):=hi; dsimp only [comp_apply]; field_simp
lemma mesh_a (h:Mesh P A j a) : P.Rating (-a) (fun i=> A.a (j i)) := by simpa using h.noted (Note.note_a A)
lemma stays (h:Mesh P A j a) (F:Filter α)(he:F ≤ P.net): Mesh (P.refine he) A j a:=⟨h.cover.mono_left he,h.grade.mono_left he⟩
lemma thick (h:Mesh P A j a)(hh:Mesh P A k b)(ht:a<b) : ∀ᶠ i in P.net,j i < k i:=by
   obtain ⟨x,hx,hv⟩:= exists_between ht
   filter_upwards [P.eventually_pos,h.grade.eventually (gt_mem_nhds hx),hh.grade.eventually (lt_mem_nhds hv)] with i hi hp hh'; apply (bob A).lt_iff_lt.mp; exact (div_lt_div_iff_of_pos_right hi).mp (show _<_ from lt_trans (show A.scale (j i)/P.scale i<x from hp) hh') -- edit
lemma next (h : Mesh P A j a) (he:A.Gentle) : Mesh P A (fun i=> j i +1) a:= by
   refine ⟨tendsto_atTop_mono (fun i=> (j i).le_succ) h.cover, ((one_mul a) ▸ ?_)⟩ -- reverse
   apply Filter.Tendsto.congr' _ (((barbell A he).comp h.cover).mul h.grade); filter_upwards [(A.divergent.comp h.cover).eventually_gt_atTop 0] with i hi; have hi:0<A.scale (j i):=hi; dsimp only [comp_apply]; field_simp
lemma note_nn (S : Schedule) (f : ℕ → ℝ) (hx:∀ i,1≤f i) {g : ℕ→ℝ}(hh:Note S g 0)(ht:∀ᶠ i:ℕ in atTop,f i ≤ g i): Note S f 0:=by
   refine ⟨fun i=> zero_lt_one.trans_le (hx _),tendsto_of_tendsto_of_tendsto_of_le_of_le' (g:=fun i=> 0) (by exact tendsto_const_nhds) hh.pitch ?_ ?_⟩
   · filter_upwards [S.divergent.eventually_gt_atTop 0] with i hi; exact div_nonneg (Real.log_nonneg (hx _)) hi.le
   filter_upwards [ht,S.divergent.eventually_gt_atTop 0] with i ht hi; exact div_le_div_of_nonneg_right (Real.log_le_log (zero_lt_one.trans_le (hx _)) ht) hi.le
end Mesh
end YM.Contacts.Power
