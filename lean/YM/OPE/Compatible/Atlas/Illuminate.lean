import YM.OPE.Compatible.Atlas.Sprinter
/-!
# finish interpolation with eventual assumptions. Uniform over all addresses including off-grid. Prepare real basis later (don't analytically interpolate the averaging operations).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory FrameRead Lattice RG Wilson Boundary EveryPhase
open scoped Topology BigOperators Classical
variable {X V J:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){Q:Finset X}
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U: Spec.Final C F S}
variable {ψ:Filter V}{T p u: V→ℝ} {s: V→ X→ℝ} (A:Circuit U X V) (L:Allot C)
variable {η M b c d:ℝ}
variable (hG:G.Simple)(H:Glowing D Q ψ T s (η/2))
lemma time_bright (H:Glowing D Q ψ T s η) : ClearTime D Q ψ s:=by
    refine ⟨H.crowned,?_⟩; filter_upwards [H.dim, (eventually_all_finset Q).mpr (fun v h=> (H.fade _ h).eventually self_mem_nhdsWithin)] with i hi hp; exact ⟨hp,fun v w h hh=> hi w hh v h⟩
set_option quotPrecheck false
variable {B:ℕ}
local notation "m"=>fun i=> aperture D C B 2 (η/2) (T i) (s i)
include H L hG
lemma apprenticeship : ∀ᶠ i in ψ, ∀ j∈legs D Q,m i (par D j) ≤ m i j ∧ C.S.a (m i j) /s i (par D j) ≤ 1/T i^2:=by
   have he:= (time_bright D H).lit
   filter_upwards [(eventually_all_finset _).mpr (fun i (hi:i∈allUp D Q)=> adjusted_to_grid D (C:=C) H B 2 hi), he,H.ray.eventually_ge_atTop 1, series_angle D hG L H B] with i hᵤ hx hi hP j hj
   let v:=par D j; have hh:= hᵤ j (Finset.mem_of_mem_erase hj); have hv:v ∈ Q:= par_leg D Q H.crowned (Finset.mem_of_mem_erase hj); have hp:= hx.pos _ hv; constructor
   · have he:0<T i:=zero_lt_one.trans_le hi
     have hR:s i v ≤ s i (par D v):= hx.range' _ _ (par_le ..) hv; refine Nat.add_le_add_right ?_ 1; refine max_le_max (hP.timing (par D v) v (par_le ..) hv) (first_order (div_pos hp (pow_pos he _)) (div_le_div_of_nonneg_right hR (by positivity)))
   apply (div_le_iff₀ hp).2; exact hh.trans_eq (by change s i v / T i^2 = _; ring)
lemma illuminated (hP:Score ψ T p) (hb:0<b)(hd:0<d)(hv:∀ᶠ i in ψ,0 ≤ u i∧ u i ≤ Real.exp (c*T i)) (hp: ∀ᶠ i in ψ, ∀ x:X→ E4, Ridge (s i) (η/2) (M+1) D Q x → Screened D Q C x (m i) → u i*‖A.value i x‖ ≤ p i):
   ∃ w:V→ℝ,Score ψ T w∧ ∀ᶠ i in ψ,∀ x:X→E4,Ridge (s i) η M D Q x → (∀ a∈A.atoms,a.Quota D Q (s i) i x b (Real.exp (-d*T i))) → u i * ‖A.value i x‖ ≤ w i:=by
    obtain ⟨J,z,hz,hf⟩:= Circuit.branchable D Q s A
    choose c hC ht using fun j (hj:j∈J)=> relaunch D Q (m) A H.ray (time_bright D H) j hz hd (by linarith only [H.positive] : 0<η) hb (apprenticeship D L hG H (B:=B)) hP hp hv
    let f j (hj:j∈J) i:= ‖c j hj i‖
    refine ⟨fun i=>∑ j:J,f j j.2 i,Score.summar Finset.univ (fun (j:J) i=> f j.val j.2 i) H.ray (fun j _=> (hC j.val j.2).liftp (by simp [f])),?_⟩
    filter_upwards [eventually_all.mpr (fun j:J=> ht j.val j.2)] with i hi x hx he -- ht dependent fix
    obtain ⟨g,hg,hq⟩:=hf i x _ _ (Real.exp_pos _) he; let s:J:=⟨g,hg⟩; exact (hi s x hx fun a ha=> ⟨he a ha,hq a ha⟩).trans ((Real.le_norm_self (c s.val s.2 i)).trans (Finset.single_le_sum (f:=fun j:J=>f j.val j.2 i) (fun j _=> norm_nonneg _) (Finset.mem_univ s)))
end YM.OPE.Arboreal.Trace
