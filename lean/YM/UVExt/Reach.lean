import YM.UVExt.ReadSlope
import YM.MergeProof.Noel

/-!
# A real shooting *interval* on one schedule

Output all inverse-coupling targets in a fixed neighborhood of the reference, without
retuning any lengths or recipe. This still uses the real intermediate value machinery and
DOESN'T show uniqueness or analyticity. `signal_one` gives a precise extra estimate which
would furnish uniqueness among the real Recipe trials, not an assumption in the existential
claims. No assertion that *new* trials have physical source grants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt
open Function Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories
open UVNext.CouplingReset Filter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}

def realRadius (a : Levels G) := min (a.clock.bar / 2) (G.slopeConstant * Real.log (a.S.block 0).val / 4)
lemma radius_pos (a : Levels G) (hG : G.Simple) : 0 < realRadius a := lt_min (half_pos a.clock.bar_pos)
  (by
    have h := a.S.block_large 0
    have hv : 1 < ((a.S.block 0).val : ℝ) := by exact_mod_cast (show 1 < (a.S.block 0).val from by omega)
    have hS := Gauge.slopeConstant_pos hG
    have hT := Real.log_pos hv
    positivity)

variable {a : Levels G} {p N : ℕ} {R : Recipe a}

lemma recipe_reaches (hG : G.Simple) (h : R.Issues N p) (hv : Drifting a) (b : ℝ)
    (hx : |b - a.clock.bar| ≤ realRadius a) : ∃ T, Competes R p N 0 T ∧ (T 0).beta=b := by
  have hb : b ∈ band a 0 := by
    rw [band,Calendar.hatBeta,Schedule.scale_zero,mul_zero,add_zero]
    have hz := abs_le.mp (hx.trans (min_le_left ..))
    have hβ := a.clock.bar_pos
    constructor <;> linarith
  by_cases hh : N=0
  · subst N
    obtain ⟨T,_,hv⟩ := h.initial
    obtain ⟨he,hK,hW⟩ := hv _ hb
    -- avoid need for a named padding recipe by coming from any existing trajectory, if R has one.
    obtain ⟨f,-⟩ := successful p 0 h hG ‹Drifting _›
    let u := update f 0 (T b); change ∃ t' : Trail a p, _
    have hU : u 0 = T b := update_self ..
    refine ⟨u,⟨fun i hi₁ hi₂ => ?_,hU ▸ hW,fun i _ hi=> (Nat.not_lt_zero i hi).elim⟩,hU ▸ he⟩
    obtain rfl := Nat.le_antisymm hi₂ hi₁
    exact ⟨hU ▸ hK,by change (update f 0 (T b) 0).beta ∈ _; rwa [update_self,he]⟩
  have hh : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hh
  obtain ⟨l,d,hld,F,hF,hS,hL,hR⟩ := steps p N h hG hv 1 hh
  obtain ⟨T,hT,hH⟩ := h.advances 0 hh l d hld (fun x=> F x 1) hS (fun x hi => (hF x hi).prices 1 le_rfl hh)
  have hlog : 0 < Real.log (a.S.block 0).val := Real.log_pos (by have he := a.S.block_large 0; exact_mod_cast (show 1<(a.S.block 0).val from by omega))
  have ha := (div_le_iff₀ hlog).mp (hv 0)
  have hq := abs_le.mp (hx.trans (min_le_right ..))
  have hΓₗ := abs_le.mp ((hH _ (Set.left_mem_Icc.mpr hld)).2.drift)
  have hΓᵣ := abs_le.mp ((hH _ (Set.right_mem_Icc.mpr hld)).2.drift)
  obtain ⟨z,hz,h₀⟩ := intermediate_value_Icc hld hT.beta (show b ∈ Icc (T l).beta (T d).beta from by
    constructor
    · rw [hL] at hΓₗ; unfold floorBeta at hΓₗ; rw [Schedule.scale_succ,Schedule.scale_zero] at hΓₗ; linarith
    · rw [hR] at hΓᵣ; unfold ceilBeta at hΓᵣ; rw [Schedule.scale_succ,Schedule.scale_zero] at hΓᵣ; nlinarith [Gauge.slopeConstant_pos hG]
    )
  change (T z).beta = b at h₀
  let f := update (F z) 0 (T z)
  have he : f 0=T z := update_self ..
  have hu {i : ℕ} (h : 0 < i) : f i=F z i := update_of_ne (Nat.pos_iff_ne_zero.mp h) (T z) (F z)
  refine ⟨f,⟨fun i hi hN=> ?_,hu hh ▸ (hF z hz).fromTop,fun i hi hN=>?_⟩,he ▸ h₀⟩
  · rcases eq_or_ne i 0 with rfl|h
    · exact ⟨he ▸ (hH z hz).1,he ▸ h₀ ▸ hb⟩
    rw [hu (Nat.pos_iff_ne_zero.mpr h)]; exact (hF z hz).prices i (Nat.pos_of_ne_zero h) hN
  have hS := hu (i:=i.succ) (Nat.succ_pos _)
  rcases eq_or_ne i 0 with rfl|hn
  · rw [he,hS]; exact (hH z hz).2
  rw [hu (Nat.pos_of_ne_zero hn),hS]; exact (hF z hz).persists i (Nat.pos_of_ne_zero hn) hN

def inverseAt (C : Family G) : Prop :=
    ∃ (S : Sheet G) (D : Rolls S) (Θ : Protection D) (W : Delays Θ) (q : Bar W)
       (I : Wait q) (Z : ChartRatio G) (P : MapPrices) (L : PostCost D) (B : Directed G I Z P L) (H : ℕ → ∀ v, Shoot.Trail B.a v),
       C.path=B.bake.make H ∧ B.Program ∧ (∀ N p,Competes B.bake p N 0 (H N p) ∧ (H N p 0).beta =B.a.clock.bar) ∧ 0 < realRadius B.a ∧ ∀ N p b, |b-B.a.clock.bar| ≤ realRadius B.a →
          ∃ T, Competes B.bake p N 0 T ∧ (T 0).beta=b

lemma reach_any {M : Metals G} {D : Rolls M.p} {A : Alloy M D} (C : Family G) (hG : G.Simple) (T : Bolt A)
    (he : C.path=Issue.trail T) : inverseAt C := by
    refine ⟨_,_,_,_,_,_,_,_,_,_,T.history,he,T.program,fun N p=> ⟨T.sticks N p,T.choice.reaches N p⟩,radius_pos _ hG,fun N p b hb=>?_⟩
    exact recipe_reaches hG (Directed.supplies _ T.program ..) (Drifting.pay A.B.valid) _ hb

section one_signal
variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)

/-- Sufficient for real inverse uniqueness; not asserted for all outputs. `Competes` trials
  carry the exact path constraints, identical pushes at all V, clipping, and bands everywhere,
  in particular initialized by the actual Wilson density. This only seeks uniqueness of the
  real *bare value* among such paths, not of every possible representation of that value. -/
structure EverySignal (b : ℝ) : Prop where
  detects (u v) : Competes B.bake p N 0 u → Competes B.bake p N 0 v → (u 0).beta=b → (v 0).beta=b →
    ∃ U, Signal B p N 0 (fun (x : ℝ) => if x=0 then u else v) {0,1} U

theorem signal_one (hG : G.Simple) (h : B.Program) {b : ℝ} (hs : EverySignal (N:=N) (p:=p) B b) (hv : |b-B.a.clock.bar| ≤ realRadius B.a) :
    ∃! α, ∃ T, Competes B.bake p N 0 T ∧ (T 0).beta=b ∧ (T N).beta=α := by
  obtain ⟨u,hU,hb⟩ := recipe_reaches hG (Directed.supplies _ h N p) (Drifting.pay B.valid) _ hv
  refine ⟨(u N).beta,⟨u,hU,hb,rfl⟩,fun a ⟨v,hV,hV',hv'⟩ => ?_⟩
  obtain ⟨Q,hJ⟩ := hs.detects v u hV hU hV' hb
  let F (x : ℝ) := if x=0 then v else u
  have hu : ∀ z∈({0,1}: Set ℝ), Competes B.bake p N 0 (F z) := by
    intro z _; unfold F; split_ifs <;> assumption
  simpa [F,knob,hv'] using signal_inverse p N B F hu Q hJ (i:=N)
    (x:=0) (y:=1) (by simp) (by simp) (Nat.zero_le _) le_rfl (by simp [knob,F,hV',hb])
end one_signal
end YM.UVExt
