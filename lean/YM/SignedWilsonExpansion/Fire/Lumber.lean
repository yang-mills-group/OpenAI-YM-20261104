import YM.SignedWilsonExpansion.Purchase.MomentS
import YM.SignedWilsonExpansion.Purchase.Onward
import YM.Extra.WEAK_SCALING_ACTLAW.Comparisons
set_option autoImplicit false
noncomputable section
namespace YM.SignedWilsonExpansion.Fire
open Function Filter Finset Lattice RG Wilson Source Labels Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Quince Quince.PreCost
open Purchases UVClock Schedules PurchVoice Extraction Asymptotics Commission
open WilsonCoeffUV.Bank PathCost
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge} (R:Run G)(h:G.Simple){n j d:ℕ}
local notation "C"=> R.family
variable {A:Levels G}

lemma n_le (A:Levels G) (j n:ℕ) : (n:ℝ) ≤ widthArc A j (j+n):=by
    induction n with
    | zero=> simp [widthArc]
    | succ n ih=>
      let M:=A.S.block ( j+n ); have hp:(3:ℝ)≤ M.val:=by exact_mod_cast A.S.block_large _
      have hv:1≤ Real.log (M.val:ℝ):= Real.le_log_iff_exp_le (by positivity)|>.mpr (Real.exp_one_lt_three.le.trans hp)
      unfold widthArc at *; rw [Nat.cast_add_one, ←Nat.add_assoc,A.S.scale_succ]; linarith
lemma fst_late {α β : Type*}(k:Filter α)(p:Filter β) : Tendsto Prod.fst (k.curry p) k := by
   apply tendsto_def.2; intro s hs; exact (show ∀ᶠ i in k, ∀ᶠ _ in p, i∈ s from Eventually.mono (p:=fun i=>i∈s) hs fun i hi=> Eventually.of_forall fun _=>hi)
lemma sum_epoch {ι:Type*} {ρ B:ι→ℝ}{j k:ι→ℕ}{L:Filter ι} (a: Glow A ρ B L j) (b: Glow A ρ B L k) : hemisphere A L B j k := by
    obtain x:= (b.sub a).congr_left (f₂ := fun i=> A.S.scale (k i) - A.S.scale (j i)) (by intro i; ring) -- name wrong
    refine ⟨1,?_⟩; simpa using x
abbrev ShapeS (ι:Type*) := ι × (ℕ×ℕ)
abbrev clock₁ {ι : Type*} (x:ShapeS ι): ℕ:= x.2.1
abbrev per₁ {ι : Type*} (x:ShapeS ι): ℕ:= x.2.2
abbrev promote {ι α:Type*} (x:ι→α) (i:ShapeS ι):α:= x i.1
lemma followY {ι:Type*} {X Y:ι→ℝ}{L:Filter ι}(F:Filter (ℕ×ℕ)) (h:Wage L X 1 Y): Wage (L.curry F) (promote X) 1 (promote Y):=by
    obtain ⟨k,v⟩:=h; exact ⟨k,v.comp_tendsto (fst_late L F)⟩
variable (W:Skill R.b (bear R.w))(g:GentleS R.family.path.levels)
variable {f:Extraction.Order}{ι:Type}{L:Filter ι}{B:ι→ℝ} {j n:ι→ℕ}
include R h W g
lemma earmark {A: ShapeS ι→ (R.family.label d ≃ₗ[ℂ] R.family.label d)} (p:Rise B L)
  (a: Epoch L B R.family.path.levels j)(b: hemisphere R.family.path.levels L B j (j+n))
  (hv:∀ᶠ x in L.curry f.fuse, ReceivesQ R.family d (clock₁ x) (per₁ x) (promote j x) (promote n x) (A x)) :
  ∃ Y ν: ShapeS ι→ℝ, ArmVote (L.curry f.fuse) (promote B) R.family d clock₁ per₁ (promote j) (promote n) Y ν A := by
    let J:= R.family.path.levels; have cap': Epoch L B J (j+n):= epoch_equiv p a b
    let K:= L.curry f.fuse; obtain ⟨Y,hY,hγ⟩:= colorIncome p g h b (Eventually.of_forall fun i=> Nat.le_add_right ..) a; let v:= fun i=> ζFront J (Y i) (j i)
    have hp: Rise (promote B) K:= p.comp (fst_late ..); have ht: Epoch K (promote B) J (promote j):= a.comp_tendsto (fst_late ..); have hx:∀ᶠ i:ShapeS ι in K, promote (j+n) i ≤ clock₁ i:= (show ∀ᶠ i:ι in L,∀ᶠ p in f.fuse,(j+n) i ≤ p.1 from Eventually.of_forall fun (i:ι)=> (Extra.WeakScaling.cofin_fst f).eventually_ge_atTop ((j+n) i))
    have hx':= UVClock.fee_Θ p J h a; have he:= followY f.fuse hY; let M := elect_lead J d h (C).labels p hY a
    refine ⟨promote Y,promote v,h,hp,ht,cap'.comp_tendsto (fst_late ..),he,( elect_lead J d h (C).labels hp he ht).1 ,?_⟩
    have hq: ∀ᶠ i:ShapeS ι in K,∀ N:ℕ, (promote (j+n) i) ≤ N→∃ Q, FrontStep R.family d (promote j i) (promote n i) N (per₁ i) (promote Y i) (promote v i) Q:=by
       change ∀ᶠ i in L,∀ᶠ y in f.fuse, _
       filter_upwards [hx'.eventually (birthQ J h), hx'.eventually_ge_atTop (R.family.ref d), M.2.eventually (ge_mem_nhds (by norm_num : 0<(1:ℝ)/2)), hγ ] with i u v φ hV
       apply ((Extra.WeakScaling.cofin_snd f).eventually (Step_quote R W h hV.1 ((n_le J ..).trans hV.2.1) v u _ φ)) -- type mismatch?
       intro l hl; exact hV.2.2 _ ( mem_Ico.mp hl ).2.le
    filter_upwards [(fst_late L f.fuse).eventually ( hx'.eventually ( open_late R.family h d )), hx,hq,hv] with x hz ht H' he
    exact ⟨⟨he,hz (per₁ x),ht⟩,issueQ R h (hz (per₁ x)|>.post) ht _, H' _ ht⟩
end YM.SignedWilsonExpansion.Fire
