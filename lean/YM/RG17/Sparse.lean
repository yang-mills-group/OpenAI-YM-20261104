import YM.RG17.Ledger
import YM.SharpGram.Lenses.Sights

/-!
# Enough geometry to situate real and measured lengths in one Layout

Strict matching LENGTH only along a subsequence of Mantle.radius;
make NO assumption that Lens covers every geometry in `Reports`. Can
pass a selected Layout proof on such geometry to every-r Returns iff also
supplied everywhere (on its domain) there. This component uses the physical
history's actual schedule and allows continued measuring work.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}{F:Final C f S}
    {u:Filter (ℕ×ℕ)}
set_option quotPrecheck false
local notation "ρ"=> OPE.run
local notation "H"=> C.path.levels.clock.hatBeta
local notation "spacing"=> C.S.a
local notation "σ"=> C.S.scale
variable (C) in
lemma armour : RateLE atTop σ H 0:=by
   have ht:RateIs atTop σ σ 0:= ⟨C.S.divergent.eventually_gt_atTop 0,Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp C.S.divergent⟩
   simpa only [zero_add] using! ((RateLE.const C.path.levels.clock.bar C.S.divergent).add
       (RateLE.const G.slopeConstant C.S.divergent|>.mul (ht.pays C.S.divergent)|>.mono (le_of_eq (zero_add _))) C.S.divergent)
variable (C) in
lemma strength : RateIs atTop σ H 0:= by
   have hp:∀ i:ℕ,1 ≤ H i:=fun i=>(C.path.levels.fits.delayed i).le
   exact RateIs.of_sandwich (RateIs.const C.S.divergent one_pos) (armour C) (Eventually.of_forall hp) (Eventually.of_forall fun _=> le_rfl) C.S.divergent
local notation "X"=> PertExtension.Running.choose C
variable (C) in
lemma catchLevel :Reach C (fun r=> PertExtension.Running.choose C r⁻¹):= by
   have he:= tendsto_inv_nhdsGT_zero (𝕜:=ℝ)
   refine ⟨(PertExtension.Running.choosing C).comp he,?_⟩
   simpa only [OPE.run,← Real.log_inv,Function.comp_def] using! (PertExtension.Running.close_mesh C|>.comp he)
variable (B:Lenses.Mantle F u)
local notation "R"=> B.radius
lemma radRate : RateIs atTop σ B.radius (-1):=by
   have ha : RateIs atTop σ spacing (-1):= ⟨Eventually.of_forall (fun _=> C.S.a_pos _),(MergeProof.Ribbons.Note.note_a C.S).pitch⟩
   have h := ha.pays C.S.divergent|>.mul ((armour C).pow 2 C.S.divergent)
   rw [mul_zero,add_zero] at h
   exact RateIs.of_sandwich ha h (B.proper.mono fun _ hx=>hx.1) (B.proper.mono fun _ hx=> hx.2) C.S.divergent
lemma retainedPaid : Tendsto (fun i=>σ i/ρ (B.radius i)) atTop (𝓝 1):=by
   have ht:= ((radRate B).rate).neg; rw [neg_neg] at ht
   have he:= ht.inv₀ one_ne_zero; rw [inv_one] at he; exact he.congr (fun _=> by rw [OPE.run,← neg_div,inv_div])
lemma homes : Tendsto B.radius atTop home:= tendsto_nhdsWithin_iff.mpr ⟨B.small,Eventually.of_forall (fun i=> B.positive i)⟩
lemma thinning : ∃ s: Extraction.Sequence,StrictAnti (B.radius ∘ ⇑s):= by
   choose q hq hQ using fun k:ℕ=> ((eventually_gt_atTop k).and (B.small.eventually (gt_mem_nhds (B.positive k)))).exists
   let s (n:ℕ):ℕ:= Nat.rec 0 (fun _ x=> q x) n
   exact ⟨⟨s,strictMono_nat_of_lt_succ fun i=> hq (s i)⟩,strictAnti_nat_of_succ_lt fun i=> hQ (s i)⟩
private lemma visible {a:ℕ→ℝ} (h:StrictAnti a)(ht:∀ i,0<a i)(Q:ℝ→Prop)
    (hQ:∀ᶠ i in atTop,Q (a i)) (hp:∀ᶠ i in home,i∉ Set.range a → Q i) : ∀ᶠ i in home,Q i:=by
   obtain ⟨N,hN⟩:= eventually_atTop.mp hQ
   filter_upwards [hp,(nhdsWithin_le_nhds (ge_mem_nhds (ht N)) : ∀ᶠ i in home,i ≤ a N)] with i he hm
   by_cases hh:i ∈ Set.range a; swap; exact he hh
   obtain ⟨m,rfl⟩:= hh; exact hN _ (h.le_iff_ge.mp hm)
lemma patchLevel (s:Extraction.Sequence)(hs:StrictAnti (B.radius ∘ ⇑s)) : ∃ p:ℝ→ℕ,Reach C p ∧ ∀ i:ℕ,p (B.radius (s i))=s i:=by
   let a:= B.radius ∘ ⇑s
   let p (r:ℝ):ℕ:= if h:r∈ Set.range a then s h.choose else X r⁻¹
   have hp(i:ℕ): p (a i)=s i := by
       rw [show p (a i)=_ from dif_pos (Set.mem_range_self i)]; exact congr_arg _ (hs.injective (Classical.choose_spec (mem_range_self i : ∃ j, a j=a i)))
   have ht i :0 < a i:= B.positive _
   have hv:=catchLevel C
   refine ⟨p,⟨tendsto_atTop.mpr ?_, Metric.tendsto_nhds.mpr ?_⟩,hp⟩
   · intro n; apply visible hs ht
     · filter_upwards [s.cofinal.eventually_ge_atTop n] with i hi; change n ≤ p (a i); rw [hp i]; exact hi
     filter_upwards [hv.growing.eventually_ge_atTop n] with i hi ht; change n ≤ p i; rw [show p i=X i⁻¹ from dif_neg ht]; exact hi
   intro ε he; apply visible hs ht
   · filter_upwards [s.cofinal.eventually (Metric.tendsto_nhds.mp (retainedPaid B) ε he)] with i hi; change dist (σ (p (a i))/ _) (1:ℝ)<ε; rw [hp]; exact hi
   filter_upwards [Metric.tendsto_nhds.mp hv.nearby ε he] with i hi he; rw [show p i= _ from dif_neg he]; exact hi
end YM.RG17
