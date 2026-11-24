import YM.Qlocal.Taxes
import YM.MergeProof.Zing

/-!
# Real re-expression at the entry. Purchasing the prologue

 Group the countable old labels **without changing the vacuum or any masks**.
 Every admissibility predicate remains tested as before. We *don't* assert that
 the grouped coefficients satisfy regular extension estimates (they may need
 not even be continuous at a flag boundary), and only group for launching the
 real component bounds, and later propagate regular comparison independently of
 that costing device. At each subsequent step when the payload traces include
 `Peak` etc, may use this purchase to continue. When using `Photo.given`, it
 matters that the regular key is unused and flavor packing avoids sharing
 multiple distinct modes on one Wing: otherwise would have to `heap` together!

 No loss depending on number of torus sites nor markers in the revival price.
 There may be arbitrary truncations/deletions etc in the marker algebra and
 test family. Need separate leases for captions propagated along identical
 manuscript-root pullback. May trade at ⟪any⟫ relative mark price.You
 don't have to actually normalize by multiplying the input marks before
 reading (can divide by charge etc, together with tolls), but that does
 need doing **in** the budget, as we do here. These proofs largely adapt/use
 native `BarCode`, Tape, Deck assembly helpers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Payload
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators
open Merge Switch UniformPays Publishing Emissions MergeProof Menu Accent Lotus
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ:ℝ}

/-- Weighted hit budget implies these sums are genuine even on same value fields. No
 claims that this UNROOTED number is volume-uniform. -/
lemma receives {p:BudgetPoint}{L:ι→Support n}{f:ι→ℝ}{q:ι→R.Mode} (h:∀ i,0 ≤ f i) (hc:∀ i,0 < c i)
    (ht:0≤a)(hl:∀ i,(L i).Nonempty)(hv:Ac.Hit L p.B (fun i=> c (q i)*f i) a B) : Summable f:=by
 let g(i):=c (q i)*f i; have hp i:0≤g i:=mul_nonneg (hc _|>.le) (h i)
 letI : Nonempty R.Mode:=⟨R.quiet⟩; obtain ⟨v,hv',hV⟩:= Finset.exists_min_image Finset.univ c Finset.univ_nonempty
 have hb:0<c v:=hc _
 have he:= Product.everyone_ne L _ hp (fun i _=>hl i) hv
 have hY:Summable (fun i=> c v*f i):= he.2.1.of_nonneg_of_le (fun i=>mul_nonneg hb.le (h _)) (fun i=>?_)
 · exact (summable_mul_left_iff hb.ne').1 hY
 · exact (mul_le_mul_of_nonneg_right (hV (q i) (mem_univ _)) (h _)).trans (le_mul_of_one_le_right (hp _) (Real.one_le_exp (mul_nonneg ht (by positivity))))

-- pressure-independent discount on arbitrary status keys.Values.S.
lemma bundle {F:ι→J} {L:J→Support n} {f:ι→ℝ} {ψ:J→ℝ} [Fintype J] (hv:Ac.Hit (L ∘ F) k (fun i=> ψ (F i) * f i) a B) :
       Ac.Hit L k (fun i=> ψ i * cram F f i) a B:=by
 intro x; let g(i:ι):=if x∈L (F i) then ψ (F i)*f i*Real.exp (a*coverNumber k (L (F i))) else 0
 have hg: SumBudget g B:=hv x; have he:= (heavy F hg.2.1); let d (j:J):= if x∈L j then ψ j*cram F f j*Real.exp (a*coverNumber k (L j)) else 0
 change SumBudget d B
 rw [show d=cram F g from ?_]; refine ⟨fun i=>tsum_nonneg (fun i=>hg.1 _),Summable.of_finite, he.tsum_eq.trans_le hg.2.2⟩
 funext i; unfold d cram; by_cases hi:x ∈ L i
 · rw [if_pos hi,← tsum_mul_left,←tsum_mul_right]; refine tsum_congr (fun j=>?_); unfold g; rw [j.prop,if_pos hi]
 rw [if_neg hi]; symm; exact (tsum_congr (fun j:{x// F x=i}=> if_neg (show x ∉ L (F j.val) from j.prop.symm ▸ hi))).trans tsum_zero

section for_parse
variable {dcl : Set (ℕ ×ℕ)} {Y:Taste Ω o P R} (hd : RetainsDeclared dcl Y s)
    (H:Peak P o Y c a A B) -- c positive.
variable (ht:a=P.p.supportExponent) (hΩ:Ω)(hz:∀ i,0<c i) -- representative
abbrev Alive (R:Census V):={z:R.Mode// z.val.Nonempty}
scoped instance footF (n:Side): Fintype (Foot n):=Fintype.ofInjective (fun x:Foot n=> (x.support,x.inventory))
  (fun _ _ h=> Progress.DirectedRecipe.foot_ext (congr_arg Prod.fst h) (congr_arg Prod.snd h))
-- might scope for downstream ; use local tag and export nonempty.Fintype instances when wrapping proofs.
abbrev Town (R:Census V)(s:V→Support n):= {z: Zone n × Alive R// speech z.2.val z.1.val s}
abbrev City (R:Census V)(s:V→Support n):= {z: Foot n × Alive R// speech z.2.val z.1.support s}
local notation "Tu" => Town R s
local notation "Cu" => City R s
local notation "branch" => Y.menu.branch
local notation "ray"=>Y.menu.rays
include H hd hΩ
lemma regular_ne (i:ℕ) : (Y.menu.branch i).Nonempty:= by
 obtain ⟨j,hj⟩:= (H.active hΩ).articles.proper i
 exact (Finset.nonempty_def.mpr ⟨o j,hd.regular i j hj (hd.origins j) ⟩)

def town (i:ℕ) : Town R s:= ⟨(⟨Y.menu.branch i,regular_ne hd H hΩ i⟩,⟨ray i, (H.active hΩ).articles.proper i⟩), hd.regular i⟩
def valley (i:dcl): City R s:=
  ⟨(readFoot (P.activities.forced i.val.1), ⟨Y.menu.marks i.val.1 i.val.2,(H.active hΩ).articles.occurs i.val.1 i.val.2⟩),hd.forced i.val.1 i.val.2 i.prop⟩
-- grouping map. At fields σ.Invariant/spatial. regular.Wing. All fields x.C.
omit H hd hΩ in
def clipped (Y:Taste Ω o P R) (x:Ω)(i:ℕ): Config G n→ℂ:= masked P.p.threshold (Y.menu.branch i) (Y.menu.regular x i)
set_option quotPrecheck false
local notation "Ω₀"=> town hd H hΩ
local notation "Ω₁"=> valley hd H hΩ
local notation "X₀"=> clipped Y
local notation "X₁"=> Y.menu.force

noncomputable abbrev snow (x:Ω)(i:Town R s)(U:Config G n) := cram (town hd H hΩ) (fun j=>clipped Y x j U) i

noncomputable abbrev stars (x:Ω)(i:City R s)(U:Config G n) := cram (valley hd H hΩ) (fun j:dcl=>Y.menu.force x j.val.1 j.val.2 U) i

set_option quotPrecheck false
local notation "L₀"=> snow hd H hΩ
local notation "L₁"=> stars hd H hΩ
structure Thin (p : BudgetPoint)(U:Support n)(f:Config G n→ℂ):Prop where
  measurable : Measurable f
  invariant : GaugeInvariant f
  reads : UsesFinal p.threshold U f
omit H hd hΩ
lemma Thin.cram (p:BudgetPoint){g:ι→J} {F:ι → Config G n→ℂ} {U:J→Support n} [Countable ι] (h:∀ j,Thin p (U (g j)) (F j))
    (x:J):Thin p (U x) fun y=> MergeProof.cram g (fun i=> F i y) x:= by
 refine ⟨Measurable.tsum (fun z=> (h z.val).measurable),fun i U=> tsum_congr fun j=> (h _).invariant ..,fun i j hx hp=>?_⟩
 exact tsum_congr fun z=>(h _).reads _ _ (z.prop.symm ▸ hx) (z.prop.symm ▸ hp)
lemma Thin.no_glimmer {g:ι→J} {F:ι → Config G n→ℂ} {U:J→ Config G n→Prop}
    (h:∀ i V,F i V≠0→ U (g i) V)(x:J)(V:Config G n) (hz: MergeProof.cram g (fun i=>F i V) x≠0): U x V:=
 Classical.byContradiction fun h' => hz ((tsum_congr (fun i':{i// g i=x}=> not_ne_iff.mp (mt (h i'.val V) (i'.prop.symm ▸ h')))).trans tsum_zero)

include H
set_option maxHeartbeats 1000000 in
lemma clip_ledger (x:Ω)(i:ℕ): Thin P.p (Y.menu.branch i) (X₀ x i):= by
 let f:= (H.active x).articles; have ht:= f.regular i
 refine ⟨masked_measurable _ _ _ ht.borel,fun T V=> ?_,fun U V hu hv=>?_⟩
 · unfold clipped; by_cases h:Healthy P.p.threshold (Y.menu.branch i) V;
   · rw [masked_eq _ _ _ _ h, masked_eq _ _ _ _ (show Healthy _ _ (Lattice.gauge T V) from (by unfold Healthy; rw [gauge_flags]; exact h))]; exact ht.symmetry T V
   rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (show ¬Healthy _ _ (Lattice.gauge T V) from (by unfold Healthy; rw [gauge_flags]; exact h))]
 have h: Healthy P.p.threshold (Y.menu.branch i) U ↔ Healthy P.p.threshold (Y.menu.branch i) V:=by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty,hv]
 unfold clipped; by_cases h': Healthy P.p.threshold (Y.menu.branch i) U
 · rw [masked_eq _ _ _ _ h',masked_eq _ _ _ _ (h.mp h')]; exact ht.sites U V hu
 rw [masked_ne _ _ _ _ h', masked_ne _ _ _ _ (mt h.mpr h')]

include hd hΩ
lemma snow_fit (x:Ω)(i:Town R s) : Thin P.p i.val.1.val (snow hd H hΩ x i) ∧ ∀ U,snow hd H hΩ x i U≠0→ Healthy P.p.threshold i.val.1.val U:=
 ⟨ Thin.cram P.p (g:=town hd H hΩ) (U:=fun i=>i.val.1.val) (fun i=>clip_ledger H x i) i, fun U=> Thin.no_glimmer (U:=fun x => Healthy _ x.val.1.val) (g:=town hd H hΩ) (F:=fun i=>clipped Y x i)
     (fun _ _ h=> Classical.byContradiction (fun he => h (masked_ne _ _ _ _ he))) i U⟩
lemma stars_fit (x:Ω)(i:City R s) : Thin P.p i.val.1.support (stars hd H hΩ x i) ∧ ∀ U,stars hd H hΩ x i U≠0→ i.val.1.support ∩ flags P.p.threshold U=i.val.1.inventory:=by
 let h₀:= (H.active x).articles; let E j: Config G n→ℂ:= Y.menu.force x (j:dcl).val.1 j.val.2; let t:=valley hd H hΩ
 exact ⟨ Thin.cram P.p (g:=t) (U:=fun i=> i.val.1.support) (F:=E) (fun i=>⟨h₀.meas i.val.1 i.val.2,h₀.invi i.val.1 i.val.2,h₀.inspects i.val.1 i.val.2⟩) i,
   fun U=> Thin.no_glimmer (U:=fun x y=>x.val.1.support ∩ flags P.p.threshold y=x.val.1.inventory) (g:=valley hd H hΩ) (F:=E) (fun i U h=> (h₀.keeps i.val.1 i.val.2 U h).1) i U ⟩

-- include witnesses of Summability in mg terror for assembly. no x-dependence
include ht hz
lemma light_funds : ∃ f:ℕ→ℝ, Summable f∧ (∀ i,0 ≤ f i) ∧ (∀ x i U, ‖clipped Y x i U‖≤ f i) ∧
      Ac.Hit (Y.menu.branch) P.p.B (fun i=> c (Y.menu.rays i) * f i) a A:= by
 obtain ⟨f,hf,hT,h⟩:=H.regular
 refine ⟨f, receives (p:=P.p) hf hz (ht.symm ▸ P.p.exponent_pos.le) (regular_ne hd H hΩ) h,hf,fun x i U=> ?_,h⟩
 by_cases hh:Healthy P.p.threshold (Y.menu.branch i) U
 · unfold clipped; rw [masked_eq _ _ _ _ hh]; obtain ⟨x₀,hx⟩:= regular_ne hd H hΩ i; exact (hT _ i x₀ hx).2 U hh [] (Nat.zero_le _) (by simp)
 unfold clipped; rw [masked_ne _ _ _ _ hh,norm_zero]; exact hf _

omit hd hΩ in
lemma dark_funds : ∃ f:ℕ ×ℕ→ℝ,Summable f∧(∀ i,0 ≤ f i)∧ (∀ x i U,‖Y.menu.force x i.1 i.2 U‖≤ f i) ∧ Ac.Hit (fun i=>(P.activities.forced i.1).support) P.p.B (fun i=>c (Y.menu.marks i.1 i.2)* f i) a B:=by
 obtain ⟨f,hf,hH,hE,h⟩:= H.forced; refine ⟨f,receives (p:=P.p) hf hz (ht.symm ▸ P.p.exponent_pos.le) (fun i=>?_ ) h,hf,hH,h⟩; exact (P.activities.forced _).inventory_ne.mono (P.activities.forced _).inventory_sup

lemma lights : ∃ f:Tu→ℝ, (∀ i,0 ≤ f i)∧ Ac.Hit (fun i => i.val.1.val) P.p.B (fun i=> c i.val.2.val*f i) a A ∧ ∀ i x U, ‖snow hd H hΩ x i U‖ ≤ f i := by
 obtain ⟨f,hf,hF,hV,hT⟩:= light_funds hd H ht hΩ hz; refine ⟨cram Ω₀ f,fun i=>tsum_nonneg fun j=> hF _, bundle (F:=Ω₀) hT,fun _ x U=> metric_cram Ω₀ hf (fun i=>hV x i U) _ ⟩

lemma darks : ∃ f:Cu→ℝ,(∀ i,0 ≤ f i)∧ Ac.Hit (fun i=> i.val.1.support) P.p.B (fun i=> c i.val.2.val*f i) a B∧ ∀ i x U,‖stars hd H hΩ x i U‖≤ f i := by
 obtain ⟨g,hg,hG,hB,hF⟩:= dark_funds H ht hz; let v i:=g (i:dcl).val; refine ⟨cram (valley hd H hΩ) v,fun i=>tsum_nonneg fun j=> hG _,bundle (F:=Ω₁) (fun i=> budget_pull (Subtype.val) Subtype.val_injective (hF i)), fun i x U=> metric_cram _ (c:=v) (hg.comp_injective Subtype.val_injective) (fun j:dcl=> hB x j.val U) _⟩ -- g ? v wrong
end for_parse
end YM.Qlocal.Payload
