import YM.QuadraticLocal.Germ.Censor
import YM.QuadraticLocal.Germ.Obey
import YM.QuadraticLocal.Rough.Theater
/-!
# qlocal — passive actual test-geometric retention across Travel call/response

 Complete actual slot address as given by X in addition to root everywhere, including
 global/mixed/log, after shuffling split.Repeatable and on same tuple and representation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Pressure Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open PhysicalNext PhysicalNext.Repeat AnalyticBridge.VerifiedReset Progress.DirectedRecipe
open RemainderComparison
namespace Travel
variable {I V:Type}{G: Gauge}{n c L:Side}{x v e κ w a b d q z:ℝ}{α:Type*}
variable {A0:Teller G}{Q:ConnectedActivityE6.Target G A0}{Horizon:ConnectedActivityE6.Target.Order G w}
variable {S:StepData c n}{D:Pressure.Tube G S}{P:Rep G n}{P':Rep G c}
open ConnectedActivityE6
variable (H:Cash w x κ L Q Horizon z D P)
variable (E₀: ℕ→ RegularAddress c)(V₀:ℕ→ Config G c→ℝ) -- select unmarked first
open Lyric Muse Serif Spire Push.SectorMeasure
local notation "O"=> Chi.canonical
set_option quotPrecheck false
local notation "ωZ"=> (Match.staple (H:=H) («J»:=H) rfl rfl rfl)
local notation "Xa"=> Refrain.read H ωZ O E₀ V₀
variable {e f r s A B M Z : ℝ}
local notation "θ₀"=> P.p.supportExponent
local notation "θ₁"=> P'.p.supportExponent
local notation "p₁"=> P'.p
local notation "θ₂"=> (P'.p.supportExponent+1+1)
variable (W:Walk H P' e f r s)
local notation "ƒ"=> Spire.fees S.ratio.count θ₂
-- Aura recipe at a paid Horizon. D.clock answers EVERY load using Lamp cover; doesn't require model sup beyond `Bright`. `Ready` purchases at post calendar with arbitrary Root/Theta. Select s schedules for real occupancy clocks; budget tolerance in.Scale uses factor 2.
open Lotus
open Trigger Typeface GridRenewal.Rain
variable [DecidableEq V]{R:Marker.Census V}{o:V→Site n}
variable {Y Γ K : ℝ} {k k' : ℕ}
variable (Iris:Eyes H P' e Γ Y K k)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
namespace Parade
open Affinity Collar
variable {X:V→Type*} [∀ i,AddCommGroup (X i)] [∀ i,Module ℝ (X i)]
variable (C:∀ i,Set (X i))(J:∀ i,Submodule ℝ (X i))
variable (L0:Gallery (Affinity.Wallet C) I o P R)(σw:V→ℝ)
variable {b b':ℝ}
variable (U:Seal L0 σw b b')
variable (hw:∀ i,0<σw i)(hx:HasSlots P.p P.activities)
variable [Countable I]
local notation "A*"=> listCosts L0 σw hw hx U.supE U.crown (sighting L0 σw U) U.looks
local notation "z'"=> Trigger.axis L0 σw
variable {kZ:ℕ}(hC:∀ u:R.Mode,u.val.card≤kZ)(hE:2*(b+b')≤K)
local notation "pad'"=> Iris.pad
variable (u:Affinity.Wallet C)
local notation "L★"=> fiscal H (P':=P') Iris L0 σw U hw hx hE u
local notation "Ψ"=> Trigger.choir L0 σw hw kZ hC
variable {bMark:ℝ}(Sh:Throng.Ledger L0 U bMark)
-- Specify core hLease via exact `estimates.card` (could also use root-specific
-- tighter p.Pre.Card but sufficient post-L site uniform). hpT and hT_b: one
-- higher boost Ξ_F on any nonquiet K. Supports boosts per occurrence not per
-- marker in the aperture test (good even for multiinput join and MANY roots). 
local notation "δM"=> 2*(b+bMark) -- used opportunity
local notation "evθ"=> Fintype.card (Site (S.ratio.count))
variable {ρs ζK:ℝ}(hpF:1≤ρs)(hΩ : (Y*ρs) * (2*(b+bMark)) ≤ K )(hKT:1≤ζK)(hΞ: ζK*(2*(b+bMark)) ≤ K)(hT : Halo.hike Q x (Fintype.card (Site (S.ratio.count))) (ζK*(2*(b+bMark))) ≤ Daisy.ribbon Q L x)
local notation "hp!"=> financeStar H Iris L0 σw U hw hx hE u Sh hKT hT
local notation "hΩt"=> Travel.magic H Iris L0 σw U hw hx hE u Sh (zero_le_one.trans (one_le_mul_of_one_le_of_one_le Iris.bells.allowed hpF)) hΩ
local notation "hskt"=> Travel.magic H Iris L0 σw U hw hx hE u Sh (zero_le_one.trans hKT) hΞ
local notation "hCt"=> Travel.finance H Iris L0 σw U hw hx hE u Sh hKT hT
local notation "Θ"=> S.ratio.parent ∘ o
local notation "ρ"=> W.entrance
local notation "Ξ"=> W.offer
local notation "Y0"=> Refrain.read H ωZ O W.entrance W.offer
local notation "T!"=> Iris.bells
local notation "ℓ₀"=> Lanes.layoutGlobal H O pad' A* u (fun _ =>1) T! L★ H ωZ p₁ Iris.block Iris.pole ρ Ξ z' Ψ hCt (Trigger.colorCosting L0 S σw hx · p₁)
local notation "ℓ₁"=> Kiosk.First.led ℓ₀ W.first
local notation "M'"=> Creek.theater H O A* u (fun _=>1) Set.univ 0
local notation "μ"=> Lanes.tagged H A* u
local notation "μL"=> Lanes.honourL H O pad' A* u (fun _=>1) T! L★ p₁ Iris.block Iris.pole (le_refl _) (le_refl _) hpF hΩt
local notation "ƒL"=> QuadraticLocal.Pane.printBulbs Θ M' Set.univ z' μ (Flues.candle A* u S) μL
local notation "w₀"=> Spire.convertGlobal L0.E S p₁
local notation "β"=> (w₀).join ƒL
local notation "H'"=> L0.density
local notation "p0'"=> fun t=> S.push P.beta (TuneR (brand A* t) Set.univ (fun _=>1) 0 z' S)
local notation "early"=> fun t=> S.push P.beta (H' t)
local notation "γ"=> Γ
-- transposed guaranteed geometry. Projections claim ancestor COVER; don't shorten a stencil when comparing rank-jets. Mark input ν.TestSource.Account identifies whatever TestField in each locus the slot means.
variable (Loc:V→Support n) (hX:Collared Loc C J P L0)
local notation "X'"=> fun v=>(Loc v).image S.ratio.parent
local notation "Tab"=> Trigger.Table L0 × Bool
private def rolesR (L0:Gallery (Affinity.Wallet C) I o P R) (i:Trigger.Table L0×Bool):= (Trigger.status L0 i.1).val
local notation "tag"=> rolesR C L0
include hX
open RemainderComparison.Passion Flues Serif Mosaic WickReps
omit hX [∀ i,Module ℝ (X i)] [∀ i,AddCommGroup (X i)] [Countable I] in
private lemma labelOr : Passion.Oriented tag R Set.univ z':=by
    refine ⟨⟨fun x=> ⟨fun _=>?_,fun _=>Set.mem_univ _⟩⟩,fun i _ s h=>?_⟩
    · exact Finset.nonempty_iff_ne_empty.mpr (fun hv=> Trigger.status_hot L0 x.1 (Subtype.ext hv))
    rw [Trigger.axis,Poly.part_send, if_neg (show s≠ Trigger.status L0 i.1 from fun hx=>h (congr_arg Subtype.val hx))]
local notation "zeta"=> Affinity.intends J C tag
private lemma aims : ∀ (V':Config G n) i,(Affinity.intends J C (rolesR C L0)).Knows {i} (fun t=>(brand A* t i).ingredient V'):=by
    intro U i; apply Affinity.maps_one; exact rfl -- fix result order
    let j:= i.1; let b:= i.2
    have ht : Attn J C (tag i) (fun t=> Trigger.color L0 j t U):=by
       unfold j; rcases i with ⟨i|i,b⟩; swap; exact ((hX.hard.lesson _ U).each i.val.2).advice
       change Attn J _ _ (fun t=> L0.E.light t i.val U); simp_rw [Lamps.light,if_neg i.prop]; by_cases hx:Healthy P.p.threshold (L0.E.ground i.val) U
       · simp_rw [masked_eq _ _ _ _ hx]; exact hX.lamps.adv _ U
       simp_rw [masked_ne _ _ _ _ hx]; exact Attn.silent
    have he: Attn J C (tag i) (fun t=> Trigger.slice b (Trigger.color L0 j t U)):= by cases b; exact ht.linear Complex.reLm; exact ht.linear Complex.imLm
    exact he.scale (Poly.toll σw _)
omit hX [Countable I] in
private lemma participates (s:Multiset Tab)(v:V) (h:v∈ Solos.mapWord tag s) : ∃ i∈s,v∈ tag i:= by
   simpa only [Solos.mapWord,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Multiset.mem_bind,mem_val] using h
-- TAG rays with no leaves have no output labels. Use support proposition ∃t U, ingredient ≠0
-- stronger: any HONORED (syntactic) footprints must travel whenever those leaves REALLY participate. Zero labels appear only in unmasked solvent & dummy K padding; their carriers are never shrunk if even once used.
omit hX
private def earned (i:Trigger.Table L0×Bool):Prop:= ∀ v∈rolesR C L0 i, Loc v⊆ (Trigger.wing L0 i).support P
local notation "Et"=> earned C L0 Loc
local notation "Teacher"=> Affinity.witness (Affinity.Wallet C) (setOf Et)
include hX
private lemma sees : ∀ (V':Config G n) i,(Affinity.witness (Affinity.Wallet C) (setOf (earned C L0 Loc))).Knows {i} (fun t=>(brand A* t i).ingredient V'):=by
    intro V' i r hr hv t; obtain rfl:= Multiset.mem_singleton.mp hr; by_contra hn; apply hv; change Et _; unfold earned
    rcases r with ⟨r|r,b⟩
    · rw [Trigger.wingE L0 hx]; exact hX.lamps.house _
    intro v he; refine ((hX.hard.lesson r.val.1 V').each r.val.2).announces t ?_ _ he
    intro hv; apply hn; change Poly.toll _ _ * Trigger.slice b _=_; rw [show (Trigger.color L0 (Sum.inr r) t V')=0 from hv]; cases b; exact mul_zero _; exact mul_zero _ -- rw binder reduction ?
-- if X stencil for all needed fields then bulbs.ghost elimination 
local notation "K!"=> Flues.kettle H O A* u (fun _=>1) Set.univ 0 H ωZ ρ Ξ
local notation "η"=> stuff (funnel H A* u H ωZ) (Flues.badge H A* u H ωZ)
-- when genuine before map projection. Leaf.foot is projected carrying both origin & test locations.P.Fix every field.
omit hX in
private lemma projecting (i:Tab)(he:earned C L0 Loc i)(v:V)(hv:v∈tag i): X' v ⊆ candle A* u S i:= by
    exact image_subset_image (show Loc v⊆ (brand A* u i).crest from he v hv)
local notation "Rope"=> Lanes.shaft H O pad' A* u (fun _=>1) H ωZ p₁ Iris.pole ρ Ξ z' (Trigger.colorCosting L0 S σw hx · p₁)
omit hX in
private lemma intense {s:Multiset Tab} (f:Affinity.Wallet C→ℝ) (h:(Affinity.intends J C (rolesR C L0)).Knows s f)(q:R.Mode)(hp: (Verse.controls Set.univ z' s).part q≠0): Attn J C q.val f:=by
    have he:= Passion.spark (labelOr C L0 σw) s q hp; have hv:= he ▸ q.val.nodup; have H: Attn J C (Solos.mapWord tag s).toFinset f:= h hv; rw [← he,Finset.val_toFinset] at H; exact H
local notation "Bu"=> Affinity.Crown
private lemma ready i (V':Config G c): Affinity.Stencil X' C J (((Y0).forced (η i)).support) (fun t=>(Rope).val i t V'):=by
    refine ⟨fun q=>?_⟩; change Addressable _ _ _ _ q.val (fun t=>((K!).song Set.univ z' t V' i).part q)
    let a:= (Verse.controls Set.univ z' ((K!).score i)).part q; let f t:= (K!).glow t i V'; have he(t): ((K!).song Set.univ z' t V' i).part q=(↑(f t):ℂ)* a:= rfl
    simp_rw [he]; by_cases hp:a=0
    · simp_rw [hp,mul_zero]; exact Addressable.gone
    case neg=>
       have Hm : Attn J C q.val f:= intense C J L0 σw f (Collar.radiant H O A* zeta (aims C J L0 σw U hw hx Loc hX) u (fun _=>1) Set.univ 0 Iris.pad.S.N H ωZ ρ Ξ i V') q hp
       refine ⟨?_,fun t ht v hv=>?_⟩
       · simp_rw [mul_comm _ a]; exact (Hm.linear Complex.ofRealCLM.toLinearMap).linear (Algebra.lmul ℝ ℂ a) -- ofReal CLM
       have hv': f t≠0:= fun hv=> ht (by rw [hv]; simp); obtain ⟨j,hj,hv⟩:= participates C L0 _ v ((Passion.spark (labelOr C L0 σw) ((K!).score i) q hp) ▸ (show v∈q.val.val from hv))
       have hP := Collar.radiant H O A* Teacher (sees C J L0 σw U hw hx Loc hX) u (fun _=>1) Set.univ 0 Iris.pad.S.N H ωZ ρ Ξ i V'
       have he:= (Flues.aligned H O Iris.pad A* u (fun _=>1) Set.univ 0 H ωZ p₁ ρ Ξ Iris.pole).invested i t j hj V' hv'; exact (projecting (S:=S) C L0 σw U hw hx u Loc j (Classical.byContradiction fun hn=>hv' (hP j hj hn t)) v hv).trans he
lemma attentive : Affinity.Crown X' C J ℓ₁:=by
    apply Affinity.Crown.passage
    refine ⟨fun i V'=> ?_⟩; refine Affinity.Stencil.gather (g:=fun (j:{j // η j=i}) t=> (Rope).val j.val t V') ?_ ?_ -- σ f
    -- defeq L0,, Layout pivot
    · intro j; have hh:= ready H W Iris C J L0 σw U hw hx u Loc hX j.val V'; have hj:j.val=j.val:=rfl; rw [j.prop] at hh; exact hh
    · intro t; exact (Lanes.shaftValue H O Iris.pad A* u (fun _=>1) T! L★ H ωZ p₁ Iris.block Iris.pole ρ Ξ z' Ψ hCt _).quality Rope (show 0≤θ₂ from by have := (P').p.exponent_pos;linarith) hw V' t i
open QuadraticLocal.Pane Affinity.Polish Spire
local notation "AT"=> QuadraticLocal.Pane.Table (R:=R) Θ M' μ
private lemma actualized : Affinity.Polish.Static C J ƒL X':=by
    refine ⟨fun i U' hu=> ?_,fun i U' t h v hv=> ?_⟩
    · let q:= i.val.2; let f:=i.val.1; let a:= (Verse.controls Set.univ z' ((M').marks f)).part q
      have hh : Healthy (Pressure.temp x) ((M').halls f) U':= by
         rw [← Iris.pole]; exact hu
      filter_upwards [Collar.dew H O A* zeta (aims C J L0 σw U hw hx Loc hX) u (fun _=>1) Set.univ 0 Iris.pad.S.N U' f hh] with g hg
      change Attn J C q.val (fun t=> a*↑((M').solvent t f g)); by_cases h:a=0; simp_rw [h,zero_mul]; exact Attn.silent; exact ((intense C J L0 σw _ hg q h).linear Complex.ofRealCLM.toLinearMap).linear (Algebra.lmul ℝ ℂ a)
    · let q:= i.val.2; let f:=i.val.1; rw [QuadraticLocal.Pane.lights] at h; have he:= left_ne_zero_of_mul (show ( (↑((M').wet p₁ t f U'):ℂ)* ((Verse.controls Set.univ z' ((M').marks f)).part q))≠0 from h); have ha:= right_ne_zero_of_mul (show ( (↑((M').wet p₁ t f U'):ℂ)* ((Verse.controls Set.univ z' ((M').marks f)).part q))≠0 from h)
      obtain ⟨j,hj,hv⟩:= participates C L0 _ v ((Passion.spark (labelOr C L0 σw) _ q ha) ▸ (show v∈q.val.val from hv))
      have hm : f∈μ:=i.prop.1; have he : (M').wet p₁ t f U'≠0:= Complex.ofReal_ne_zero.mp he
      have hR:= fame M' μ _ μL _ hm
      refine (projecting (S:=S) C L0 σw U hw hx u Loc j ?_ v hv).trans (hR.travels t j hj U' he)
      by_contra ht; apply he; unfold Manor.wet; split
      next hc=>
        rw [hR.stall t hc]; have hp:=Next.Foundations.one_healthy ((M').halls f) _ (P'.p.threshold_pos).le («G»:=G); have hX₀: (Teacher).Knows ((M').marks f) (fun b=> (M').solvent b f 1):= (Collar.dew H O A* Teacher (sees C J L0 σw U hw hx Loc hX) u (fun _=>1) Set.univ 0 Iris.pad.S.N 1 f (Iris.pole ▸ hp)).self_of_nhds; exact hX₀ j hj ht t
      next=>
        by_cases hu':Healthy P'.p.threshold ((M').halls f) U'
        · rw [masked_eq _ _ _ _ hu']; have hp := (Collar.dew H O A* Teacher (sees C J L0 σw U hw hx Loc hX) u (fun _=>1) Set.univ 0 Iris.pad.S.N U' f (Iris.pole ▸ hu')).self_of_nhds; exact hp j hj ht t
        exact masked_ne _ _ _ _ hu'
lemma homes : Affinity.Polish.Static C J β X' :=by
    obtain ⟨ht,hv⟩:= actualized H Iris C J L0 σw U hw hx hE u Sh hpF hΩ Loc hX
    refine ⟨fun i V' _=> ?_, fun i V' t h v hv'=>?_⟩
    · rcases i with i|i
      · exact Eventually.of_forall fun j=> hX.lamps.adv i.val 1
      exact ht i V' (by assumption)
    rcases i with i|i
    · exact image_subset_image (hX.lamps.house _ _ hv')
    exact hv i V' t h v hv'
-- budget after ALL polys & slipping.Mask.Layout.Highlight
variable {η':Type}[Countable η'] {ι:Type}[Countable ι]
variable (b₀:Canopy.ShiftRows (Affinity.Wallet C) ι G P'.p (S.ratio.parent ∘ o) R) (K₀:Lamps (Affinity.Wallet C) η' G P'.p (S.ratio.parent ∘ o) R)
local notation "M₀"=> report H W Iris L0 σw U hw hx hC hE u Sh hKT hT b₀ K₀
local notation "χ"=> chamber C J β X' (homes H Iris C J L0 σw U hw hx hE u Sh hpF hΩ Loc hX)
lemma shines (hU:Taut X' C J K₀)(hH:∀ i U',Affinity.Stencil X' C J ((b₀.place i).val) (fun t=> b₀.soap t i U')): Collared X' C J P' M₀:=
    ⟨hU, Affinity.Crown.second _ W.second b₀ (attentive H W Iris C J L0 σw U hw hx hC hE u Sh hKT hT Loc hX) hH⟩
local notation "zeroₛ"=> Travel.void (R:=R) G p₁ Θ (Affinity.Wallet C)
variable [Fintype V]
variable (hr:0≤ s) (hY:∀ U:Config G c,P'.eval U≠0) (hp:P'.eval=S.push P.beta P.eval)
local notation "In"=> NamesFull H L0 σw U hw hx u
-- final certificate has Collared (`Crown/Taut`) after actual push. One career choice
-- for all wallet regs chosen earlier. Supports and ancestor phase. No fake mask read.
-- Epoch theorem ties prices for K.Primary. This call keeps local_θ per mark *log*
-- and strong marked-only norms at actual post layout. Not claiming price for extracted
-- one-markal entries beyond this opened layout. Work primary separate.
def roster : Gallery (Affinity.Wallet C) (Subtype (Affinity.Polish.Apt C β X')) Θ P' R:= report H W Iris L0 σw U hw hx hC hE u Sh hKT hT zeroₛ χ
local notation "U0"=> β
local notation "T'"=> roster H W Iris C J L0 σw U hw hx hC hE u Sh hpF hΩ hKT hT Loc hX
include hr hY hp hΞ hΩ
set_option maxHeartbeats 650000 in
lemma present (s':Tree.Forest S.ratio): let ge := ƒ*b+ρs⁻¹*Γ
    Collared X' C J P' T' ∧ (T').E.Paid σw P'.p.B θ₂ ge ∧ (T').Pays σw θ₁ ge r ∧ Throng.Hard.Pair (T').K σw P'.p.B θ₁ r (ζK⁻¹*r) ∧ ∀ t,S.push P.beta (L0.density t)=(T').density t:=by
    haveI := Travel.countF H L0 σw U hw hx u; obtain ⟨hPe,hP,hΩ',hT₁⟩:= Travel.broker H W Iris L0 σw U hw hx hC hE u Sh hpF hΩ hKT hΞ hT hr hY hp s'
    let ge:= ƒ*b+ρs⁻¹*Γ; change (Collared X' C J P' T') ∧ _ ; have hx' := homes H Iris C J L0 σw U hw hx hE u Sh hpF hΩ Loc hX
    refine ⟨shines H W Iris C J L0 σw U hw hx hC hE u Sh hKT hT Loc hX zeroₛ χ (tenancy C J β X' hx') (by simp), costs C J β X' hx' hPe, ⟨costs C J β X' hx' hP.budget,hP.wages⟩,hΩ', ?_⟩
    intro t; rw [hT₁ t]; funext U'; unfold Gallery.density; rw [show (T').E.log t U'= (β).log t U' from Affinity.Polish.stems C J β X' hx' t U']; rfl
end Parade
end Travel
end YM.QuadraticLocal
