import YM.Qlocal.Projection
import YM.Integration.LocalComparisonDeclaredRetention
import YM.Integration.RiderTasteRegular
import YM.Extra.MULTISOURCE_BOUNDS.Bands
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Wind
/-!
Publishing the full comparison in the native test-uniform norms. Layout kept
*constant*, no vac normalization changing after call. This also allows
projecting to the relative product norm (`priceNormalized`, nonquiet only).
Implements the assembly for the step proofs here, e.g. turn-averaged renditions,
captions and all depletions. Mix.grain charges the factorial norm. We keep the
maybe more useful non-factorial global derivative norm at all pins as well,
including when captioning. RetainsDeclared on all routable & nonempty supports
(the interface `Retains` alone with dummy forced slots can be impossible, see
`LocalComparisonDeclaredRetention`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Publishing
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators
variable {ι Ω J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b δ A B θ:ℝ}

abbrev KLaw (P : RG.Rep G n)(i:ℕ)(f:Config G n→ℂ): Prop:=
  UsesFinal P.p.threshold (P.activities.forced i).support f ∧
     Measurable f ∧ GaugeInvariant f ∧ ∀ V : Config G n,f V≠0→ (P.activities.forced i).eligible P.p.threshold V
lemma dawn (i:ℕ) : KLaw P i 0:= ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _=>rfl,fun _ h=> (h rfl).elim⟩
lemma KLaw.smul {f: Config G n→ℂ} (h: KLaw P k f)(x:ℂ) : KLaw P k (x • f):= by
  obtain ⟨h,hB,hQ,hV⟩:=h; exact ⟨fun u v hu hv=> congr_arg (x*·) (h u v hu hv), hB.const_smul x,fun i U=>congr_arg (x*·) (hQ i U),fun U hu=> hV _ (right_ne_zero_of_mul hu) ⟩
lemma KLaw.sum {f:ι→ Config G n→ℂ} (s:Finset ι) (h:∀ i∈s, KLaw P k (f i)):KLaw P k (∑ i∈s,f i) := by
 induction s using Finset.induction with
 | empty => rw [Finset.sum_empty]; apply dawn
 | insert a s hy he => rw [Finset.sum_insert hy]; let f' :=∑i∈s,f i
                       obtain ⟨h₁,hB,hτ,hV⟩:=he (fun _ hw=> h _ (mem_insert_of_mem hw)); obtain ⟨ht,hr,h',hp⟩:= (show KLaw P k (f a) from h a (by simp)); exact
                        ⟨fun u v hu hv=>congr_arg₂ (·+·) (ht u v hu hv) (h₁ u v hu hv), hr.add hB,fun i U=> congr_arg₂ (·+·) (h' i U) (hτ i U), fun U hh=>
                          Classical.byContradiction (fun hl=>hh (show f a U+ f' U=0 from (by unfold f'; rw [not_ne_iff.mp (mt (hp U) hl), not_ne_iff.mp (mt (hV U) hl),zero_add])))⟩

/-! Layout. -/
variable (L:Ledger Ω J G n R)(P) (o s)
local notation "P'"=> P.activities
local notation "p"=> P.p
-- static query flags for adaptation.Carry all inputs as kernels. choose all above.
structure Ethics : Prop where
 origins i : o i∈s i
 branch j : (L.region j).Nonempty
 constant x j U : L.total j → L.raw x j U=L.raw x j 1
 quiet x j U : (L.raw x j U).part R.quiet=0
 owns x j q U : (L.raw x j U).part q≠0→ ∀ i∈q.val,s i⊆L.region j
 hard x j q : KLaw P j (fun U=>(L.forced x j U).part q) -- quiet too
 hosts x i U q : (L.forced x i U).part q≠0 → ∀ v∈q.val,s v⊆(P.activities.forced i).support
 base x j U : (L.forced x j U).part R.quiet=(P.activities.K j U:ℂ)

abbrev Tons (u : R.Mode→ℝ) (f:J× R.Mode→ℝ) (i:J):ℝ := ∑ q : R.Mode, u q * f (i,q)
-- `dens v * toll`. choose nonnegative. we include the quiet cost with optional density zero to exclude K vacuum if useful. actual separately.
def exchange (Z: R.Mode→ℝ) (w:V→ℝ) (v:R.Mode):ℝ:= Poly.toll w v * Z v

structure Bulk (u:R.Mode→ℝ) (α T W:ℝ) : Prop where
 regular : ∃ f:J×R.Mode→ℝ, (∀ i,0≤ f i) ∧ (∀ i: J,∀ j:R.Mode, ∀ x:Ω, let g(U:Config G n):=(L.raw x i U).part j
                       P.p.Regular (L.region i) g ∧ ∀ z∈L.region i,P.p.supBounds z (L.region i) g (f (i,j))) ∧
            Ac.Hit L.region P.p.B (Tons u f) α T
 forced : ∃ f:ℕ×R.Mode→ℝ,(∀ i,0≤ f i)∧ (∀ i:ℕ,∀ j: R.Mode,(∃ v∈j.val, ¬s v⊆(P.activities.forced i).support)→ f (i,j)=0)∧
            (∀ (x:Ω) i V j, ‖(L.forced x i V).part j‖≤f (i,j))∧
            Ac.Hit (fun i=>(P.activities.forced i).support) P.p.B (Tons u f) α W

-- first produce stronger Materialized main relation: `Peak` on Taste, retaining all x,
-- direction witnesses and sup at all pins. Then downscale for RelativeBudget using
-- `T` itself. For reading output mask and projection need exact relation.P.A.
local notation "expense"=> Ac.Hit
structure Peak (A:Taste Ω o P R) (q:R.Mode→ℝ) (α:ℝ)(C E:ℝ) : Prop where
 active x : (A.leaf x).Active
 -- capture every non-unit caption, unit free only if explicit fixed zero here
 units x i : A.menu.global x i=0
 regular : ∃ f:ℕ→ℝ, (∀ i,0≤ f i)∧(∀ x i j,j∈A.menu.branch i→P.p.supBounds j (A.menu.branch i) (A.menu.regular x i) (f i))∧
       Ac.Hit A.menu.branch P.p.B (fun i => q (A.menu.rays i) * f i) α C
 captions : ∃ f:ℕ→ℝ,(∀ i,0 ≤ f i)∧ (∀ x i, ‖A.score x i‖ ≤ f i)∧
       Ac.Hit A.site P.p.B (fun i=>q (A.tag i)*f i) α C
 forced : ∃ f:ℕ×ℕ→ℝ,(∀ i, 0≤f i)∧ (∀ x i U, ‖A.menu.force x i.1 i.2 U‖ ≤ f i)∧
       (∀ (i j : ℕ), 0 < f (i,j) → ∀ v∈(A.menu.marks i j).val,o v∈ (P.activities.forced i).support)∧
       Ac.Hit (fun i:ℕ×ℕ=> (P.activities.forced i.1).support) P.p.B (fun i=> q (A.menu.marks i.1 i.2)* f i) α E

namespace Bulk
lemma proclaim (X : J→ Support n)(u : R.Mode→ℝ) (y : J × R.Mode→ℝ)(h0:∀ i,0 ≤ y i) (hp :∀ v,0 ≤ u v) (H : Ac.Hit X P.p.B (Tons u y) a A) : Ac.Hit (X ∘ Prod.fst) P.p.B (fun i : Key J R=> u i.2.val*y (i.1,i.2.val)) a A:=by
 intro z; let E j := if z∈ X j then Real.exp (a*coverNumber P.p.B (X j)) else 0
 let f(i:J × R.Mode):= if z∈ X i.1 then u i.2 * y (i.1,i.2)* Real.exp (a*coverNumber P.p.B (X i.1)) else 0
 have hB:(∀ i,0 ≤ f i):=by intro i; unfold f; split; exact mul_nonneg (mul_nonneg (hp _) (h0 _)) (Real.exp_nonneg _); exact le_rfl
 let b(k: Key J R): J×R.Mode := (k.1,k.2.val);
 refine budget_pull (b) ?_ (budget_rows f _ ?_ (H z))
 · exact fun i j he=> Prod.ext (congr_arg (fun x: J× R.Mode=> x.1) he) (Subtype.ext (congr_arg (fun x:J×R.Mode=> x.2) he))
 intro i; refine budget_finite (fun j=> hB (i,j)) ?_; by_cases hc:z∈X i
 · unfold f Tons; rw [if_pos hc,Finset.sum_mul]; apply sum_le_sum; intro j _; simp only [hc,if_true, le_refl]
 unfold f; simp only [hc, if_false, Finset.sum_const_zero, le_refl]
end Bulk

variable [Countable J] [Nonempty V]
local notation "W"=> L.taste P o s
local notation "DK"=> Key ℕ R
local notation "RK"=> L.RegularKey s
local notation "A!"=> P.activities

def Declared (s:V→Support n) (R : Census V) : Set (ℕ × ℕ):= {z|Ledger.forceDeclared (R:=R) P s z.1 z.2}

abbrev forces (R : Census V) : Key ℕ R ↪ ℕ × ℕ := ⟨fun k=> (k.fst,pin k),fun _ _ he=> pin_injective (congr_arg Prod.snd he)⟩

lemma force_tag (k:DK) : (W).menu.marks k.fst (pin k) = k.2.val:= by simp only [Ledger.taste,Ledger.view,codedMode,unpin_pin]
lemma force_off (x:Ω) (i:ℕ ×ℕ) (h:i∉ Set.range (forces R)) : (W).menu.force x i.1 i.2=0:= by
  apply funext; intro U; exact L.forced_offRoute P o s x i.1 i.2 U (fun ⟨z,hz,he⟩=>h ⟨z,Prod.ext he hz⟩)

variable {L s o P}
omit [Nonempty V] in

lemma regular_ray_nonempty_ (k:R.Mode) (h:k≠R.quiet) : k.val.Nonempty:=
         nonempty_iff_ne_empty.mpr fun hl=> h (Subtype.ext hl)
variable (h: Ethics P o s L)(k:R.Mode→ℝ)(h₀: ∀ v,0≤ k v)(hB:Bulk P s L k a A B)
set_option maxHeartbeats 1000000
include h
lemma retains_ : RetainsDeclared (Declared P s R) W s:= by
 refine ⟨h.origins,L.regular_covers P o s,?_,?_,L.caption_covers P o s⟩
 · rintro i j ⟨z,rfl,rfl,ht⟩; rw [force_tag]; exact ht
 intro i j hj x; ext U; exact L.forced_offDeclaration P o s (fun _ _ _ _ hp=>h.hosts _ _ _ _ hp) _ _ _ _ hj

include hB
lemma activates (x:Ω) : ((W).leaf x).Active :=by
 have hg : ∀ i,((W).menu.rays i).val.Nonempty:=by
   intro i; by_cases hv:i∈Set.range (pin (α:=RK)); swap; · simp only [Ledger.taste,Ledger.view,unpin_blank _ _ hv]; exact Finset.singleton_nonempty _
   obtain ⟨z,rfl⟩:=hv; rw [Ledger.regular_mode]; exact regular_ray_nonempty_ _ z.val.2.prop
 have hv i j s : o j ∈ (W).menu.branch i:= L.regular_covers P o _ i j s (h.origins j)
 have hW(i j:ℕ): KLaw P i ((W).menu.force x i j):= by
   by_cases hu:(i,j)∈Set.range (forces R); swap; · exact (force_off P o s L x (i,j) hu).symm ▸ dawn _
   obtain ⟨z,hz⟩:=hu; obtain ⟨hz,rfl⟩:= Prod.mk_inj.mp hz; subst i; change KLaw P _ ((W).menu.force _ _ (pin z)); exact (funext (L.forced_source P o s x z.fst z.2)).symm ▸ h.hard ..
 refine ⟨⟨hg,hv,fun i=>?_,fun i j=>?_,fun i j hi v hp=>(retains_ h).forced i j ?_ v hp (h.origins v), fun i j=>(hW i j).1, fun i j=>(hW i j).2.2.2, fun i j=>(hW i j).2.1, fun i j=>(hW i j).2.2.1⟩, hg,hv⟩
 · obtain ⟨u,hp,hU,hB⟩:= hB.regular; by_cases he:i∈Set.range (pin (α:=RK)); swap; · simp only [Taste.leaf, View.terms,Ledger.taste,Ledger.view,unpin_blank _ _ he]; exact (Extra.Histories.regular0 P.p _ 0).1
   obtain ⟨z,rfl⟩:=he; simp only [Taste.leaf, View.terms,Ledger.taste,Ledger.view,unpin_pin]; let i:=z.val.1; by_cases h: L.total z.val.1
   · simp only [h,if_true]; exact (Extra.Histories.regular0 _ _ 0).1
   simp only [h,if_false]; exact ((hU z.val.1 z.val.2.val x)).1
 · by_cases hv:j∈Set.range (pin (α:=DK)); swap; · simp only [Taste.leaf, View.terms,Ledger.taste,Ledger.view,codedMode,unpin_blank _ _ hv]; exact singleton_nonempty _
   obtain ⟨v,rfl⟩:=hv; simp only [Taste.leaf, View.terms,Ledger.taste,Ledger.view,codedMode,unpin_pin]; exact regular_ray_nonempty_ v.2.val v.2.prop
 exact Classical.byContradiction (fun hv=> hi ((retains_ h).padding i j hv x))

include h₀
theorem assemble : Peak P o (W) k a A B := by
 constructor
 · exact activates h k hB
 · intros; rfl
 · obtain ⟨f,hF,hS,hW⟩:= hB.regular; let F(x:RK):= f (x.val.1,x.val.2.val); let μ : RK ↪ ℕ:=⟨pin,pin_injective⟩; let z:= stuff μ F; have hz(i): z (pin i)= F i:=stuffed μ F i
   refine ⟨z,Rack.positive _ _ (fun i=>hF _),fun x i u hu=> ?_, fun i=> transfer_budget μ ?_ ?_ (budget_pull (Subtype.val : RK→Key J R) Subtype.val_injective (Bulk.proclaim P _ k f hF h₀ hW i))⟩ -- name positive?
   · by_cases ht:i∈Set.range μ; swap; · simp only [Ledger.taste,Ledger.view,unpin_blank _ _ (show i∉ Set.range pin from ht),z,blank μ F ht]; exact (Extra.Histories.regular0 ..).2
     obtain ⟨r,rfl⟩:=ht; let r':= r.val.1; change u∈(W).menu.branch (pin r) at hu; rw [Ledger.regular_region] at hu; change P.p.supBounds _ ((W).menu.branch (pin r)) ((W).menu.regular _ _) (z (pin r)); rw [Ledger.regular_region,hz]; simp only [Ledger.taste,Ledger.view, show μ r=pin r from rfl, unpin_pin]; by_cases hb: L.total r.val.1
     · simp only [hb,if_true]; exact Local.bound_weaken (f:=0) (Extra.Histories.regular0 _ _ u).2 (hF _)
     simp only [hb,if_false]; exact (hS r.val.1 r.val.2.val x).2 u hu
   · intro j; dsimp only; rw [show μ j=pin j from rfl, Ledger.regular_region, Ledger.regular_mode,hz]; rfl
   intro j hj; dsimp only; unfold z; rw [blank μ _ hj]; simp
 · obtain ⟨f,hF,hS,hW⟩:= hB.regular; let F(x:RK):= f (x.val.1,x.val.2.val); let μ : RK ↪ ℕ:=⟨pin,pin_injective⟩; let z:= stuff μ F; have hz(i): z (pin i)= F i:=stuffed μ F i
   refine ⟨z,Rack.positive _ _ (fun i=>hF _),fun x i=> ?_, fun i=>transfer_budget μ ?_ ?_ (budget_pull (Subtype.val : RK→Key J R) Subtype.val_injective (Bulk.proclaim P _ k f hF h₀ hW i))⟩
   · by_cases ht:i∈Set.range μ; swap; · rw [show (W).score x i=0 from (by simp only [Ledger.taste,unpin_blank _ _ (show i∉ Set.range pin from ht)])]; unfold z; rw [blank μ F ht,norm_zero]
     obtain ⟨r,rfl⟩:=ht; change ‖(W).score x (pin r)‖ ≤ z (pin r); rw [hz]; simp only [Ledger.taste, unpin_pin]; split; swap; · rw [norm_zero]; exact hF _
     obtain ⟨u,hu⟩:=h.branch r.val.1; have hU : Healthy P.p.threshold (L.region r.val.1) (1:Config G n):= by unfold Healthy; rw [UVNext.CouplingReset.flags_one]; simp
     exact ((hS r.val.1 r.val.2.val x).2 u hu).2 (1:Config G n) hU [] (Nat.zero_le _) (by simp)
   · intro j; dsimp only; rw [show μ j=pin j from rfl,hz]; simp only [Ledger.taste,Ledger.view,unpin_pin]; rfl
   intro j hj; dsimp only; unfold z; rw [blank μ _ hj]; simp
 obtain ⟨f,hF,hY,hS,hW⟩:= hB.forced; let F (x:DK):= f (x.1,x.2.val); let z:=stuff (forces R) F
 refine ⟨z,Rack.positive _ _ (fun i=>hF _),fun x i U=>?_,fun i j hp v hv=> ?_, fun i=> transfer_budget (forces R) ?_ ?_ (Bulk.proclaim P _ k f hF h₀ hW i)⟩
 · by_cases ht:i∈Set.range (forces R); swap; · rw [force_off _ _ _ _ x i ht]; unfold z; rw [blank _ F ht, Pi.zero_apply,norm_zero]
   obtain ⟨r,rfl⟩:=ht; unfold z; rw [stuffed]; change ‖(W).menu.force x r.1 (pin (r.1,r.2)) U‖≤ _; rw [Ledger.forced_source]; exact hS ..
 · by_cases ht:(i,j)∈Set.range (forces R); swap; · exact False.elim (hp.ne' (blank _ _ ht))
   obtain ⟨r,hV⟩:=ht; rcases r with ⟨u,y⟩; obtain ⟨rfl,rfl⟩:= Prod.mk_inj.mp hV; apply (fun he:s v⊆ ((A!).forced u).support=> he (h.origins v)); rw [force_tag] at hv; exact Classical.byContradiction (fun he=> hp.ne' ((stuffed (forces R) F (u,y)).trans (hY u y.val ⟨v,hv,he⟩)))
 · intro i; dsimp only; unfold z; rw [stuffed]; rw [show ((W).menu.marks ((forces R) i).1 ((forces R) i).2) = i.2.val from force_tag _ _ _ _ i]; rfl
 intro j hj; dsimp only; unfold z; rw [blank _ _ hj]; simp
end YM.Qlocal.Publishing
namespace YM.Qlocal.Publishing
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators
variable {Ω J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b δ A B θ κ:ℝ}

namespace Peak
variable {T:Taste Ω o P R}
    (w : V → ℝ) {L : J→Support n} {Q : J→R.Mode} {f:J→ℝ}
local notation "p"=> P.p
local notation "x★"=> P.activities
variable (hp: P.p.supportExponent ≤ a)
include hp
private lemma per_mark (h : Ac.Hit L P.p.B (fun i=>Poly.toll w (Q i)* f i) a b) (h₁:∀ x,0<w x)(hx:∀ i,0≤ f i)
    (hr : ∀ i,0 < f i → ∀ j∈(Q i).val,o j∈L i) (j:V): SumBudget (fun i => if j∈ (Q i).val then Poly.toll w (Q i) * P.p.mass (L i) (f i) else 0) b:=by -- hp include
 refine budget_mono (h (o j)) (fun i=> ?_) (fun i=> ?_)
 · split; exact mul_nonneg (Poly.worth h₁ _).le (mul_nonneg (Real.exp_nonneg _) (hx _)); rfl
 split
 next hi=>
   rcases eq_or_lt_of_le (hx i) with he|he; · rw [BudgetPoint.mass,← he,mul_zero,mul_zero]; exact (h _).1 _
   rw [if_pos (hr i he j hi)]; unfold BudgetPoint.mass; rw [mul_comm (_ * f i),mul_left_comm (Real.exp _)]; apply mul_le_mul_of_nonneg_left _ (Poly.worth h₁ _).le; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) he.le
 next=> exact (h _).1 _
variable {w} (hb:0<κ)(hw:∀ i,0<w i) (h:Peak P o T (fun v=>Poly.toll w v) a A B)
include h hp hw hb
lemma budget [Nonempty Ω] : Nonempty (FullBudget P.p T w κ ((Real.exp 1+1)*A) (B / κ)) := by
 obtain ⟨x,hx,hX,hB⟩:=h.regular; obtain ⟨y,hy,hY,hc⟩:=h.captions; obtain ⟨f,hf,hF,hE,H⟩:=h.forced
 let W i:=Real.exp 1*x i
 refine ⟨⟨W,f,y,fun _=>0,h.active,hw,hb,fun i=>mul_nonneg (Real.exp_nonneg _) (hx i), fun i=> ⟨fun u z hv=> Extra.Multi.grain_of_sup (hX u i _ ?_)⟩,fun u i=>(h.active u).articles.regular i, hf, (fun u i j U=>hF u (i,j) U), hy,hY, fun _=>le_rfl, (fun y i=> by rw [h.units,norm_zero]),?_,?_⟩⟩
 · exact (congr_fun T.root z) ▸ ((h.active u).articles.pins i z hv) -- transport? elaborator
 · intro v
   -- need one Ω when proving pins.Tags can omit [Nonempty Ω] ??? current peak given x, if empty, produce witnesses zero and other hG maybe force/caption positive supports? tags can arbitrary. Require Nonempty Ω.
   refine ⟨Real.exp 1*A,A,?_,per_mark (o:=o) w hp hc hw hy (fun i _ j hh=> ?_) v,by ring_nf; rfl⟩
   · let u:Ω:= Classical.ofNonempty
     have he(v') : T.menu.origins v'=o v':=congr_fun T.root v'
     have hh:= budget_scale (Real.exp_pos 1).le
       (per_mark (o:=o) w hp hB hw hx (fun i _ j hh=> (he j) ▸ ((h.active u).articles.pins i j hh)) v)
     convert! hh using 1; ext i; split_ifs; unfold W BudgetPoint.mass; ring; rw [mul_zero]
   let u:Ω:=Classical.ofNonempty; exact (congr_fun T.root j) ▸ ((h.active u).captions.pins i j hh)
 intro v; rw [mul_div_cancel₀ B hb.ne'] -- lemma mul α κ isn't κ*B...
 exact per_mark (o:=o) w hp H hw hf (fun i=>hE i.1 i.2) v

variable {f:R.Mode→ℝ} -- price envelope f
set_option quotPrecheck false
local notation "W"=> (priceNormalized f T)
omit h hb hp hw
lemma weight_scaled (f:R.Mode→ℝ) (y:Ω)(i j) (h:(T.leaf y).Active) : KLaw P i ((priceNormalized f T).menu.force y i j) := by
 let g:=((↑((f (T.menu.marks i j))⁻¹):ℂ)); let z:=T.menu.force y i j; have hk:(priceNormalized f T).menu.force y i j=g•z:=rfl -- via ofReal_smul? test
 have he: KLaw P i z:= ⟨h.articles.inspects i j,h.articles.meas i j,h.articles.invi i j,h.articles.keeps i j⟩
 exact hk.symm ▸ he.smul g
variable (hv:∀ q,0<f q)
lemma scaling (ha:Peak P o T (exchange (fun v=> (f v)⁻¹) w) a A B)
    (hv:∀ q,0<f q) : Peak P o (W) (fun v=>Poly.toll w v) a A B:=by
 refine ⟨fun x=> ?_,fun x i=> ?_, ?_, ?_,?_⟩
 · let hp:= ha.active x; let v:=priceNormalized f T; have hT(j:ℕ): P.p.Regular (T.menu.branch j) (v.menu.regular x j):= regular_smul ((↑((f (T.menu.rays j))⁻¹):ℂ)) (hp.articles.regular j)
   let x0:= hp.articles
   refine ⟨⟨x0.proper,x0.pins,hT,x0.occurs, ?_,fun i j=>(weight_scaled (T:=T) f x i j hp).1, fun i j=>(weight_scaled (T:=T) f x i j hp).2.2.2,fun i j=>(weight_scaled (T:=T) f x i j hp).2.1,fun i j=>(weight_scaled (T:=T) f x i j hp).2.2.1⟩, ⟨hp.captions.card,hp.captions.pins⟩⟩
   intro i j hV y hy
   apply x0.retained i j ?_ y hy
   intro he; apply hV; funext U; change (f (T.menu.marks i j))⁻¹ • T.menu.force x i j U=0; rw [show T.menu.force x i j=0 from he, Pi.zero_apply,smul_zero]

 · change (f (R.fire i))⁻¹ • T.menu.global x i=_; rw [ha.units,smul_zero]
 · obtain ⟨g,hg,hG,ht⟩:= ha.regular; let F i:= (f (T.menu.rays i))⁻¹
   refine ⟨fun i=> F i * g i, fun i=> mul_nonneg (inv_pos.mpr (hv _) |>.le) (hg _),fun x i j hh=>?_,?_⟩
   · have he:= bound_smul (F i:ℂ) (hG x i j hh); rw [Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ F i from inv_nonneg.mpr (hv _|>.le))] at he; exact he
   convert! ht using 1; ext i; dsimp only; unfold F exchange; rw [mul_assoc]; rfl
 · obtain ⟨g,hg,hG,ht⟩:= ha.captions; let F i:= (f (T.tag i))⁻¹
   refine ⟨fun i=> F i*g i,fun i=> mul_nonneg (inv_pos.mpr (hv _) |>.le) (hg _), fun x i=>?_,?_⟩
   · let c:= F i; have hh:0 ≤ c:=inv_nonneg.mpr (hv _|>.le); change ‖c • T.score x i‖ ≤ _; rw [norm_smul, Real.norm_of_nonneg hh]; exact mul_le_mul_of_nonneg_left (hG _ _) hh
   convert! ht using 1; ext i; unfold F exchange; dsimp only; rw [mul_assoc]; rfl
 obtain ⟨g,hg,hG,ht,hH⟩:= ha.forced; let F(i:ℕ×ℕ):=(f (T.menu.marks i.1 i.2))⁻¹; have hd i : 0 ≤ F i:= inv_nonneg.mpr (hv _|>.le)
 refine ⟨fun i=> F i*g i,fun i=> mul_nonneg (hd _) (hg _),fun x i U=>?_,fun i j hv=> ht i j (pos_of_mul_pos_right hv (hd _)),?_⟩ -- pos_of?
 · change ‖F i • _‖≤_; rw [norm_smul, Real.norm_of_nonneg (hd i)]; exact mul_le_mul_of_nonneg_left (hG x i U) (hd i)
 convert! hH using 1; ext i; unfold F exchange; dsimp only; rw [mul_assoc]; rfl

include hv hp hb hw
lemma relative [Nonempty Ω] (ha: Peak P o T (exchange (fun v=> (f v)⁻¹) w) a A B)
    (h₁:f R.quiet=1) : Nonempty (RelativeBudget P.p T w κ f ((Real.exp 1+1)*A) (B/κ)) := ⟨hv,h₁, Classical.choice (budget hp hb hw (ha.scaling (P:=P) hv))⟩
end Peak
end YM.Qlocal.Publishing
