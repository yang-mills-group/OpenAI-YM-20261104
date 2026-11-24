import YM.Qlocal.Ledger
/-!
A genuine regular LOG and forced joint representation now read into the
full marker algebra layout. Gives the output toll bound relative to any labels'
markers separately. Includes packed products of modes, factors at non-typical
or *zero* test values; ears.S. full. Need marry realization back to
raw input Canon (next files).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Publishing
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ:ℝ}
open Merge Switch UniformPays

abbrev speech (q:R.Mode) (U:Support n) (s: V→Support n): Prop:= ∀ i∈q.val,s i⊆U

def lives (Z:Poly R) (U:Support n) (s:V→Support n): Prop:= ∀ q, Z.part q ≠0→ speech q U s

def priceQ (z:Poly R) (c:R.Mode→ℝ):ℝ:=∑ i: R.Mode,c i*‖z.part i‖ -- weight may include tropical/zero at quiet etc

structure Syntax (Z:ι→Poly R) (s:V→Support n)(e:ι→Support n): Prop where
  proper i : (Z i).part R.quiet=0
  mental i : lives (Z i) (e i) s
  repeated i : Z i* Z i=0

-- probability/even quirks: as written `mental i` gives lives for own support. A T(product) lives on X if every e_i ⊆ X. no enlargement
lemma LivesOne (U:Support n)(s:V→Support n) : lives (1:Poly R) U s:=by
 intro q h; have ht:q=R.quiet:= Classical.byContradiction (fun ht=>h (by simp only [Poly.one_part,if_neg ht])); simp only [ht]; intro k; exact fun hh=> False.elim (Finset.notMem_empty k hh)
lemma lives.one {z:Poly R}{Y:Support n} (h : lives z X s) (he:X⊆Y):lives z Y s := fun i hi k hk=> (h i hi k hk).trans he
lemma lives_times {z y:Poly R}(h:lives z X s)(hu:lives y X s): lives (z*y) X s:=by
 intro q hV j hj
 rw [Poly.part_mul] at hV; obtain ⟨i,-,hi⟩:= exists_ne_zero_of_sum_ne_zero hV; obtain ⟨k,-,hk⟩:= exists_ne_zero_of_sum_ne_zero hi
 split at hk; swap; · simp at hk
 rename_i ho; rcases Finset.mem_union.mp (show j∈ _ from ho.2.symm ▸ hj) with he|he
 · exact h i (left_ne_zero_of_mul hk) _ he
 exact hu k (right_ne_zero_of_mul hk) _ he
lemma lives_many (S:Finset ι) (z:ι→Poly R) (h:∀ i∈S, lives (z i) X s) : lives (∏ i∈S,z i) X s:=by
 induction S using Finset.induction with
 | empty => rw [Finset.prod_empty]; exact LivesOne X s
 | insert i S hi hS => rw [Finset.prod_insert hi]; exact lives_times (h _ (by simp)) (hS fun i hi=>h _ (mem_insert_of_mem hi))
-- Can code tickets for marks ℂ. retain relative any cap on priceQ, at w (maybe bigger after truncating any prescribed modes). No positivity cap assumed at entry but preserve symbols even if erased.

variable {Z:ι→Poly R} {e:ι→Support n} (h:Syntax Z s e) (hO:∀ i,o i∈s i)
variable [Fintype ι]

include h
omit [Fintype ι] in
lemma syntax_one (t:Finset ι)(hn:t.Nonempty) : (∏ i∈t,Z i).part R.quiet=0:= by
 rw [MergeProof.Accent.shockProd₀]; obtain ⟨s,hS⟩:=hn; exact Finset.prod_eq_zero hS (h.proper _)
-- clean

variable {K: WayK Ω ι G n}
variable {L:Ω→J→ Config G n→ Ways ι}
variable (P) (V' : Spectrum Ω ι G n J)
variable (hr: V'.Reads P.p L) (hx:V'.Costs P.p e a A)(hK : UniformPays P.activities P.p K B d)
    (he:∀ x i u, u∈e i → Merge.Motion.Hush i u (fun j=>(P.activities.forced j).support) (K x))
set_option quotPrecheck false
local notation "p"=> P.p

-- force first.
variable (Z K) in
def script : Ledger Ω J G n R where
  region := V'.region
  raw x j U := (↑(V'.raw x j U):ℂ) • ∏ i∈ V'.tag j,Z i
  total := V'.total
  forced x i U := sound Z (fun t s=> K x t s i U)
-- order arguments?
local notation "S'"=> script Z K V'
local notation "A₀"=> P.activities
local notation "UH!"=> UniformPays P.activities P.p K B d
local notation "partK"=> (S').forced
abbrev zProd (U:Finset ι) := ∏ i∈U, Z i
private abbrev Wk (i:ℕ)(u:Ω)(q:R.Mode)(t:Finset ι): Config G n→ℂ := (zProd (Z:=Z) t|>.part q) • (Complex.ofReal ∘ (fun U=>amount K u i U t))
omit h in
private lemma f_many (x:Ω)(i:ℕ) (z:R.Mode) (U:Config G n): (partK x i U).part z= ∑ t:Finset ι,Wk (K:=K) (Z:=Z) i x z t U:= by
 unfold script Switch.sound; dsimp only [mapScores_apply]; rw [Poly.part_sum]; refine sum_congr rfl fun j _=>?_ ; rw [Poly.part_smul]; exact mul_comm .. -- `unfold` macro invalid
include h hr hx hO hK he
set_option maxHeartbeats 1000000
lemma weighs : Ethics P o s (S'):=by
 obtain ⟨f,hF,hV⟩:= hK.keeps e he; refine ⟨hO,hx.locations,?_,?_,?_,?_,?_,?_⟩
 · intro x i U hi; dsimp only [script]; rw [hr.constant i hi x U]
 · intro x i U; change ( (↑(V'.raw x i U) : ℂ) • _ : Poly R).part _=_; rw [Poly.part_smul]; rcases eq_empty_or_nonempty (V'.tag i) with hi|hi
   · rw [hr.quiet i hi x]; simp
   rw [syntax_one h _ hi]; rw [mul_zero]
 · intro x i q U hp j hj; unfold script at hp; dsimp only [Poly.part_smul] at hp; let H j (he:j∈V'.tag i):lives (Z j) (V'.region i) s:= (h.mental _).one (hx.owned _ _ he)
   exact lives_many (V'.tag i) Z H q (right_ne_zero_of_mul (show _≠0 from hp)) j hj
 · intro x i q; rw [show (fun U=>(partK x i U).part q)=(∑ k,Wk (K:=K) (Z:=Z) i x q k) from funext fun U=> (f_many V' x i q U).trans (Finset.sum_apply ..).symm]; refine KLaw.sum _ (fun t H=>?_); obtain ⟨v,m,hG,hZ,-⟩:= (hV i t).2 x
   exact KLaw.smul (f:=Complex.ofReal ∘ (fun U=>amount K x i U t)) (⟨fun u w hx hv=> congr_arg Complex.ofReal (v u w hx hv), Complex.continuous_ofReal.measurable.comp m, fun _ _=>congr_arg Complex.ofReal (hG _ _),fun U hu=> (hZ U).2 (Complex.ofReal_ne_zero.mp hu)⟩) _
 · intro x i U q H u hu; rw [f_many] at H
   obtain ⟨z,-,hz⟩:= exists_ne_zero_of_sum_ne_zero H; have ht(j)(hj:j∈z):e j ⊆ (P.activities.forced i).support:= by
     rcases (hV i z|>.2 x).2.2.2.2 j hj with ht|ht; exact ht
     apply False.elim (hz ?_); unfold Wk at *; rw [show (fun U : Config G n=>amount K x i U z)=0 from ht]; simp
   exact lives_many z Z (fun j hj=> (h.mental _).one (ht j hj)) _ (left_ne_zero_of_mul hz) u hu
 intro x i U; rw [f_many, Finset.sum_eq_single ∅]; rotate_left
 · intro j _ hj; unfold Wk; dsimp only [zProd]; rw [Pi.smul_apply,smul_eq_mul,syntax_one h _ (nonempty_iff_ne_empty.mpr hj)]; rw [zero_mul]
 · simp
 unfold Wk zProd; rw [Pi.smul_apply,smul_eq_mul,Function.comp_apply, hK.quiet]; simp

variable (hg:∀ x,0≤ c x) (hC:∀ U:Finset ι, priceQ (zProd (Z:=Z) U) c ≤ C)
omit hr hO
include hg hC
omit h hK he in
lemma levels_regular : ∃ f:J×R.Mode→ℝ,(∀ i,0≤ f i)∧ (∀ i: J,∀ j:R.Mode, ∀ x:Ω, let g(U:Config G n):=((S').raw x i U).part j; P.p.Regular ((S').region i) g ∧ ∀ z∈(S').region i,P.p.supBounds z ((S').region i) g (f (i,j)))∧
     Ac.Hit (S').region P.p.B (Tons c f) a (C*A):= by
 obtain ⟨f,hF,hV⟩:= hx.rent.majorize; let y(i:J×R.Mode):=‖(zProd (Z:=Z) (V'.tag i.1)).part i.2‖* f i.1; have hp i: 0≤ y i:=mul_nonneg (norm_nonneg _) (hF i.1|>.1); have he':0≤C:= (sum_nonneg (fun i (_:i∈(univ:Finset R.Mode))=> mul_nonneg (hg i) (norm_nonneg _))).trans (hC ∅)
 refine ⟨y,hp,fun i j x=>?_,fun j=>budget_mono (budget_scale he' (hV j)) (fun i=>?_) (fun i=>?_)⟩ -- keys projection
 · intro g; have hU : g=((zProd (Z:=Z) (V'.tag i)).part j) • (Complex.ofReal ∘ V'.raw x i):= by ext1 U; exact mul_comm .. -- change
   rw [hU]; exact ⟨regular_smul _ (ornate ((hF i|>.2 x).1)),fun z hz=> bound_smul _ (Blush.pricingG ((hF i|>.2 x).1) ((hF i|>.2 x).2 z hz))⟩
 · split; exact mul_nonneg (sum_nonneg fun i _=> mul_nonneg (hg i) (hp _)) (Real.exp_nonneg _); exact le_rfl
 split
 next hi=> dsimp only [script,Tons]; rw [if_pos (show j∈ V'.region i from hi),←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _); unfold y; dsimp only; simp_rw [← mul_assoc,← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hC _) (hF _|>.1)
 next hi=> rw [if_neg (show j∉ V'.region i from hi),mul_zero]

include hr hO -- use ethics.supports for post shrink (could drop after)
lemma levels_hard : ∃ f:ℕ×R.Mode→ℝ,(∀ i,0≤ f i)∧ (∀ i:ℕ,∀ j: R.Mode,(∃ v∈j.val, ¬s v⊆(P.activities.forced i).support)→ f (i,j)=0) ∧ (∀ (x:Ω) i V j, ‖(partK x i V).part j‖≤f (i,j))∧
            Ac.Hit (fun i=>(P.activities.forced i).support) P.p.B (Tons c f) d (C*B):= by
 obtain ⟨f,hF,hV⟩:= hK.keeps e he;
 let p' (i:ℕ)(q:R.Mode)(j:Finset ι):= ‖(zProd (Z:=Z) j).part q‖* f (i,j)
 have hC' : 0 ≤ C:= (sum_nonneg (fun i (_:i∈(univ:Finset R.Mode))=> mul_nonneg (hg i) (norm_nonneg _))).trans (hC ∅)
 have hf i j t : 0≤ p' i j t:= mul_nonneg (norm_nonneg _) (hV i t|>.1); let f'(i:ℕ×R.Mode):= ∑ j:Finset ι,p' i.1 i.2 j; let β(i:ℕ×R.Mode):=if speech i.2 (P.activities.forced i.1).support s then f' i else 0; have hv i : 0 ≤ β i:= by unfold β; split; exact sum_nonneg fun j _=> hf _ _ _; rfl
 refine ⟨β,hv,?_,?_,fun i=>?_⟩
 · intro i j; rintro ⟨v,h,H⟩; exact if_neg (fun hv=> H (hv _ h))
 · intro x i y j; unfold β; split; next hx=>
     rw [f_many]; apply (norm_sum_le _ _).trans; refine Finset.sum_le_sum fun z _=>?_ ; unfold Wk p'; dsimp only; rw [Pi.smul_apply,Function.comp_apply,norm_smul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left ((hV i z|>.2 x).2.2.2.1 _|>.1) (norm_nonneg _)
   next hh=> rw [not_ne_iff.mp (mt ((weighs (s:=s) P h hO V' hr hx hK he).hosts x i y j) hh),norm_zero]
 let b(i':ℕ×Finset ι):= if i∈(P.activities.forced i'.1).support then f i'*Real.exp (d*coverNumber P.p.B (P.activities.forced i'.1).support) else 0
 have hSa:SumBudget b B:= hF i
 have hg' : SumBudget (fun i:ℕ=>∑ j : Finset ι,b (i,j)) B:= by
    rw [show (fun i:ℕ=> ∑ j: Finset ι,b (i,j))=(fun i=> ∑' j,b (i,j)) from funext fun i=>(tsum_fintype ..).symm]; refine ⟨fun i=>tsum_nonneg (fun j=>hSa.1 _), ?_, hSa.2.1.tsum_prod.symm.trans_le hSa.2.2⟩; exact ((summable_prod_of_nonneg hSa.1).1 hSa.2.1).2
 refine budget_mono (budget_scale hC' hg') (fun i=>?_) (fun z=>?_)
 · split; exact mul_nonneg (sum_nonneg fun i _=> mul_nonneg (hg i) (hv _)) (Real.exp_nonneg _); rfl
 split
 next hi=>
   unfold b; simp_rw [if_pos (show i∈_ from hi),← Finset.sum_mul,←mul_assoc]; refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _); unfold Tons
   apply le_trans (b:=∑ i':R.Mode,c i' * f' (z,i')) (sum_le_sum (?_)); rotate_left
   · intro a _; exact mul_le_mul_of_nonneg_left (show β _ ≤ _ from by unfold β; split; rfl; exact sum_nonneg (fun i _=>hf _ _ _)) (hg _)
   unfold f'; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_le_sum; intro i hi; unfold p'; simp_rw [← mul_assoc]; rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (hC i) (hV _ _|>.1)
 next => exact (budget_scale hC' hg').1 _

-- depression z≥P.sup
lemma levels (hp : a=d) : Bulk P s (S') c d (C*A) (C*B):=by rw [← hp]; constructor; exact levels_regular P V' hx hg hC; rw [hp]; exact levels_hard P h hO V' hr hx hK he hg hC
end YM.Qlocal.Publishing
