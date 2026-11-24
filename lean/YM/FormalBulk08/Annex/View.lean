import YM.FormalBulk08.Annex.Rits

/-! Map supports, est C^D norms on exactly centered cube.
Purchases apply independent D-of profiles over cover. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Annex
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type}{G:Gauge}{n: Side}{r t j k u l e E D:ℕ}{A B C σ η:ℝ}{o:Loc G 1}
open Spigot Pose
variable {K:KernelChoices}{W:Dove.Lab G K I}
open Precision Rial Dove Dove.Lab Next.Free Quire Labels Source Drops Elm Roof Drift
variable (F:Frame G r)(T:SectionData F)
lemma moves (ρ:ChartRatio G)(a:hue G)(_W:Dove.Lab G K I)(X:Flight j t)(V: Lodge X.patch)(Q:Pot G)(Y:Anthem D G)(p:X.patch.Branches K G)(hL:2≤ X.L.val)(d l:ℕ)
   (h:∀ x y,compress D x=compress D y→ Y x=Y y)(x y)(hp:compress D x=compress D y): migrates a X V K Q ρ p hL d l Y x=migrates a X V K Q ρ p hL d l Y y:= by
    unfold migrates stir; suffices h':quick X V Q Y ρ p hL d l x=quick X V Q Y ρ p hL d l y from by rw [h']
    unfold quick; apply congr_arg; apply Finset.sum_congr rfl; intro i _; unfold stepsong Kemp.work; rw [h _ _ (pen_keeps X.odd hL i x y hp)]
lemma encloses (ρ:ChartRatio G)(W:Dove.Lab G K I)(a:hue G)(hd:r+1≤D)(i:I)(m n)(p:Letter F)(x y:Studio D)(h:compress D x=compress D y):bornY ρ W a F T hd i m n p x=bornY ρ W a F T hd i m n p y:= by
   unfold bornY Elm.terrace; generalize m-n=j; induction j generalizing x y n p with
   | zero=>rw [walkF]; unfold sectionY; rw [notch_holds _ h]
   | succ j ih=>
     rw [walkF]; unfold avenue larch; simp only [Finset.sum_apply,Kemp.launch]; apply Finset.sum_congr rfl; intro i hi; apply congr_arg; exact moves _ _ W _ _ _ _ _ _ _ _ (fun x y p=> ih _ _ _ _ p) _ _ h
lemma entrains (ρ:ChartRatio G)(W:Dove.Lab G K I)(a:hue G)(hd:r+1≤D) (i:I)(m)(p:Letter F)(x y:Studio D)(h:compress D x=compress D y): issue W ρ a F T hd i m p x=issue W ρ a F T hd i m p y:= by unfold Drift.issue; funext i k;simp_rw [encloses F T ρ W a hd _ _ _ _ x y h]
variable {F T}{ρ:ChartRatio G}{H: Hol G}(q:Quota F H W o D E l)(p:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:r≤l)
include q p h a hs ht hb hr
open Aster
lemma settles (i:Letter F): ∃ C:Leaf W.scrolls→ℝ,Soft (chron _) C∧ ∀ x:Leaf W.scrolls,∀ X:Studio D,∀ e≤ E,∀ k,
    Knoxville (fame _) (W.windowD x) (0,o) (issue W ρ a F T q.horizon x.a x.b i X e k) (C x*‖compress D X‖) ∧ ∀ N,x.b≤ N → Knoxville (fame _) (W.windowD x) (0,o) (bornY ρ W a F T q.horizon x.a N x.b i X e k) (C x*‖compress D X‖) ∧ Knoxville (fame _) (W.windowD x) (0,o) (bornY ρ W a F T q.horizon x.a N x.b i X e k-issue W ρ a F T q.horizon x.a x.b i X e k) (C x*fare_n x N*‖compress D X‖):= by
   obtain ⟨B,b,J⟩:= supported D; obtain ⟨C,c,Q⟩:= timber q p h a hs ht hb hr i; refine ⟨fun i=>C i*B,c.times (soft_coin _ B),fun x f i' hi k=>?_⟩; obtain ⟨g,e,H⟩:= J f; have hh: 0 ≤ C x:= (Q x).1.height; have hx: C x*‖g‖≤ C x*B*‖compress D f‖:= (mul_le_mul_of_nonneg_left H hh).trans_eq (mul_assoc ..).symm;have hz:=congr_fun (sliced (T:=issue W ρ a F T q.horizon x.a x.b i) hi g) k
   refine ⟨?_,fun N v=> ?_⟩
   · rw [entrains F T ρ W a q.horizon x.a x.b i _ _ e,←hz]; exact ((Q x).1.precincts i' hi k g).mono hx
   rw [encloses F T ρ W a _ _ _ _ _ f g e,entrains F T ρ W a _ _ _ _ f g e,← hz]; refine ⟨((Q x).2 N v |>.1.precincts i' hi k g |>.mono hx),(((Q x).2 N v).2.precincts i' hi k g).mono ?_⟩; rw [mul_right_comm (C x),mul_right_comm (C x*B)]; exact mul_le_mul_of_nonneg_right hx (ratioR_pos ..).le
lemma routed (i:Letter F)(n:ℕ)(Q:Herald)(hx:VividC n o E D (Pose.slots F i) W Q):∃ C:Leaf W.scrolls→ℝ,Soft (chron _) C ∧ ∀ x:Leaf W.scrolls,
    let G:= sliceM (Drift.issue W ρ a F T q.horizon x.a x.b i) E; let s:=Pose.slots F i; let w:=min (inkGate o s n E D Q (W.windowD x)) 1
    0<w ∧ (∃ M,Litany Q o M s n E 0 (E+1) w (C x) G ∧ ∀ a∈M,Brooted a) ∧ ∀ N,x.b≤N→let V:= bornY ρ W a F T q.horizon x.a N x.b i;∃ M P,Litany Q o M s n E 0 (E+1) w (C x) V ∧ Litany Q o P s n E 0 (E+1) w (C x*fare_n x N) (V-G) ∧ (∀ a∈ M,Brooted a) ∧ ∀ a∈ P,Brooted a:= by
   obtain ⟨C,c,H⟩:= presented q p h a hs ht hb hr i n Q hx
   obtain ⟨B,b,P⟩:= author (G:=G) D n
   refine ⟨_,(soft_coin _ B).times c,fun x=>?_⟩; intro Z s w; obtain ⟨he,⟨M,m⟩,X⟩:=H x;have hw: 0 < w:= lt_min he zero_lt_one
   have he(x' y:Studio D)(hx:compress D x'=compress D y):Z x'=Z y:=congr_arg (fun p=> stopper p E) (entrains F T ρ W a _ _ _ i _ _ hx)
   have hz:w≤1:=min_le_right ..; refine ⟨hw,P _ _ Z _ _ s _ _ _ hw.le hz he M (lit_mono m (min_le_left ..) le_rfl),fun N hn=> ?_ ⟩; intro V; obtain ⟨R,S,r,s'⟩:=X N hn
   have ht x' y (h:compress D x'=compress D y): V x'=V y:= encloses F T ρ W a _ _ _ _ _ _ _ h
   obtain ⟨A,u,Q₀⟩:=P _ _ V _ _ _ _ _ _ hw.le hz ht R (lit_mono r (min_le_left ..) le_rfl)
   obtain ⟨B₁,v,Q₁⟩:= P _ _ (V-Z) _ _ _ _ _ _ hw.le hz (fun x' y h=>congr_arg₂ (·-·) (ht _ _ h) (he _ _ h)) S (lit_mono s' (min_le_left ..) le_rfl); exact ⟨A,B₁,u,mul_assoc B (C x) (fare_n x N) ▸ v,Q₀,Q₁⟩
end YM.FormalBulk08.Annex
