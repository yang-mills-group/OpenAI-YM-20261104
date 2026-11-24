import YM.QuadraticLocal.Display
import YM.QuadraticLocal.Germ.Solid
import YM.Integration.LocalComparisonDeclaredRetention
/-!
# `FullBudget` with manuscript independent test-norm signature (sup in all rows)

Outputs are Poses.E with exact amplitude even after pressure stamps, not reduced to one
response collation. Outside-unit ownership preserved. One copy of each polynomial forced
row in *that* vacuum. Needs Move only for its next.R lifecycle; covers empty label slots via
`RetainsDeclared`, not trying to fit a geometric extent into each unoccupied filler.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.QuadraticLocal.Display
open Function Filter Finset Lattice Wilson RG Ac Marker Overlay RG3 RG3.Held RG3.Forms Press
open Push.Corrected Push.AbsoluteSums MeasureTheory Extra.Trajectories Next.Foundations Push.Local
open RG3.Script.Picnic Integration.LocalComparison
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type}[DecidableEq V][Nonempty V]{R:Census V}{G:Gauge}{n:Side} {T:Type*}[Nonempty T]
variable {ι:Type*}[Countable ι]{P:Rep G n}{o:V→Site n} {w:V→ℝ}{q b c κ:ℝ}
local notation "Q"=> pin (α:=ι)
variable (A:Gallery T ι o P R)
open Affinity
namespace Focal
local notation "D₀" => Taste T o P R
local notation "L"=> Display.taste A
lemma gleam {X':Type*}[Nonempty X'] (f:X'→T) : Display.taste (readH A f) = Integration.LocalComparison.pullback f L:= rfl
-- unconditional forced at any i. Push.Pack.Shed. Tensor beyond.
variable (t:T) (U:Config G n)
local notation "Z"=> Article.Key ℕ R
local notation "Et"=> L
local notation "E₀"=> (taste A).leaf t
local notation "XA"=> (E₀).contents
local notation "CA"=> (E₀).captions
local notation "Pz"=> {i:R.Mode // i≠R.quiet}
local notation "Q!"=> pin (α:=Z)
lemma embossed (i:ℕ) : ((taste A).leaf t).contents.each i U=A.K.hard t i U:=by
   let t' := Bands.tagged XA i
   let e(x:Pz):ℕ:= Q! ((i,x) : Z)
   have he: Injective e:= by intro x y h; exact congr_arg Prod.snd (pin_injective h)
   have hh (j:Z) : t' (Q! j) U= if j.fst=i then Poly.send j.snd.val ((A.K.hard t i U).part j.snd.val) else 0:=by
       unfold t' Bands.tagged; change Poly.send (unpin (fun k: Z=> k.2.val) (R.fire _) (Q! j)) (unpin ((article A t).scored id i) 0 (Q! j) U)= _; rw [unpin_pin,unpin_pin]; unfold Article.scored; dsimp only [id_eq,article]; by_cases ht:j.fst=i; rw [if_pos ht,if_pos ht,ht]; rw [if_neg ht,if_neg ht,Poly.send_zero]
   have h0 (x) (h:x ∉ Set.range e): t' x U = 0:= by
      by_cases hx:x∈ Set.range Q!; obtain ⟨j,rfl⟩:=hx; rw [hh]; exact if_neg fun hp=> h ⟨j.2,congr_arg Q! (Prod.ext hp.symm rfl)⟩
      change Poly.send _ (unpin ((article A t).scored id i) 0 x U)=_; rw [unpin_blank ((article A t).scored id i) _ hx]; apply Poly.send_zero
   have ht : ∑' x,t' x U=A.K.hard t i U- Poly.send R.quiet ((A.K.hard t i U).part R.quiet):=by
      rw [← he.tsum_eq (f:=fun x=> t' x U) (fun i hi=> by_contra fun hn=> hi (h0 i hn)),tsum_congr (g:=fun j=>Poly.send j.val ((A.K.hard t i U).part j.val)) (fun a=> (?_ : t' (e a) U=_)),tsum_fintype,Article.record_sum]; unfold e; rw [hh,if_pos rfl]
   change Poly.send R.quiet _+_= _; rw [← A.K.quiet t,ht]; abel
-- same density for ANY summable log, since K column equality at all (other hypotheses usually incl gas summability)
variable [Fintype V]
lemma lit (h:Summable (fun i=>A.E.frame i t U)): ((L).leaf t).log U= A.E.log t U:=by
    let D:= Q
    let a i:= Bands.ray XA i U; let b i:= Poly.send ((CA).tag i) ((CA).value i)
    have hV i: a (D i)+b (D i)= A.E.frame i t U:= logE t U i
    have ht i : a (D i)=0 ∨ b (D i)=0:= by
      by_cases h:A.E.clear i
      · apply Or.inl; change Poly.send _ (masked _ _ (unpin (drawn A t) 0 (pin i)) U)=0; rw [unpin_pin]; simp [drawn,h,masked]
      exact Or.inr (show Poly.send _ (unpin (nomad A t) 0 (pin i))=0 from by rw [unpin_pin, nomad,if_neg h,Poly.send_zero])
    have he:= h.norm
    have h1 : Summable a:= pin_injective.summable_iff (g:= (pin (α:=ι))) (f:=a) (fun i hi=> (vacR t U hi).1)|>.mp ((he.of_nonneg_of_le (g:=fun i=> ‖a (D i)‖) (fun i=>norm_nonneg _) (fun i=>by rw [← hV]; rcases ht i with h|h <;> simp [h])).of_norm)
    have h2 : Summable b:= pin_injective.summable_iff (g:= (pin (α:=ι))) (f:=b) (fun i hi=> (vacR t U hi).2)|>.mp ((he.of_nonneg_of_le (g:=fun i=> ‖b (D i)‖) (fun i=>norm_nonneg _) (fun i=>by rw [← hV]; rcases ht i with h|h <;> simp [h])).of_norm)
    have hx : ∀ i,(XA).units i=0:= fun _=>rfl
    change (∑ i:V,Poly.send (R.fire i) ((XA).units i))+_+_= _; simp_rw [hx, Poly.send_zero]; rw [Finset.sum_const_zero,zero_add]; change (∑' i,a i)+(∑' i,b i)=_
    rw [← Summable.tsum_add h1 h2]; refine (Push.Corrected.Pad.sums D pin_injective (fun i=>A.E.frame i t U) (fun i=>a i+b i) hV (fun i hi=> ?_)).symm
    by_contra hx; obtain ⟨hr,hs⟩:= vacR (A:=A) t U hx; apply hi
    change a i + b i= 0; rw [show a i=0 from hr,show b i=0 from hs,zero_add]
lemma organized (h:∀ U,Summable (fun i=>A.E.frame i t U)): ((taste A).leaf t).density=A.density t:=by
   funext U; rw [RG3.Forms.Deck.density, Focal.lit A t U (h U)]; unfold QuadraticLocal.Gallery.density
   suffices he:Bands.cluster XA U=A.gas t U by rw [he]
   refine tsum_congr fun i=>?_ ; unfold Bands.packet Fusion.Attached.packet; split; simp only [embossed A t U]; rfl
end Focal
namespace Lens
open ComparisonDensity.Address
variable {α:Type}[Countable α](D: V→ ComparisonDensity.Address.Orbit)
-- use `full` def explicitly.Project.Lo.
instance witnesses : Nonempty (Integration.LocalComparison.TestSpace D):=inferInstanceAs (Nonempty (∀ v:V,(D v).Mood))
variable (M:Gallery (Affinity.Full (E:=fun v=>(D v).Mood)) α o P R)(X:V→Support n)(K:∀ v,Submodule ℂ (D v).Mood)
variable (h:Affinity.Adult X K M)
-- can use `coordinates` defeq TestSpace` via change`
local notation "L"=> Display.taste M
local notation "F"=> Affinity.Full (E:=fun v=>(D v).Mood)
def theater : Taste (TestSpace D) o P R:= L
local notation "D₁"=> theater D M
-- declare only rows with matching i, nonempty labels, all stencils. Needed even for garbage empty values; cap.
local notation "f"=> pin (α:=α)
local notation "F₀"=> Article.Key ℕ R
local notation "n₀"=> pin (α:=F₀)
def stands : Set (ℕ×ℕ):= { s| ∃ j:Article.Key ℕ R, n₀ j=s.snd ∧ j.fst=s.fst ∧ (∀ v∈ ((D₁).menu.marks s.fst s.snd).val, X v⊆ (P.activities.forced s.fst).support)}
private lemma flow i j (t:F) : (D₁).menu.force t i j= ((article M t).impression ((view M).terms t) id).entries i j:=rfl
private lemma marks (i j:ℕ)(t:F): (D₁).menu.marks i j= ((article M t).impression ((view M).terms t) id).marks i j:=rfl
include h
lemma retention (he:∀ v,o v∈ X v): RetainsDeclared (stands D M X) D₁ X:= by
    refine ⟨he,?_, ?_, ?_,?_⟩
    · intro i v hw; change v∈ (unpin _ (R.fire _) i).val at hw; change X v⊆ unpin (Display.focus M) univ i;
      by_cases he:i∈ Set.range f; obtain ⟨j,rfl⟩:=he; rw [unpin_pin] at hw ⊢; exact h.house j v hw
      rw [unpin_blank _ _ he]; exact subset_univ _
    · rintro i j ⟨u,hv,he,hH⟩ v hv; exact hH _ hv
    · intro i j hv t; rw [flow D M i j t]; by_cases hp:j∈ Set.range n₀; swap; · rw [Article.scored_blank _ _ _ _ _ hp]
      obtain ⟨u,rfl⟩:=hp; rw [Article.scored_pin]; funext U; unfold Article.scored; split; swap; · rfl
      next hu=>
        change (M.K.hard t _ U).part u.snd.val=_; by_contra hn; apply hv; refine ⟨u,rfl,hu,?_⟩; rw [marks D M _ _ t, Article.marked_pin,← show u.fst=i from hu]; exact h.stalk _ _ _ t hn
    intro i v hv; change v∈ (unpin _ (R.fire _) i).val at hv; change X v⊆ unpin (Display.focus M) univ i; by_cases he:i∈ Set.range f
    · obtain ⟨j,rfl⟩:=he; rw [unpin_pin] at hv ⊢; exact h.house _ _ hv
    rw [unpin_blank _ _ he]; exact subset_univ _

lemma print : Integration.LocalComparison.Multilinear D D₁:=by
    let k:= K; let t:F:= Classical.arbitrary F; constructor
    · intro i U; change Letter ℂ _ (unpin _ (R.fire _) i).val (fun t=> unpin (Display.drawn M t) _ i U); by_cases he:i∈ Set.range f
      · obtain ⟨j,rfl⟩:=he; rw [unpin_pin]; simp_rw [unpin_pin]; unfold Display.drawn; split; exact Letter.still; exact (h.regular j U).full
      simp_rw [unpin_blank _ _ he]; exact Letter.still
    · intro i j U; simp_rw [flow D M i j,marks D M _ _ t]; by_cases he:j∈ Set.range n₀; obtain ⟨u,rfl⟩:=he; simp_rw [Article.scored_pin,Article.marked_pin]; unfold Article.scored; split; exact (h.hard ..).full; exact Letter.still
      simp_rw [fun t:F=> Article.scored_blank (article M t) ((view M).terms t) id i j he]; exact Letter.still
    · exact fun i=> Letter.still
    intro i; change Letter ℂ _ (unpin _ (R.fire _) i).val (fun t=> unpin (Display.nomad M t) _ i); by_cases he:i∈ Set.range f
    · obtain ⟨j,rfl⟩:=he; simp_rw [unpin_pin]; unfold Display.nomad; split; exact (h.regular ..).full; exact Letter.still
    simp_rw [unpin_blank _ _ he]; exact Letter.still
omit h
-- Independent choice. `neighborhood` not assumed independent across v.Prec declared before. compatibility no hidden identifications.
def portion (i: V): Set ((D i).Mood):= {x|(D i).Bill x.val 1}
def affine (x:IndependentTests D): Wallet (portion D):=fun i=> ⟨ testInclusion D x i, (x i).prop⟩
instance : Nonempty (IndependentTests D):= ⟨fun i=> ⟨0,Orbit.Bill.zero.more zero_le_one⟩⟩
instance : Nonempty (Affinity.Wallet (portion D)):= ⟨affine D (Classical.arbitrary _)⟩
def cost (i:V)(x:(D i).Mood):ℝ:= if x∈portion D i then 1 else ( (D i).admits x).choose+1
omit [Countable ι] [Nonempty V] [DecidableEq V] in -- nonempty V omit countable α?
lemma cost_pos (i:V)(x:(D i).Mood): 0< cost D i x:=by unfold cost; split; exact zero_lt_one; exact add_pos_of_nonneg_of_pos (((D i).admits x).choose_spec.nonneg) zero_lt_one
-- choose simple Spring over positions
-- instance for ℝ Module choose complexToReal of submodule? check.
def adopts : Affinity.Spring ℝ (portion D) where
    rate:=cost D
    nonzero i x := (cost_pos ..).ne'
    level i x h:= if_pos h
    accepts i x:= by
       rw [← Complex.coe_smul]; change (D i).Bill _ 1; unfold cost; split
       next h=>simpa only [_root_.inv_one,Complex.ofReal_one,one_smul] using (show (D i).Bill _ 1 from h)
       next h=>
          let e:= ((D i).admits x).choose; have he : 0 ≤ e:= ((D i).admits x).choose_spec.nonneg
          have hz:= ((D i).admits x).choose_spec.smul (↑((e+1)⁻¹)); refine Orbit.Bill.more hz ?_; rw [Complex.norm_real,Real.norm_of_nonneg (by positivity), ←div_eq_inv_mul]; exact (div_le_one (by linarith)).2 (by linarith only [he])
lemma spin : ∀ i:V, Set.MapsTo (fun t:(D i).Mood=> Complex.I • t) (portion D i) (portion D i):=fun i x hx=> by
    change (D i).Bill _ 1 at hx ⊢; convert hx.smul Complex.I <;> simp [Complex.norm_I]
-- beyond as well. all tests; don't use bigger radius. 
def pullCost {X Y:Type*} {Mb:Taste X o P R} {w:V→ℝ}{p:BudgetPoint}{κ A B:ℝ}(Y': Y→X)(h:FullBudget p Mb w κ A B): FullBudget p (Integration.LocalComparison.pullback Y' Mb) w κ A B:= { h with
   active:=fun t=>h.active (Y' t), regular:= fun i=> ⟨fun x=> (h.regular i).controls (Y' x)⟩, regular_law:=fun x=> h.regular_law (Y' x), forced:=fun x=> h.forced (Y' x), caption:=fun x=> h.caption (Y' x), unit:= fun x=>h.unit (Y' x) }
lemma supplies (h: Nonempty (FullBudget P.p (taste (readH M (readBack (portion D)))) w κ b c)): Nonempty (FullBudget P.p (Integration.LocalComparison.pullback (testInclusion D) D₁) w κ b c):=by
   obtain ⟨H⟩:=h; exact ⟨ Lens.pullCost (affine D) H ⟩
end Lens
end YM.QuadraticLocal.Display
