import YM.OPE.Beams.Penny
/-!
# Common footage
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G} {F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype Z][DecidableEq Z]{f:Filter L}
    {x:L→ (I→ E4)→ J→ E4}{T:L→ℝ}{a b d:ℝ}{v:I}{j k:J}
    {y:L→ (I→ E4)→ Z→ E4}
variable (ht:Tendsto T f atTop)
local notation "X'"=> (I→ E4)
variable {w:L→ I→ J→ ℝ}{z:L→ I→ Z→ℝ}
structure Slender (f:Filter L)(T:L→ℝ)(x:L→ (I→ E4)→ J→ E4)(w:L→I→J→ℝ) : Prop extends Film f T x w where
    speed i j:Tendsto (fun a=> w a i j) f (𝓝 0)
    narrows j : ∀ k:ℝ,0 < k→ ∀ᶠ i in f, ∀ z:I→ E4,‖z‖≤1 → ‖x i z j‖ ≤ k
-- general joining
variable (h:Film f T x w)(h':Film f T y z)(S':Slender f T x w)(B:Slender f T y z)
private def guard (x:L→ (I→ E4)→ J→ E4) (y:L→ (I→ E4)→ Z→ E4)(p:L→ I→J→ℝ)(q:L→I→Z→ℝ)(f:Filter L)(T:L→ℝ) := ∀ (a:I)(j:J)(k:Z),∀ t>0,∀ᶠ i in f,∀ u:I→ E4,‖u‖≤1→ |p i a j-q i a k|+jacket (T i)≤ t*‖x i u j-y i u k‖
include h h'
lemma Film.join (he:∀ a j k,∀ t>0,∀ᶠ i in f,∀ u:I→ E4,‖u‖ ≤ 1→ |w i a j-z i a k|+jacket (T i)≤t*‖x i u j-y i u k‖):Film f T (fun i u=> beside (x i u) (y i u)) (fun i u=> beside (w i u) (z i u)):=by
    refine ⟨fun i=>?_ ,fun i u k a t=>?_,?_⟩; · apply differentiable_pi.mpr; intro j; cases j; exact (differentiable_pi.mp (h.unfolds i)) _; exact (differentiable_pi.mp (h'.unfolds i)) _
    · rw [h.constant i u k a t,h'.constant i u k a t]; funext j; cases j<;>rfl
    rintro a (j|j) (k|k) hv t hx; exact h.opens _ j k (fun he=> hv (congr_arg Sum.inl he)) _ hx; exact he a j k t hx
    · filter_upwards [he a k j t hx] with i hi u hu; change |z i a j-w i a k|+_ ≤t*‖y i u j-x i u k‖; rw [norm_sub_rev,abs_sub_comm]; exact hi u hu
    exact h'.opens _ j k (fun he=> hv (congr_arg Sum.inr he)) _ hx
omit h h'
include S' B
lemma Slender.join (he:∀ a j k,∀ t>0,∀ᶠ i in f,∀ u:I→ E4,‖u‖ ≤ 1→|w i a j-z i a k|+jacket (T i)≤ t*‖x i u j-y i u k‖): Slender f T (fun i u=>beside (x i u) (y i u)) (fun i u=> beside (w i u) (z i u)):= ⟨S'.toFilm.join B.toFilm he,fun a k=>by cases k; exact S'.speed ..; exact B.speed .., fun j k hx=>by cases j; exact S'.narrows _ k hx; exact B.narrows _ k hx⟩
omit S' B
local notation "E!"=> (fun (_:L) (_:X') (_:Unit)=> (0:E4))
lemma Slender.empty : Slender f T (E!) 0:= ⟨⟨fun i=>differentiable_const _,fun _ _ _ _ _=>by funext; simp [along],fun _ _ _ h=> (h (Subsingleton.elim ..)).elim⟩,fun _ _=> tendsto_const_nhds,fun j a ha=> Eventually.of_forall (fun _ _ _=> le_of_lt (by simp [ha]))⟩ -- Y implicits infer
include S'
lemma Slender.relabel (s:Z→J)(hp: Injective s): Slender f T (fun i u=> x i u ∘ s) (fun i u=> w i u ∘ s) := by
    refine ⟨⟨fun i=> differentiable_pi.mpr fun j=> ?_,fun i u k a t=> ?_,fun a j k he=>S'.opens a (s j) (s k) (hp.ne he)⟩,fun i j=> S'.speed i (s j),fun j=>S'.narrows (s j)⟩; exact differentiable_pi.mp (S'.unfolds i) (s j)
    rw [S'.constant i u k a t]; rfl
lemma Slender.away {y:L→ E4}(he:Tendsto (fun i=> ‖y i‖) f (𝓝 0)): Slender f T (fun i z=> OPE.away (x i z) (y i)) w:=by
    refine ⟨⟨fun i=> differentiable_pi.mpr fun j=>?_,fun i u k a t=>?_,fun a j k hj z hv=>?_⟩, S'.speed,fun j t ht=>?_⟩
    · exact (differentiable_pi.mp (S'.unfolds i) j).sub_const (y i)
    · rw [S'.constant i u k a t]; funext j; unfold OPE.away along; abel_nf; ac_rfl
    · simp_rw [OPE.away, sub_sub_sub_cancel_right]; exact S'.opens a j k hj z hv
    filter_upwards [S'.narrows j _ (half_pos ht), he.eventually (ge_mem_nhds (half_pos ht))] with i hi hp z hz; unfold OPE.away; linarith only [norm_sub_le (x i z j) (y i), hp, hi z hz]

include ht
lemma Slender.addOn (z: Z → E4)(he:Injective (beside (sole (0:E4)) z)): Film f T (fun i u=> beside (x i u) z) (fun i u=> beside (w i u) (fun _:Z=> (0:ℝ))) :=by
    obtain ⟨he,hZ,hh⟩:= beside_distinct.mp he; let I': L→ X'→ Z→ E4:=fun _ _=> z; let v: L→ I→ Z→ℝ:=0; have hf: Tendsto (fun i=> jacket (T i)) f (𝓝 0):= (jacket_price ht).tends (by norm_num) ht
    apply Film.join S'.toFilm (z:=v) (y:=I') ?_
    · intro a j k t H; let u:= ‖z k‖; have he:0<u:=norm_pos_iff.mpr (show z k ≠ 0 from Ne.symm (hh () k)); let y':= u/2; have hx: 0 < y':= half_pos he
      filter_upwards [S'.narrows j y' hx, ((S'.speed a j).norm.add hf).eventually (ge_mem_nhds (show ‖(0:ℝ)‖+0<t*y' from (by rw [norm_zero,zero_add]; exact mul_pos H hx)))] with i hi ht u' hu; change |w i a j-0|+_ ≤ _; rw [sub_zero]; refine ht.trans (mul_le_mul_of_nonneg_left ?_ H.le); unfold y' u I'; linarith only [show ‖x i u' j‖ ≤ ‖z k‖/2 from hi u' hu,norm_sub_norm_le (z k) (x i u' j), norm_sub_rev (z k) (x i u' j)]
    refine ⟨fun a=>differentiable_const _,fun i j k a t=> by funext; simp [along,v,I'],fun a j k he t h=> ?_⟩; filter_upwards [hf.eventually (ge_mem_nhds (mul_pos h (norm_pos_iff.mpr (sub_ne_zero.mpr (hZ.ne he)))))] with i hi u hu using (by simpa [v,I'] using hi)
-- Smooth beams
include U
variable (p:J→ C.book.Token)(a':I)(M:Mode U.sector.derivatives)(R:Prescription U.sector.derivatives) {o:L→ E4} (hx:Tendsto (fun i=> ‖o i‖) f (𝓝 0))
include a'
include hx in
lemma Slender.illuminated (e:Exterior C.book) : Lent (f:=f) (T:=T) (F:=fun i z=> Prescription.reading S (x i z) p (o i) e):=(Slender.addOn ht (S'.away hx) (bearing e) (bearing_clear e)).budgets U (beside p e.letter) ht a' -- order
lemma Slender.on (hx:Tendsto (fun i=> ‖o i‖) f (𝓝 0)) : Lent (f:=f) (T:=T) (F:=fun i z=>R.ope M (x i z) p (o i)):=by
    unfold Prescription.ope; exact Lent.sum ht (fun i (_:i∈ (R.sheet M).support)=> (Lent.const ht (RateLE.const _ ht)).mul (S'.illuminated U ht p a' hx i)) -- parameter order h?
end YM.OPE.Log.Reels
