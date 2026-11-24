import YM.Push.ABSOLUTE_SUMS.Labels
import YM.MergeProof.Tally
import YM.Extra.MULTISOURCE_BOUNDS.Bands
import YM.Overlay.Pays

/-! # Seat all marked modes (weight launch). Can separate union terms with arbitrary aft-grade.

Produce true Overlay.Bands on stepped Rep without resampling hard address, predicate, anchor or
nest. Defined on complete all-flag carrier and its unmasked extension for nonempty Modes and
with pins on ALL (not just single-character events); use ANY volume in SeatCost conversions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsI.Seat
open Function Marker RG Wilson MeasureTheory Filter Finset Lattice Ac
open Push Push.AbsoluteSums Extra.Multi MergeProof.Accent
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{V:Type}[Fintype V][DecidableEq V][Nonempty V]{P: Census V}{R:Rep G n}
variable {ι:Type}
structure Ship (ι:Type)(P:Census V)(R:Rep G n) where
   origin : V→Site n
   lo : ι→Support n
   E : ι→ Config G n → Poly P
   model : ι→ P.Mode→ Config G n→ℂ -- extension at H-support union
   K : ℕ→Config G n→Poly P -- complete force path incl unmarked predecessor
namespace Ship
variable (A:Ship ι P R)
structure Valid : Prop where
   loNe i : (A.lo i).Nonempty
   Eformat i : Burns A.origin (A.lo i) (A.E i) R.p.threshold
   model i a : R.p.Regular (A.lo i) (A.model i a)
   agrees i s (U:Config G n) : s≠P.quiet→ masked R.p.threshold (A.lo i) (A.model i s) U=(A.E i U).part s
   born i : Borne A.origin (R.activities.forced i).support (A.K i) R.p.threshold
   keeps i U : A.K i U≠0 → (R.activities.forced i).eligible R.p.threshold U
   still i U : (A.K i U).part P.quiet=(R.activities.K i U:ℂ)

-- all ROOT and every power reserve. reintegration requires L¹ proof later
variable (lev:ι→ℕ)(r:V→ℝ)
def sumTag {α:Type} (g:α→P.Mode→ℝ)(i:α) := ∑ j, Poly.toll r j*g i j
structure Spiral (a b:ℝ)(u:ℕ→ℝ)(c:ℝ): Prop where
   loans : ∃ g:ι→P.Mode→ℝ, (∀ i y,0≤g i y∧∀ x∈ A.lo i, R.p.supBounds x (A.lo i) (A.model i y) (g i y)) ∧
      ∀ k, Hit A.lo R.p.B (fun i=> if k≤lev i then sumTag (P:=P) r g i else 0) a (u k)
   fires : ∃ g:ℕ→P.Mode→ℝ, (∀ i y U, ‖(A.K i U).part y‖ ≤ g i y) ∧ Hit (fun i=>(R.activities.forced i).support) R.p.B (fun i=> sumTag r g i) b c
local notation "A!" => A
end Ship

section bind
open Overlay
variable (A:Bands P R)
variable (t:ℕ→ℕ)
-- Hold full norm through all radii AFTER the valuation = linear budget for H on entire healthy set
structure Graded (w:V→ℝ)(a:ℝ)(v:ℕ→ℝ) : Prop where
    sounds : ∃ u:ℕ→ℝ,(∀ i,0≤u i ∧ ∀ j∈A.support i,R.p.supBounds j (A.support i) (A.H i) (u i)) ∧
       ∀ m,Hit A.support R.p.B (fun i=> if m ≤ t i then Poly.toll w (A.rays i)*u i else 0) a (v m)
structure Glow (w:V→ℝ)(e c:ℝ): Prop where
    posts : ∃ u:ℕ×ℕ→ℝ,(∀ i U, ‖A.entries i.1 i.2 U‖≤u i) ∧ Hit (Extra.Multi.forced R) R.p.B (fun i=> Poly.toll w (tags A i)*u i) e c
-- projection E and K keep ALL geometry
variable {a b c' u e:ℝ}{v:ℕ→ℝ}{V':Bands P R}{w:V→ℝ}
omit [Nonempty V] [Fintype V] in
lemma Weigh {I: Type} (o:V→Site n)(s:I→Support n)(P': BudgetPoint) (q:I→ P.Mode) {f:I→ℝ} (hf:∀ i,0≤ f i)(hc:∀ i,0<f i→∀ j∈(q i).val,o j∈ s i) (he:Hit s P'.B (fun i=>Poly.toll w (q i)* f i) a c')(hp:P'.supportExponent+e ≤ a)(hw:∀ i,0<w i) : Weighted q s P' w e f c':=by
   intro z; refine Push.AbsoluteSums.budget_mono (he (o z)) (fun i=> ?_) fun i=> ?_
   · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Poly.worth hw _).le (hf _));rfl
   dsimp only; split
   next h =>
     rcases (hf i).eq_or_lt with hi|hu
     · rw [← hi,mul_zero,mul_zero]; simp
     rw [if_pos (hc _ hu _ h), mul_comm]
     exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (mul_nonneg (Poly.worth hw _).le hu.le)
   next=> exact (he (o z)).1 _

set_option quotPrecheck false
local notation "forceK" => Extra.Multi.forced R
omit [Nonempty V] [Fintype V] in
lemma Graded.roots (h:Graded A t w a v)(ha:A.Active) (b:ℝ)(hb:R.p.supportExponent+b≤a)(hw:∀ i,0 < w i): ∃ u:ℕ→ℝ,(∀ i,0 ≤ u i∧ ∀ x∈(A.rays i).val,R.p.supBounds (A.origins x) (A.support i) (A.H i) (u i)) ∧
      ∀ m,Weighted A.rays A.support R.p w b (fun i=>if m≤t i then u i else 0) (v m):=by
   obtain ⟨v',hV,hE⟩:=h.sounds
   refine ⟨v',fun i=> ⟨(hV i).1,fun j hj=>(hV i).2 _ (ha.pins i j hj)⟩, fun i=> Weigh A.origins _ _ _ (fun j=>?_) (fun i _=> ha.pins i) ?_ hb hw⟩
   · split; exact (hV _).1;rfl
   convert! hE i using 2; split <;> ring
omit [Nonempty V] [Fintype V] in
lemma Glow.roots (h:Glow A w a u)(ha:A.Active)(b:ℝ)(hb:R.p.supportExponent+b≤a)(hw:∀ i,0<w i): ∃ t:ℕ×ℕ→ℝ,(∀ i U, ‖A.entries i.1 i.2 U‖ ≤ t i) ∧ Weighted (tags A) forceK R.p w b t u :=by
   obtain ⟨k,hp,hK⟩:= h.posts
   let k' (i:ℕ×ℕ):= if A.entries i.1 i.2=0 then 0 else k i
   have he (i:ℕ×ℕ) U: ‖A.entries i.1 i.2 U‖≤k' i:=by
      unfold k'; split
      next h=> simp [h]
      next=> exact hp i U
   have hz i:0≤k' i:= (norm_nonneg _).trans (he i 1)
   refine ⟨k',he,Weigh A.origins _ _ _ hz (fun i hu=> ?_) ?_ hb hw⟩
   · unfold k' at hu; split at hu; · linarith
     next hh=> exact ha.retained _ _ hh
   refine Push.AbsoluteSums.Labels.raise_prices _ _ (fun i=> mul_nonneg (Poly.worth hw _).le (hz i)) hK fun i=> mul_le_mul_of_nonneg_left ?_ (Poly.worth hw _).le
   unfold k'; split; exact (norm_nonneg _).trans (hp i 1); exact le_rfl
omit [Nonempty V] [Fintype V] in
lemma rady (h:Graded A t w a v)(hf: Glow A w b u)(ha:A.Active)(he:R.p.supportExponent≤a)(hg:R.p.supportExponent≤b)(hw:∀ i,0 < w i)(hc:u ≤ e*c')(hp:0<c'){q:ℝ}(hu:∀ i,w i*‖A.units i‖≤ q) : A.Radial w q (v 0) e c' :=by
    obtain ⟨t',hx,H⟩:= Graded.roots A t h ha 0 (by simpa using he) hw
    obtain ⟨K,hh,hV⟩:= Glow.roots A hf ha 0 (by simpa using hg) hw
    refine ⟨hw,hu,hp,⟨_,hx,fun i=> ?_⟩,K,fun i j=> ⟨(norm_nonneg _).trans (hh (i,j) 1), hh (i,j)⟩,fun i=> ?_⟩
    · simpa [BudgetPoint.mass,mul_left_comm] using H 0 i
    exact budget_loosen (by simpa [BudgetPoint.mass, tags,mul_left_comm] using hV i) hc
end bind
end YM.GapsI.Seat
