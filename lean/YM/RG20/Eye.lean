import YM.OPE.Vitrines.Budget
import YM.UVExtension.Eyelet.Wares
import YM.MergeProof.Accent

/-!
# One-step accounts seen by the same-family chart

Equality of two `UVExtension.Eyelet.Eye` observations (at actual eligible sources and
in a fixed vacuum chart) remembers enough for FULL exponent, aggregate forced histories
AND regular extra reserve. We don't just observe primary readout, grab arbitrary K
representatives for next estimates, or use this as a re-presentation principle for
*unmarked* density; that's fixed inclusive of all predicates, thresholds and sites.

`ageing`/`rack` normalize the source presentation to avoid trying to get a raw K budget on a
cancelling family. If desired for a joint `Accent.restore`, KEEP THE CARTON MULTI component
identical and just substitute these representatives for singleton carriers. No dropping flags,
unit lanes or re-assuming independence. Downstream associated Blown regular (+2) reserve is
not proxied by norm of Eye and transports without reverse-bounding via the latter.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RG20
open Lattice Wilson Source Labels RG Extra.Histories Push UVExtension Eyelet MergeProof
  Function Filter Planned.GuardedAtom
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

section
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
  {A : Hol G} {R : Rep G n} {P Q : Coefficient F n} {v a : ℝ}
  (hP : Eligible P A R v) (hQ : Eligible Q A R v)
  (h : Eye P A R v = Eye Q A R v)

include h in
lemma seeIndex : P.x = Q.x := (sees ..).symm.trans ((congr_arg Prod.fst h).trans (sees ..))

include hP hQ h
lemma seeTag (i : Eyelet.Slot n) (z : supE (G := G) R.p i) :
    z.read (graft P i) = z.read (graft Q i) := by
  have he := congr_arg (gaze d A R.p i z) (show hP.tollE = hQ.tollE from
    congr_arg (fun X : Bucket F R.p A n => X.2.1) ((hP.vistas).symm.trans (h.trans hQ.vistas)))
  rw [hP.take, hQ.take] at he
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (toll_pos ..).ne') he

lemma seeSup (i : Eyelet.Slot n) (b : ℝ) :
    R.p.supBounds 0 i.1.1 (graft P i) b ↔ R.p.supBounds 0 i.1.1 (graft Q i) b := by
  simp_rw [Concert.tap_bound, fun z => seeTag hP hQ h i z]

lemma seeMask (i : Eyelet.Slot n) :
    masked R.p.threshold i.1.1 (graft P i) = masked R.p.threshold i.1.1 (graft Q i) := by
  funext U
  by_cases hu : Healthy R.p.threshold i.1.1 U
  · rw [masked_eq _ _ _ _ hu, masked_eq _ _ _ _ hu]
    exact seeTag hP hQ h i ⟨U, hu, [], Nat.zero_le _, by simp⟩
  simp_rw [masked_ne _ _ _ _ hu]

lemma seeBar : profile R.activities P.forced = profile R.activities Q.forced := by
  funext i U
  by_cases hi : i ∈ Set.range (barcode R.activities)
  · obtain ⟨i,rfl⟩ := hi
    let z := sender R.activities i
    have he := congr_arg (tire R.p z ⟨U⟩) (show hP.tollK = hQ.tollK from
      congr_arg (fun X : Bucket F R.p A n => X.2.2) ((hP.vistas).symm.trans (h.trans hQ.vistas)))
    rw [hP.make, hQ.make] at he
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (div_pos (toll_pos ..) hP.vigor).ne') he
  haveI : IsEmpty {j // barcode R.activities j = i} := ⟨fun ⟨j,e⟩ => hi ⟨j,e⟩⟩
  simp only [profile, cram, tsum_empty]

lemma seeEx (B : SectionData F) :
    P.exponentialEntry 0 B R = Q.exponentialEntry 0 B R := by
  let K := hP.hK.some
  rw [← respect P K hP.form.origin B, ← respect Q K hQ.form.origin B]
  funext U
  unfold Coefficient.exponentialEntry
  rw [show (ageing P K).x = (ageing Q K).x from seeIndex (P := P) (Q := Q) h]
  exact congr_arg (_ + ·) (tsum_congr fun i => congr_fun (seeMask hP hQ h (key n i)) U)

lemma seeDensity {σ C Λ δ w : ℝ} (hr : R.Lawful σ C Λ δ w) (B : SectionData F) :
    P.density 0 B R = Q.density 0 B R := by
  obtain ⟨x,hx⟩ := hP.pay
  obtain ⟨y,hy⟩ := hQ.pay
  exact reentry (seeEx hP hQ h B) hr (rem_dominated hx) (rem_dominated hy) (seeBar hP hQ h)

lemma seeRackForced (K : Guard.Keeper R.p R.activities) :
    (rack K P).forced = (rack K Q).forced := by rw [rack,rack]; change extend _ _ _ = extend _ _ _; rw [seeBar hP hQ h]

omit h

/-- Any multiplicative support weight on regular charges. No volume factor.
Witness via alias-preserving index embedding. -/
def SFund (P : Coefficient F n) (R : Rep G n) (w : Support n → ℝ) (a : ℝ) : Prop :=
    ∃ e : ℕ → ℝ, SumBudget (fun i => w (P.support i) * e i) a ∧
      ∀ i, R.p.supBounds 0 (P.support i) (P.regular i) (e i)

-- exactly the alias embedding, not forgetting equal support names
omit hP hQ in
lemma inAgeing (ho : ∀ i, (0 : Site n) ∈ P.support i) (K : Guard.Keeper R.p R.activities)
    (w : Support n → ℝ) : SFund P R w a ↔ SFund (ageing P K) R w a := by
  let Z := takes P ho
  have hs i : (ageing P K).support (Z i)=P.support i := (bunch P ho i).1
  have hf i : (ageing P K).regular (Z i)=P.regular i := (bunch P ho i).2
  constructor
  · rintro ⟨e,hE,hB⟩
    let g:= extend Z e 0
    have hG i : g (Z i) = e i := Z.injective.extend_apply ..
    have ho' i (hX : i ∉ Set.range Z) : g i=0 := extend_apply' _ _ _ hX
    refine ⟨g, Local.sumBudget_pass Z _ ?_ (fun i h => by simp only [ho' i h,mul_zero]), ?_⟩
    · simp_rw [hs,hG]; exact hE
    intro i
    by_cases hh : i ∈ Set.range Z
    · obtain ⟨j,rfl⟩ := hh
      rw [hs,hf,hG]; exact hB _
    rw [show (ageing P K).regular i=0 from sleeps P ho i hh, ho' i hh]
    exact (hot ..).2
  rintro ⟨e,hE,hB⟩
  refine ⟨e ∘ Z, ?_, fun i => ?_⟩
  · have hE := AbsoluteSums.budget_pull Z Z.injective hE
    simp_rw [hs] at hE
    exact hE
  rw [← hf, ← hs]; exact hB _

include h
lemma seeFunds (w : Support n → ℝ) : SFund P R w a → SFund Q R w a := by
  let K:= hP.hK.some
  rw [inAgeing hP.form.origin K w,inAgeing hQ.form.origin K w]
  rintro ⟨e,hE,hB⟩
  exact ⟨e,hE, fun i => (seeSup hP hQ h (key n i) (e i)).mp (hB i)⟩

lemma seeBlown (hB : Blown P 0 R a) : Blown Q 0 R a :=
  seeFunds hP hQ h (fun S => Real.exp ((R.p.supportExponent + 2)*coverNumber R.p.B S)) hB

/-- Full remainder bound forwards after canonical stow; includes divisor at this scale.
No uncontrolled decompaction. -/
lemma seeBill (K : Guard.Keeper R.p R.activities) (he : P.remBound 0 R v a) :
    (rack K Q).remBound 0 R v a := by
  obtain ⟨x,y,hx,hy,hX,hV,hE,hB⟩ := keeps K P he
  have f := seeFunds (a := x) hP hQ h (w := fun S => Real.exp (R.p.supportExponent * coverNumber R.p.B S)) hE
  refine ⟨x,y,hx,hy,hX,hV,f,?_⟩
  rw [← seeRackForced hP hQ h K]; exact hB

-- joint transport in Accent.restore representation. E.K activities addresses unchanged.
-- compatible with any existing H K and their Towed bounds, any same-root frame.
omit hP hQ h
open MergeProof.Accent Marker Motion
lemma seeCarton {I : Type*} [Fintype I] [DecidableEq I] {Γ : Census I}
    {P Q : I → Coefficient F n} (hP : ∀ i, Eligible (P i) A R v) (hQ : ∀ i, Eligible (Q i) A R v)
    (h : ∀ i, Eye (P i) A R v = Eye (Q i) A R v) (B : SectionData F)
    (m : I → Motion) (x : I → Site n) (H : Support n → Config G n → Poly Γ)
    (K : MergeProof.Box n → Config G n → Poly Γ) :
    restore R (fun i => stepUp (m i) (x i) ((P i).exponentialEntry 0 B R))
      (fun i => floatUp (m i) (x i) (profile R.activities (P i).forced)) H K =
    restore R (fun i => stepUp (m i) (x i) ((Q i).exponentialEntry 0 B R))
      (fun i => floatUp (m i) (x i) (profile R.activities (Q i).forced)) H K := by
  simp_rw [fun i => seeEx (hP i) (hQ i) (h i) B, fun i => seeBar (hP i) (hQ i) (h i)]
end
end YM.RG20
end
