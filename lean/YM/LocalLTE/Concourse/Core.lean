import YM.LocalLTE.Drift.Story
/-!
# Grade zero representations and stripping unit

Scalar transport in the moment sector does NOT use the same slack argument as the
irrelevant pages. Exact unit step, priced additions. Also record elementary
actual-probe estimates on this same frame's grade coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Concourse
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Guard Push Local Motion LocalLTE.Vinca LocalLTE.River
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n:Side}{d:ℕ}
lemma weightPositive (D:Labels.Frame G d)(i:D.Index)(h:i≠0) : 0 < (D.grades i).1 :=by
    classical
    have hx : (D.basis i).val ≠ 0:= fun he => D.basis.ne_zero i (Subtype.ext he)
    obtain ⟨u,hu⟩:∃ u : Labels.Key G →₀ ℕ, MvPolynomial.coeff u (D.basis i).val≠0:=by
       by_contra! hh; apply hx; ext i; simp [hh]
    have he := (Labels.pure_grade _ _).1 (D.pure i) hu
    have hp := D.factors_pos i h; have ht : (Finsupp.weight Labels.bidegree u).2 ≤ _ := Labels.power_le u
    change (Finsupp.weight Labels.bidegree u)=D.grades i at he; rw [← he] at hp; refine hp.trans_le (ht.trans_eq ?_); rw [← he, Labels.weight_slot]
lemma onlyZero (D:Labels.Frame G 0)(i:D.Index) : i=0:= not_not.mp (fun h=>Nat.not_lt_zero _ ((weightPositive D i h).trans_le (D.bound i)))
variable {F:Labels.Frame G 0}
lemma center_eq (v:F.Coeff): v=v 0 • F.e0:=by
    funext i; rw [onlyZero F i]; simp [Frame.e0]
lemma removes (v:F.Coeff): F.core v=0:=by
    funext i; rw [onlyZero F i]; change Function.update (β:=fun _:F.Index=>ℂ) v 0 0 0=0; rw [Function.update_self]
lemma center_size (v:F.Coeff) : F.coeffSize v=‖v 0‖:=by
    unfold Labels.Frame.coeffSize; rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _)]; intro i _ h; exact (h (onlyZero F _)).elim
lemma center_entry (D:SectionData F) (P:Coefficient F n)(R:Rep G n)(o:Site n)(U:Config G n) : P.exponentialEntry o D R U=P.x 0+∑' j,P.maskedTerm R j U:=by
    unfold Coefficient.exponentialEntry; rw [removes P.x,map_zero,show D.places 0 o=0 from funext fun i=>congr_fun (map_zero (IsLinearMap.mk' D.evaluate D.eval_linear)) _]
    congr 1; rw [add_eq_left]; exact congr_fun (map_zero (maskLinear R.p.threshold (D.footprint o))) U
-- run on limbs without scalar. keep SAME forced roles/addresses.
variable (v:F.Coeff)
noncomputable abbrev memo (T:Coefficient F n):Coefficient F n:={T with x:=v}
variable {v}{P Q : Coefficient F n}{R:Rep G n}{D:SectionData F}{A: Hol G}{o : Site n}{ν t s:ℝ}
lemma memo_format (v:F.Coeff) (h:P.Format o A R) : (memo v P).Format o A R := ⟨h.smooth,h.origin,h.identity_null,h.projects,h.forcing,h.carried,h.invariant,h.supported,h.borel⟩
lemma memo_cost (v:F.Coeff)(h:P.remBound o R ν t): (memo v P).remBound o R ν t:=h
lemma memo_force (v:F.Coeff)(h:Tab P o R ν t s):Tab (memo v P) o R ν t s:=⟨h.divisor,h.first,h.second,h.regular,h.forced⟩
lemma memo_density (v:F.Coeff)(P:Coefficient F n)(D:SectionData F)(o:Site n)(R:Rep G n)(U:Config G n): (memo v P).density o D R U=P.density o D R U+((v-P.x) 0)* (R.eval U:ℂ):=by rw [Coefficient.density,Coefficient.density,center_entry,center_entry]; dsimp only [Pi.sub_apply]; change (R.eval U:ℂ)*(v 0+∑' i,P.maskedTerm R i U)+↑(Real.exp _)*(∑' i,P.marked R i U)=_;ring
lemma solo_lead (T:Heading F)(L:Side): T.leads L F.e0= F.e0:=by change T.map (vowel F L F.e0)=_; rw [show vowel F L F.e0=F.e0 from ?_,T.unit]; funext i; rw [onlyZero F i]; simp [vowel]
lemma memo_off (u v:F.Coeff)(P Q: Coefficient F n) : Vinca.decrement (memo u P) (memo v Q)=memo (u-v) (Vinca.decrement P Q):=rfl
variable {x y z:ℝ}{a j:ℕ}
lemma disrobe (h:Exhibition D x a j A R P Q ν t z):Exhibition D x a j A R (memo 0 P) (memo 0 Q) ν t z:=by
    have he := h.stock; refine ⟨⟨?_,he.regular,he.forced⟩, memo_format _ h.format,h.layout,?_,?_,?_⟩
    · simpa [memo,Frame.coeffSize] using he.cost
    · rw [memo_off]; exact memo_format _ h.trade
    · rw [memo_off]; exact memo_force _ h.fee
    rw [memo_off]; simpa [memo,Frame.coeffSize] using h.fee.first
lemma stripped (h:Patrons D x a j R.p P t): Patrons D x a j R.p (memo 0 P) t:= by
    exact ⟨by simpa [memo,Frame.coeffSize] using h.cost, h.regular,h.forced⟩
end YM.LocalLTE.Concourse
