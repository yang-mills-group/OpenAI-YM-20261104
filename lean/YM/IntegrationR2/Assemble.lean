import YM.IntegrationR2.Plate
import YM.FullVolume.Mark.Latch
import YM.MergeProof.Sonata

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric.R2
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p m : ℕ) (A : Hol G)
open Extra.Histories.InputColumn
local notation "κ"=> Real.sqrt (H.levels.clock.forcedAllowance (m+1))
private lemma foam {ι W : Type*} {u : W → ℂ} {f : ι → W → ℂ} (h : Dominated f) (hv : ∃ c : ℝ, ∀ x, ‖u x‖ ≤ c) :
    Dominated fun i x => u x * f i x := by
  obtain ⟨b,hb,hr⟩ := h; obtain ⟨c,hh⟩ := hv
  refine ⟨_,hb.mul_left c,fun i x => ?_⟩
  rw [norm_mul]; exact mul_le_mul (hh x) (hr ..) (norm_nonneg _) ((norm_nonneg _).trans (hh x))
variable {T : Extra.Histories.Heading F} {C η t w : ℝ}
local notation "Old"=> H.rep N p (m+1)
set_option quotPrecheck false
section
variable {n:Side}{P:Coefficient F n}{R:Rep G n}{Y:Hol G} {κ' a b:ℝ}
lemma rack_reserve (K:Keeper R.p R.activities) (h:P.Format 0 Y R) (hp:Tab P 0 R κ' a b) : Tab (rack K P) 0 R κ' a b :=
   ⟨hp.divisor,hp.first,hp.second,hp.regular,(wages _ _ h hp).forced⟩
lemma Plus.nil (hv:0≤ a) : Plus R (book (0:F.Coeff) 0) a := by
   refine ⟨fun _=>0,?_,fun i=> (regular0 ..).2⟩
   simp_rw [reservedMass,mul_zero]; exact Local.sumBudget_zero (div_nonneg hv turn_pos.le)
lemma Plus.orientPaid (z:Extra.Histories.Motion) (S:R.activities.Moves z.1 0) (h:Plus R P b) (hf:P.Format 0 Y R) (he:2≤n.val):
   Blown (audition S P) 0 R b := by
    have hx:= Blown.spin (z:=z) (R:=R) h S hf he -- replace
    rw [mul_div_cancel₀ _ turn_pos.ne',show affine z.1 (0:Site n) 0=0 from by simp [affine]] at hx
    exact hx
end
/-!
Sharpen `design`: Reassembly uses the canonical forced input's *undivided*
mass. The gain here applies to output in `Tool`'s native dictionary. In
particular we haven't discarded forced feedback into either channel. Include
+2 as ADDITIONAL reserve. Uses `FullVolume.Mark.Slate` proof adapted to this
bound.
-/
local notation "R"=> H.rep N p m
lemma splitDesign (F':Plate F (H.S.side (m+1) p) (H.S.side m p)) (Z : Keeper (H.rep N p (m+1)).p (H.rep N p (m+1)).activities)
    (P : Coefficient F (H.S.side (m+1) p))(X:Wing→Prop)(D:GaugeDoor Old R)(i:F.Index)
    (h:H.Selected)(hm:m<N)(hp:P.Format 0 A (H.rep N p (m+1))){l r:ℝ}(hP:Tab P 0 Old κ l r)(hx:P.x=Size.axis F i)
    (hs:P.support=mapSeat)(hq: SoundDoor (H.levels.clock.op m p) D)(hz:0≤η)(hD:Plate.Prints B H N p m A F' T C η w D X)
    (hrP:ReservePlate B H N p m A Old (H.S.block m) F' C η D) (heX:∀ i, X (.gasKey (cart Z i))):
    let L := H.S.block m; let x:= P.x
    let t := l + κ*r
    Span B H N p m A (gather F' Z P i) (P.exponentialEntry 0 B (Old)) (profile (Old).activities P.forced) (P.x 0) D X (P.density 0 B Old) (T.leads L x) (η*(F.coeffSize (F.core x)+t)) (C*F.coeffSize (vowel F L (F.core x))+η*t) (w+2*t) ∧
    Plus R (gather F' Z P i) (C*F.coeffSize (vowel F L (F.core x))+η*t) :=by
   intro L x t
   let Q:= rack Z P; have hx':Q.x=x:=rfl; have htQ: Q.Format 0 A Old:=rack_format Z P hp; have htab: Tab Q 0 Old κ l r:= rack_reserve Z hp hP; have hw := htab.bound le_rfl
   have hr: profile (Old).activities Q.forced=profile (Old).activities P.forced:= stows Z P
   have he: Q.exponentialEntry 0 B (Old)=P.exponentialEntry 0 B (Old):=rfl
   let J:=Extra.Histories.primary (0:Site (H.S.side (m+1) p)) x
   let f:= consist (J.density 0 B (Old)) (fun i => Extra.Histories.salary (Old) (Q.support i) (Q.regular i)) (fun i => Extra.Histories.fare (Old) i (Q.forced i))
   have hk := (h.represents N p (m+1) hm).good
   have h0 : 0 < κ := Real.sqrt_pos.2 (forcedPos ..)
   have hE := Rep.envelope Old hk
   have hR := (Rep.exponentEnv Old hk).exp
   have hL := rem_dominated hw
   have hy := Coefficient.envelope B hk (primary_rem (o:=0) x h0) (primary_format (o:=0) (H:=A) x); let U₀:= Old
   have hu : Dominated f := by
      refine InputColumn.dominated hy.cost (foam (Q.regular_series hw) ?_) (foam (dress_abs hk hL) ?_)
      · obtain ⟨c,hc⟩ := hE.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
      obtain ⟨c,hc⟩ := hR.cost; exact ⟨c, fun i => (Complex.norm_real _).trans_le (hc i)⟩
   have hf (i : Listing) : Measurable (f i) := by
      rcases i with i|i|i; exact hy.meas
      exact (Complex.continuous_ofReal.measurable.comp hE.meas).mul (masked_measurable _ _ _ (htQ.smooth i).borel)
      exact (Complex.continuous_ofReal.measurable.comp hR.meas).mul ((htQ.borel i).mul (dressed_meas hk i))
   have hP': P.density 0 B Old=Q.density 0 B Old:= reentry he.symm hk (rem_dominated (hP.bound le_rfl)) hL hr.symm
   have hW : Q.density 0 B Old = fun U => ∑' i, f i U := by
      funext U; let a i := Q.maskedTerm Old i U; let b i := Q.forced i U * dressed Old i U
      have hn : HasSum a (∑' i, a i) := ((Q.regular_series hw).summable U).hasSum
      have ha : HasSum b (∑' i, b i) := ((dress_abs hk hL).summable U).hasSum
      rw [(added (f:=fun i => f i U) (hn.mul_left ((Old).eval U:ℂ)) (ha.mul_left (Real.exp ((Old).exponent U):ℂ))).tsum_eq]; change _ = (Extra.Histories.primary 0 x).density 0 B Old U + _
      rw [primary_density,Coefficient.density,dress_eq hk hL]; change ((Old).eval U:ℂ)*(part B 0 Old U Q.x+∑' i,a i) + _ = _; rw [hx']; unfold b; ring

   obtain ⟨a,hA,hA'⟩:= htab.regular; obtain ⟨b,hB,hB'⟩:= htab.forced
   let g i:=(Old).p.mass (Q.support i) (a i); let k i:=((Old).p.mass ((Old).activities.forced i).support (b i))
   let y:= F.coeffSize (F.core x); let d':= F.coeffSize (vowel F L (F.core x))
   let V:= consist (η*y) (fun i=> η*g i) (fun i=> η*k i); let W:= consist (C*d') (fun i=> η*g i) (fun i=> η*k i)
   let U': Listing→F.Coeff:= consist (T.leads L x) 0 0
   let Hp := consist w (fun i=> 2*g i) (fun i=>2*k i); let O':Listing → Config G (H.S.side (m+1) p)→ℂ:=consist (J.exponentialEntry 0 B Old) (Q.maskedTerm Old) (fun _=>0); let E':= consist 0 (fun _=>0) (fun i=> exactGas U₀.activities i (Q.forced i)); let Y': Listing→ℂ:= consist (P.x 0) 0 0
   have hin(i':Listing): Span B H N p m A ((tell ∘ tags F' Z P i) i') (O' i') (E' i') (Y' i') D X (f i') (U' i') (V i') (W i') (Hp i') ∧ Plus R ((tell ∘ tags F' Z P i) i') (W i') :=by
      rcases i' with i'|j|j
      · change Span B H N p m A (tell (F'.main i)) (J.exponentialEntry 0 B Old) 0 (P.x 0) D X (J.density 0 B Old) _ _ _ w ∧ _
        have hx₀:x=Size.axis F i:=hx
        change Span _ _ _ _ _ _ _ _ _ _ _ _ _ (T.leads L x) (η*F.coeffSize (F.core x)) (C*F.coeffSize (vowel F L (F.core x))) w ∧ Plus R (tell (F'.main i)) (C*F.coeffSize (vowel F L (F.core x))) -- hx, x=L here
        unfold J; rw [hx,hx₀]; exact ⟨hD.main i, hrP.main i⟩
      · let U:= H.rep N p (m+1)
        have hp':U.p.supBounds 0 (mapSeat j) (P.regular j) (a j):=(congr_fun hs j) ▸ (hA' j)
        have hv':RegFit U 0 d A (mapSeat j) (P.regular j):=(congr_fun hs j) ▸ (show RegFit U 0 d A (P.support j) (P.regular j) from ⟨hp.smooth j,hp.origin j,hp.identity_null j,hp.projects j⟩)
        change Span _ _ _ _ _ _ _ (masked U.p.threshold (P.support j) (P.regular j)) _ _ _ _ (Extra.Histories.salary U (P.support j) (P.regular j)) _ (η*(U.p.mass (P.support j) _)) (η*(U.p.mass (P.support j) _)) (2*(U.p.mass (P.support j) _)) ∧ Plus R (tell (F'.tint j (P.regular j))) (η*(U.p.mass (P.support j) _))
        rw [congr_fun hs j]; exact ⟨hD.regular j _ _ hv' hp',hrP.regular j _ _ hv' hp'⟩
      classical
      by_cases ht : Q.forced j=0
      · change Span B H N p m A (tell (F'.ink j (Q.forced j))) 0 (exactGas _ j (Q.forced j)) 0 D X (Extra.Histories.fare _ j (Q.forced j)) 0 _ _ _ ∧ Plus R (tell (F'.ink j (Q.forced j))) (W (.inr (.inr j)))
        rw [ht]; rw [show exactGas (Old).activities j 0=0 by simp [exactGas]]; rw [show Extra.Histories.fare Old j 0=0 from funext fun U=> by simp [Extra.Histories.fare],hD.blank]; exact ⟨spanNone B H N p m A X D (mul_nonneg hz (hB.1 j)) (mul_nonneg zero_le_two (hB.1 j)),Plus.nil (mul_nonneg hz (hB.1 j))⟩
      have hψ:X (.gasKey j):=by
         have hr:j∈ Set.range (cart Z):= not_not.mp (fun hp'=>ht (pit Z P hp')); obtain ⟨p,rfl⟩:=hr; exact heX _
      exact hrP.forced X j _ (b j) ht hψ ⟨htQ.invariant j, htQ.borel j,htQ.supported j,htQ.carried j,htQ.forcing j⟩ (hB' j).2
   let z':=(∑' i,g i)+(∑' i,k i); have hy':z'≤t:=(add_le_add hA.2.2 hB.2.2)
   have hV:HasSum V (η*y+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (hB.2.1.hasSum.mul_left _)
   have hW':HasSum W (C*d'+η*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (hB.2.1.hasSum.mul_left _)
   have hQ:HasSum Hp (w+2*z'):=by unfold z';rw [mul_add]; exact added (hA.2.1.hasSum.mul_left _) (hB.2.1.hasSum.mul_left _)
   have huP : HasSum U' (T.leads L x):=by simpa only [U',consist,add_zero, Sum.elim_inl] using added (f:=U') hasSum_zero hasSum_zero
   have hP₀: Summable (fun i=> F.coeffSize (U' i)):= by apply summable_of_ne_finset_zero (s:={Sum.inl ()}); rintro (⟨⟩|i|i) hi; simp at hi; all_goals simp [U',Labels.Frame.coeffSize,consist]
   have hδ : HasSum Y' (P.x 0):=by simpa only [Y',consist,add_zero, Sum.elim_inl] using added (f:=Y') hasSum_zero hasSum_zero
   have he' (U): HasSum (fun j=> O' j U) (P.exponentialEntry 0 B Old U):=by
      have hJ j:J.maskedTerm Old j U=0:=congr_fun (map_zero (Push.Local.maskLinear _ _)) _
      have Hx(i:Coefficient F (H.S.side (m+1) p)):i.exponentialEntry 0 B Old U= part B 0 Old U (Coefficient.x i)+∑' j,i.maskedTerm Old j U:=rfl
      rw [← he,Hx,hx']; convert added (f:=fun j=> O' j U) ((Q.regular_series hw).summable U|>.hasSum) (hasSum_zero) using 1; change _= J.exponentialEntry _ _ _ U+(_+0);rw [Hx]; simp_rw [hJ,tsum_zero,add_zero];rfl -- hw consumed use
   have hq' j U: HasSum (fun i=> E' i j U) (profile (Old).activities P.forced j U):=by
      rw [← hr]; convert added (f:=fun i=>E' i j U) hasSum_zero (profiled (Old).activities _ hL U j) using 1; change _=(0:ℂ)+(0+_); rw [zero_add,zero_add]
   have h' := wind B H N p m A D hq h hm.le (fun j=>(hin j).1) he' hq' hδ hu hf hP₀ hV.summable hW'.summable hQ.summable
   rw [← hW,← hP',hV.tsum_eq, hW'.tsum_eq,hQ.tsum_eq,huP.tsum_eq] at h'; refine ⟨?_,?_⟩; apply Span.weaken h' (by nth_rw 2 [mul_add]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz)) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' zero_le_two))
   have he := Plus.joins (code Listing) (fun i => (hin i).2) hW'.summable
   rw [hW'.tsum_eq] at he; exact he.more (add_le_add le_rfl (mul_le_mul_of_nonneg_left hy' hz))
end YM.MergeProof.Matric.R2
