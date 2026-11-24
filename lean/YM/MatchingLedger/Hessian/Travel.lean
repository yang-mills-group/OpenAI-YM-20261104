import YM.MatchingLedger.Hessian.Columns
import YM.MatchingLedger.Hessian.Pipes

/-!
# No orientation averaging until done pricing

Held slot(slotFace) cost after flipping directions. Native mass (shared path and rep in later
callers). Loop unsymmetric per-atom paid without cycling labels. This is at represented kinetic
FITTED output, not an argument defining it independently from a recipe.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Spring
open Function Filter Lattice Wilson RG Exterior Precision Work.F03 Pert Pert.Kinetic
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Finset
variable {n : Side} {G : Gauge} (c : G.Color) (R : PathData G) {C Λ σ : ℝ} {p : Clip} (h : R.Bounds p σ C Λ)

-- solvable spectral test cost; clip direct controlled internally
include h
private def card_face : PlaqAxes:= ⟨(0,1),by decide⟩ -- omit
lemma upper_C : 0≤ C:= (tsum_nonneg (h.rows card_face).1).trans (h.rows card_face).2.2
lemma upper_Λ : 0≤Λ:= (tsum_nonneg h.two.1).trans h.two.2.2
lemma cap_clip : p.direct≤1:= by
  have hm := h.metric card_face card_face; rw [if_pos rfl, if_pos rfl] at hm
  refine (le_add_of_nonneg_right (show 0≤∑ i,R.symbol0 i card_face* R.symbol0 i card_face from Finset.sum_nonneg fun i _=>mul_self_nonneg _)).trans hm.le
omit h

variable (hn:4≤n.val) (s : Signed)
include hn h

def pipeB (f : Face (Per n)) : Floor n→ₗ[ℝ]G.Color where
  toFun v:= ∑' i, (R.row f.2 i).1 • curl c s (slotFace (R.row f.2 i).2 f.1) v
  map_add' x y:= by
    have he (v:Floor n): Summable (fun i:ℕ=> (R.row f.2 i).1 • (curl c s (slotFace (R.row f.2 i).2 f.1) v)):= by
      simp_rw [← curl_line c s hn]; exact ellLine_summable R h _ _
    simp_rw [map_add,smul_add]; exact (he x).tsum_add (he y)
  map_smul' k v:= by
    simp_rw [map_smul,smul_comm _ k,tsum_const_smul'']; rfl

lemma pipe_line (f : Face (Per n))(v:Floor n): ellLine R f (Bid.pulled (lift1 (surf c v)) s)=pipeB c R h hn s f v:= by
  unfold ellLine; simp_rw [curl_line c s hn]; rfl
lemma pipe_plain (f:Face (Per n)) : pipeB c R h hn s f (1:Floor n)=0:=by
  change (∑' i, (R.row f.2 i).1 • curl c s (slotFace (R.row f.2 i).2 f.1) (1:Floor n))=0; simp [curl_plain]

variable {hc : ‖c‖=1} {r : ℝ} (hr:0≤r) (hx:r≤1) (hs:r≤σ)
include hc hr hx hs
lemma pipe_felt (f:Face (Per n)) : felt r (affine s 0 f.1) (fieldRow (pipeB c R h hn s f))≤ C*curlPay:= by
  let z(i:ℕ) := |(R.row f.2 i).1| * Real.exp (σ*(R.row f.2 i).2.length)
  let U(i:ℕ) (j:Site n):= (R.row f.2 i).1 • fieldRow (curl c s (slotFace (R.row f.2 i).2 f.1)) j
  have he(i) : felt r (affine s 0 f.1) (U i) ≤ z i*curlPay := by
     unfold U; rw [felt_scale]; apply (mul_le_mul_of_nonneg_left (token_felt (hc:=hc) c s hr hx f.1 _) (norm_nonneg _)).trans; unfold z
     rw [Real.norm_eq_abs, mul_assoc]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); rw [mul_comm (Real.exp (σ*_))]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))) curlPay_nn
  apply le_trans (felt_infinite U hr ((h.rows f.2).2.1.mul_right curlPay) he); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right (h.rows f.2).2.2 curlPay_nn

omit hc hr hx hs

-- weights of indifferent atoms; propagate color entry for asym bounds
section loop
variable (x : Site n)
omit h hn

def play (w:Slot)(i:G.ColorIndex) : Floor n→ₗ[ℝ]ℝ := (innerSL ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ i)).toLinearMap.comp (curl c s (slotFace w x))
lemma play_eq (w:Slot)(i:G.ColorIndex)(v:Floor n) : play c s x w i v= (curl c s (slotFace w x) v) i:= by change inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ i) _ = _; simp only [EuclideanSpace.basisFun_inner]
include hc hr hx
lemma play_pay (w:Slot)(i:G.ColorIndex): felt r (affine s 0 x) (fieldRow (play c s x w i))≤ curlPay * Real.exp (r*w.length) := by
  refine le_trans (b:=felt r (affine s 0 x) (fieldRow (curl c s (slotFace w x)))) ?_ (token_felt (hc:=hc) c s hr hx ..)
  apply Finset.sum_le_sum; intro j _; apply mul_le_mul_of_nonneg_right _ (beam_pos ..).le; unfold fieldRow; simp_rw [Function.comp_apply,play_eq,PiLp.norm_apply_le]

-- lap via ℝ, inner order ok

def atomB (w:Atom G 2) : Block n:= ∑ b:Fin 2→G.ColorIndex, w.coeff b • lap (play c s x (w.leg 0) (b 0)) (play c s x (w.leg 1) (b 1))
omit hc hr hx
include hn
lemma pulse_atom (i : ℕ) (v:Floor n): pulse (atomB c s x (R.loop i)) v v= pair R (Bid.pulled (lift1 (surf c v)) s) x true i := by
  unfold atomB pulse; rw [utter_many]; unfold pair Atom.poly slotAt; simp only [↓reduceIte]; apply Finset.sum_congr rfl; intro j _; rw [utter_scale, show utter (lap _ _) (spur v v)= _ from pulse_lap _ _ v v,Real.inner_apply, Fin.prod_univ_two,curl_line c s hn,curl_line c s hn,play_eq, play_eq,mul_comm ((curl ..) v _)]; -- ambiguity?
lemma atom_plain (i:ℕ) : pulse (atomB c s x (R.loop i)) 1 1=0:= by rw [pulse_atom c R hn s]; simp only [pair,Atom.poly,slotAt,curl_line c s hn, ↓reduceIte,curl_plain,Fin.prod_univ_two]; simp
omit hn
include hr hx hc hs
lemma atom_pay (w:Atom G 2): paid (atomB c s x w) r≤ w.budget σ * curlPay^2:=by
  have he(b:Fin 2→G.ColorIndex): paid (lap (play c s x (w.leg 0) (b 0)) (play c s x (w.leg 1) (b 1))) r ≤ Real.exp (σ*w.length) * curlPay^2:= by
    apply (paid_lap hr (affine s 0 x) _ _).trans
    have h0:0≤curlPay:=curlPay_nn
    refine (mul_le_mul (play_pay (hc:=hc) c s hr hx x _ _) (play_pay (hc:=hc) c s hr hx x _ _) (felt_nn ..) (by positivity)).trans ?_
    rw [Atom.length,Fin.sum_univ_two,Nat.cast_add]; let a:ℝ:=(w.leg 0).length; let b:ℝ:=(w.leg 1).length
    calc _ = Real.exp (r*(a+b))*curlPay^2:= by unfold a b; rw [mul_add,Real.exp_add]; ring
         _ ≤ _:= mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right hs (by positivity))) (sq_nonneg _)
  unfold atomB Atom.budget Atom.magnitude; apply (paid_many ..).trans; rw [Finset.sum_mul,Finset.sum_mul]; refine Finset.sum_le_sum fun b _=>?_;
  rw [paid_scale, mul_assoc (|_|),Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (he b) (abs_nonneg _)

omit hr hx hc hs
def soloB : Block n:= ∑' i, atomB c s x (R.loop i)
variable (hc_: ‖c‖=1) -- avoid assume nontriv for available
include h hc_
lemma loop_available : Summable (fun i=> atomB c s x (R.loop i)):= paid_available (h.two.2.1.mul_right _) (show (0:ℝ) ≤ 0 from le_rfl) (fun i=> atom_pay (hc:=hc_) c s (r:=0) le_rfl zero_le_one h.width.le x (R.loop i))
lemma solo_pay : ∀ (r:ℝ), 0 ≤ r → r ≤ 1 → r ≤ σ →  paid (soloB c R s x) r ≤ Λ * curlPay^2:= by
  intro r hr he hs; apply (paid_all (h.two.2.1.mul_right _) hr (fun i=> atom_pay (hc:=hc_) c s hr he hs x _)).trans; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.two.2.2 (sq_nonneg _)
include hn
lemma pulse_solo (u:Floor n): pulse (soloB c R s x) u u= soloLoop R (Bid.pulled (lift1 (surf c u)) s) x:= by unfold pulse soloB; rw [utter_infinite (loop_available c R h s x hc_)]; exact tsum_congr fun i=> pulse_atom c R hn s x i u -- args for available
lemma solo_plain : pulse (soloB c R s x) 1 1= 0:= by
  unfold pulse soloB; rw [utter_infinite (loop_available c R h s x hc_)]; change (∑' i,pulse (atomB c s x (R.loop i)) 1 1)=0; simp only [atom_plain c R hn s, tsum_zero]
end loop
-- aggregate before any kinetic subtraction; tail estimates are on total local budget
omit h hn -- they are still included? check
variable (β:ℝ)
section stage
include h hn
def bendB (f:Face (Per n)):= p.direct • lap (curl c s f) (curl c s f) + lap (pipeB c R h hn s f) (pipeB c R h hn s f)
def priceB (x: Site n) := (β/2) • (∑ i:PlaqAxes, bendB c R h hn s (x,i)) + soloB c R s x
def spanB := (Fintype.card Signed : ℝ)⁻¹ • (∑ s:Signed, ∑ x:Site n, priceB c R h hn s β x)
def faceValueBill (C : ℝ) := curlPay^2*(1+C^2)
def spanPay (C Λ β:ℝ) := |β/2| * Fintype.card PlaqAxes * faceValueBill C + Λ*curlPay^2
include hr hx hs hc
lemma bend_fee (f:Face (Per n)) : paid (bendB c R h hn s f) r ≤ faceValueBill C:= by
  unfold bendB; refine (paid_add ..).trans ?_
  let a:= affine s (0:Site n) f.1
  have hM:= upper_C R h; have hb0:0≤ curlPay:=curlPay_nn
  have hA0 := curl_felt (hc:=hc) c s hx f
  have hB0 := pipe_felt (hc:=hc) c R h hn s hr hx hs f
  have ha : paid (lap (curl c s f) _) r ≤ curlPay^2 := (paid_lap hr a (curl c s f) (curl c s f)).trans ((mul_le_mul hA0 hA0 (felt_nn ..) hb0).trans_eq (pow_two _).symm)
  have hb : paid (lap (pipeB c R h hn s f) _) r ≤ (C*curlPay)^2 := (paid_lap hr a (pipeB c R h hn s f) (pipeB c R h hn s f)).trans ((mul_le_mul hB0 hB0 (felt_nn ..) (by positivity)).trans_eq (pow_two _).symm)
  rw [paid_scale,Real.norm_of_nonneg p.quadratic_pos.le]; exact (add_le_add ((mul_le_of_le_one_left (paid_nn ..) (cap_clip R h)).trans ha) hb).trans_eq (by unfold faceValueBill; ring)
lemma price_fee (x : Site n): paid (priceB c R h hn s β x) r ≤ spanPay C Λ β:= by
   unfold priceB; apply (paid_add ..).trans; apply add_le_add _ (solo_pay c R h s x hc r hr hx hs)
   rw [paid_scale, mul_assoc]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg (β/2));
   exact le_trans (paid_many _ _ _) ((Finset.sum_le_sum (fun i _=> bend_fee (hc:=hc) c R h hn s hr hx hs (x,i))).trans_eq (by simp))
lemma span_fee : paid (spanB c R h hn β) r ≤ fuel n * spanPay C Λ β:= by
   let N:ℝ:= Fintype.card Signed; have hN:0<N:= Nat.cast_pos.mpr Fintype.card_pos
   have h'(s:Signed): paid (∑ x:Site n, priceB c R h hn s β x) r ≤ fuel n * spanPay C Λ β:=by
      exact le_trans (paid_many _ _ _) ((Finset.sum_le_sum (fun x _=> price_fee (hc:=hc) c R h hn s hr hx hs β x)).trans_eq (by simp [fuel]))
   unfold spanB; rw [paid_scale,Real.norm_of_nonneg (inv_pos.mpr hN).le, (inv_mul_le_iff₀ hN)]
   exact le_trans (paid_many _ _ _) ((Finset.sum_le_sum (fun x _=> h' x)).trans_eq (by simp [N]))

omit hr hs hx hc
lemma pulse_bend (f:Face (Per n))(u:Floor n) : pulse (bendB c R h hn s f) u u=p.direct* ‖faceCurl f (Bid.pulled (lift1 (surf c u)) s)‖^2 + ‖ellLine R f (Bid.pulled (lift1 (surf c u)) s)‖^2 := by
  rw [curl_line c s hn, pipe_line c R h hn s]
  unfold bendB pulse; rw [utter_plus,utter_scale]; change p.direct*pulse _ _ _ + pulse _ _ _=_
  rw [pulse_lap,pulse_lap,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
include hc
lemma price_plain (x:Site n): pulse (priceB c R h hn s β x) 1 1=0:= by
  unfold pulse priceB; rw [utter_plus,utter_scale,utter_many]; have he:= solo_plain c R h hn s x hc; unfold pulse at he; rw [he]
  have hi (i:PlaqAxes): utter (bendB c R h hn s (x,i)) (spur 1 1)=0:= by simpa only [pulse,curl_line c s hn,curl_plain,pipe_line c R h hn s,pipe_plain,norm_zero, zero_pow, OfNat.ofNat_ne_zero,ne_eq,not_false_eq_true,mul_zero,add_zero] using pulse_bend c R h hn s (x,i) 1
  simp [hi]
lemma span_sampling (x: Site n)(u:Floor n): pulse (priceB c R h hn s β x) u u= costPath p R β (Bid.pulled (lift1 (surf c u)) s) x := by
  unfold pulse priceB; rw [utter_plus,utter_scale,utter_many]
  change (β/2)* (∑ i:PlaqAxes, pulse (bendB c R h hn s (x,i)) u u) + pulse _ _ _=_
  rw [pulse_solo c R h hn s x hc u]; simp_rw [pulse_bend]; rfl
lemma span_sampling_all (u:Floor n): pulse (spanB c R h hn β) u u= actualPath (p:=p) R β (surf c u):=by
  unfold pulse spanB actualPath Patch.average; simp_rw [utter_scale,utter_many]; congr 1; exact Finset.sum_congr rfl (fun i _=> Finset.sum_congr rfl fun x _=> span_sampling (hc:=hc) c R h hn i β x u)
lemma span_plain : pulse (spanB c R h hn β) 1 1=0:=by
    unfold pulse spanB; simp_rw [utter_scale,utter_many]; change _ * (∑ s:Signed,∑ x:Site n, pulse (priceB c R h hn s β x) 1 1)= _; have he (s:Signed)(x:Site n): pulse (priceB c R h hn s β x) 1 1=0:= price_plain (hc:=hc) ..; simp [he]
end stage
end YM.MatchingLedger.Spring
