import YM.RegulatorIR.Tape.Hound

/-!
# Terminal pole estimate in varying periods

At fixed native terminal side or bounded list of them. Not a continuum IR
infinite-volume claim at fixed mesh. Need ellipt strict along terminal
sequence, *full torus*, variation reaching point with scarce costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Taping
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic Lattice Wilson Geometry Geometry.Field Chart Gauge RG Orb Laplace Tree Forest Step Matrix Prim Binding.Last StopB Uniform Ledger Ledger.Sky
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W:Type}{M : W→ℕ}{n:Page M→Side}
variable {f: Side}
-- curvature costO gain at terminal via literal K

def paid (G:Gauge)(f:Side):ℝ:=by
 by_cases h:Even f.val
 · let P: ℝ:=f.val
   let q:= Carto G 1 P h (show (1:ℝ)*f.val=P from one_mul _);let K:= fmat q q (finer moon)
   have H: Vertex (beneath K):= sunrise (G:=G) h (show (1:ℝ)*f.val=P from one_mul _) |>.symm ▸ (fun i : Horizon G f=>⟨costO_pos i,costO_null i h⟩ : Vertex costO) -- syntax
   exact (literal (spine G f) K (gains H h)).choose
 exact 1
lemma endpoint (G:Gauge)(f:Side) (h:Even f.val):0<paid G f ∧ ∀ x:Meadow G (Cotree f),paid G f*‖x‖^2 ≤ costO (inhabit x):=by
 let q:=Carto G 1 (f.val:ℝ) h (show (1:ℝ)*f.val=_ from one_mul _);let K:= fmat q q (finer moon)
 have hp:beneath K= costO:= sunrise ..;have hz:Vertex (beneath K):=hp.symm ▸ (show Vertex (G:=G) (f:=f) costO from fun i=> ⟨costO_pos _,costO_null i h⟩)
 have He:=literal (spine G f) K (gains hz h) |>.choose_spec; have he:paid G f= (literal (spine G f) K (gains hz h)).choose:=by unfold paid;rw [dif_pos h]
 rw [he,← hp];exact He

section
variable (i : Book G f)

def Hertz (G:Gauge)(f:Side) :ℝ:= ∑ i:Book G f, ‖(pupil i).toContinuousLinearMap‖
lemma hertz_nonneg (G:Gauge)(f:Side):0≤ Hertz G f:= Finset.sum_nonneg fun _ _=> norm_nonneg _
lemma air (x:Meadow G (Cotree f)) : ‖pupil i x‖≤ Hertz G f *‖x‖ := ((pupil i).toContinuousLinearMap.le_opNorm x).trans (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f:=fun i:Book G f=> ‖(pupil i).toContinuousLinearMap‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ i)) (norm_nonneg _))
variable {K : Matrix (Book G f) (Book G f) ℝ}
variable (hc:Vertex (beneath K)) (hp: K.transpose=K) (ht:Even f.val)
lemma passage {e:ℝ}(h:0<e)(hy:∀ x,e*costO x ≤beneath K x) j : ‖axis hc hp ht i j‖ ≤ (Hertz G f / paid G f)*Hertz G f / e:=by
 let A:=polar hc hp ht;let y:= A.inverse (pupil i)
 have hv : e*(paid G f)*‖y‖^2 ≤ pupil i y:=by
    have hh:= (mul_le_mul_of_nonneg_left ((endpoint G f ht).2 y) h.le).trans (hy (inhabit y)); rw [mul_assoc]; apply le_trans hh
    change A.P y y/2 ≤ pupil i y
    rw [show A.P y= pupil i from A.applies _]
    have hz: 0 ≤ pupil i y:=by obtain ⟨a,ha,H⟩:= A.slope; specialize H y; rw [show A.P y=pupil i from A.applies ..] at H; nlinarith
    linarith
 have hz: paid G f * ‖y‖ ≤ Hertz G f/e:=by
    by_cases h₀:y=0; rw [h₀,norm_zero,mul_zero]; exact div_nonneg (hertz_nonneg ..) h.le
    have he':e*paid G f*‖y‖^2 ≤ Hertz G f*‖y‖:= hv.trans ((Real.le_norm_self _).trans (air i y)); rw [sq,mul_comm e,← mul_assoc] at he'; apply (le_div_iff₀ h).mpr; calc
       _ = (paid G f* e*‖y‖):=by ring
       _ ≤ _:= le_of_mul_le_mul_right he' (norm_pos_iff.mpr h₀)
 have he: ‖y‖≤ Hertz G f/e/paid G f:=by apply (le_div_iff₀ (endpoint G f ht).1).mpr; rw [mul_comm]; exact hz
 change ‖pupil j y‖≤ _; exact ((air j y).trans (mul_le_mul_of_nonneg_left he (hertz_nonneg ..))).trans_eq (by ring)
end

namespace Reel
variable {S:Heir n G}(H: Reel S)(L:Meter W)
-- explicit curvature terminal cap lower assumed from K Cover oracle
structure Endings : Prop where
 periods : ∃ v:ℕ,∀ w,(n (Page.finallyW M w)).val≤v
 pay : ∀ w, Billed (H.stem (Page.finallyW M w))
 symw w : let i:=Page.finallyW M w; Layer.Sym (S.maps i) (S.maps i) (H.stem i)
 ellipt : ∃ e: W→ℝ, (∀ w,0<e w) ∧ Poly L (fun w=> ENNReal.ofReal (e w)⁻¹) ∧ ∀ w,let i:= Page.finallyW M w; Ellipt (H.stem i) (e w) (n i) -- ofReal ambiguous precedence assumes ofReal (e w)^-1 want inverse inside. positive can adapt
variable (C:H.Endings L)
include C
lemma lows (q: Side→ℝ≥0∞)(h:∀ u,q u ≠ ⊤): Poly L fun w=>q (n (Page.finallyW M w)) :=by
 obtain ⟨p,hp⟩:=C.periods
 let f (z:ℕ) := if h:0<z then q ⟨z,h⟩ else 0
 have hc z : f z≠⊤:= by unfold f;split; exact h _; exact ENNReal.zero_ne_top
 let c:= (Finset.range (p+1)).sup f; have hz : c≠⊤:= ne_of_lt (Finset.sup_lt_iff (by simp)|>.mpr (fun i _=> lt_of_le_of_ne le_top (hc i)))
 apply (Poly.standard L hz).mono; intro w;let m:=n (Page.finallyW M w)
 change q m≤ c; rw [show q m=f m.val from (by simp [f];rfl)]; exact Finset.le_sup (f:=f) (Finset.mem_range.mpr (Nat.lt_succ_of_le (hp w)))

lemma strength_v (w) {e:ℝ}(h : Ellipt (H.stem (Page.finallyW M w)) e (n (Page.finallyW M w)))(x) : e*costO x ≤ H.spot (Page.finallyW M w) x:=by
 let i:=Page.finallyW M w; have hv : Sym (S.maps i) (S.maps i) (H.stem i):= C.symw w
 change e*costO x≤ beneath (fmat (S.maps i) (S.maps i) _) x; rw [H.realms i]
 rw [H.realms i] at hv; exact muscle _ _ _ h hv (C.pay w) x
lemma potentials : ∃ t:W→ℝ≥0∞,Poly L t ∧ ∀ w, Layer.height (H.feeMarg.endK w) (t w):=by
 obtain ⟨e,h,hp,hz⟩:= C.ellipt
 let q (p:Side):= Hertz G p / paid G p*Hertz G p
 have hi:= (H.lows L C (q:=fun p=> ENNReal.ofReal (q p)) (fun _=> ENNReal.ofReal_ne_top)).mul hp
 refine ⟨_,hi,?_⟩; intro w i j; let p:= Page.finallyW M w;let v:=n p
 change ‖H.vapors p i j‖ₑ≤ ENNReal.ofReal (q v)* _
 have he : ‖H.vapors p i j‖ ≤ q v/e w:= passage _ _ _ _ (h w) (H.strength_v L C w (hz w)) _
 rw [← ofReal_norm]; apply (ENNReal.ofReal_le_ofReal he).trans_eq; rw [div_eq_mul_inv, ENNReal.ofReal_mul]; unfold q; have h0:=hertz_nonneg G v;have hx:= (endpoint G _ (H.even p)).1; change 0 < paid G v at hx; positivity

-- width at requested native terminal side

def toll (Q:ℕ)(f:Side):ℝ≥0∞:= Tariff.amount 1 Q (f.val)
omit C H L in
lemma toll_one (Q:ℕ)(f:Side):1 ≤ toll Q f:= Tariff.amount_unit (by norm_num) _ (by positivity)
omit C H L in
lemma toll_fin (Q:ℕ)(f:Side):toll Q f≠⊤:=by unfold toll Tariff.amount;finiteness
include H
omit C L in
lemma fee_tariff (Q:ℕ)(w:W)(x y : Rest (fun i=>Book G (n i)) w): (S.landQ Q w).road x y≤ toll Q (n (Page.finallyW M w)):=by
 let i:= Page.finallyW M w; let P:= S.P w; let f:=n i;let z:= S.maps i
 change Tariff.amount (S.radius i) Q (Spatial.distance P (z.atO x) (z.atO y))≤ _
 have hP:0<P:= S.hp w; have hv:S.l i≤S.radius i:= le_max_right ..; have hx:=S.hl i
 apply (Tariff.amount_mono (hx.trans_le hv) Q ((min_le_left (Spatial.wheel P _ _) _).trans ((Spatial.halfwidth_le P hP _).trans (show P/2≤P by linarith)) : Spatial.distance P _ _ ≤P)).trans
 have hg : P/S.radius i≤ (f.val:ℝ):=by rw [← show S.l i* (f.val:ℝ)=P from H.phase i]; apply (div_le_iff₀ (hx.trans_le hv)).mpr; rw [mul_comm]; exact mul_le_mul_of_nonneg_left hv (by positivity) -- check rw
 unfold Tariff.amount toll; simp only [Tariff.amount, div_one];gcongr

lemma terminals (Q:ℕ): Beam L (S.landQ Q) H.feeMarg.endK:=by
 obtain ⟨v,hv,h⟩:= H.potentials L C
 have hz:= H.lows L C (toll Q) (toll_fin Q)
 have ht:= H.lows L C (fun n=> (Fintype.card (Book G n):ℝ≥0∞)) (fun _=> by finiteness)
 refine ⟨_,ht.mul (hv.mul hz),?_⟩; intro w
 let f:=n (Page.finallyW M w);let X:=toll Q f; let F:= H.feeMarg.endK w
 have hp(T:Layer (Book G f) (Book G f))(H₀:height T (v w)) z: quota (T z) (fun i=>(S.landQ Q w).road z i)≤↑(Fintype.card (Book G f)) * (v w * X):= by
    rw [quota, tsum_fintype]; apply le_trans (Finset.sum_le_sum (g:=fun _=> v w * X) (fun i _=> mul_le_mul' (H₀ ..) (H.fee_tariff ..))) (le_of_eq ?_); simp
 exact ⟨hp F (h w), hp (Function.swap F) (fun i j=> h w j i)⟩

def feeC (G:Gauge)(Q a b:ℕ)(f:Side): ℝ≥0∞:= quota (charter G f a b) (fun _=>toll Q f)
lemma incurred (Q a b:ℕ): Workday L (S.landQ Q) fun w=> H.feeMarg.haar w a b := by
 have he(g:Side): feeC G Q a b g≠⊤:=by rw [feeC,quota,tsum_fintype]; exact ENNReal.sum_ne_top.mpr (fun _ _=> ENNReal.mul_ne_top (by finiteness) (toll_fin Q g))
 refine ⟨_, H.lows L C _ he,fun w i u=> ?_⟩
 let g:= n (Page.finallyW M w); let T:Packet (Book G g) b:= charter G g a b
 apply le_trans (Stalk.over_le (fun p:Tuple _ b=>p i) T (S.landQ Q w).diameter _) ?_
 exact quota_mono T (fun z=> Tariff.diameter_le _ (toll_one Q g) (fun a b => H.fee_tariff ..))
lemma year (Q a:ℕ): S.Epoch H.feeMarg L Q a := ⟨H.terminals L C _, fun i _ j=> H.incurred L C Q i j, fun _=> little.form (by norm_num)⟩
end Reel
end YM.RegulatorIR.Taping
