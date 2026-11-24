import YM.MatchingLedger.Hessian.Carry
import YM.MatchingLedger.Hessian.Pipes

/-!
# E activity curvature entries with no hard strip-width assumptions

Average over all sites only after summing supports. Read native halo prices and complete
threshold witness. Wrapping labels quoted at zero holonomy using Exp pricing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Spring
open Function Filter Lattice Wilson RG Exterior Precision Work.F03 Pert Pert.Kinetic
open AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff InnerProductSpace Finset
variable {n : Side} {G : Gauge} (c : G.Color) (A : Activities G n) {p : BudgetPoint} {u : ℝ} {o : Site n} {X : Support n}

def cardB (f : Config G n→ℝ) : Block n:= fun i j=> logHessian f (surf c (spot i)) (surf c (spot j))
lemma pulse_card (f : Config G n→ℝ)(v w:Floor n): pulse (cardB c f) v w= logHessian f (surf c v) (surf c w):= by
  rw [summed (surf c) v,summed (surf c) w]; unfold pulse utter cardB spur; simp only [hessian_eq,map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _=>?_); unfold fieldRow; simp only [Function.comp_apply]; ring

section support
variable {f : Config G n→ℝ} (hc : ‖c‖=1)(hG:G.Simple) (h : p.supBounds o X f u) (hv : p.Regular X f)
local notation "A'" => cardB c f
include hG hv
lemma fly {x y:Site n} (he : x∉X ∨ y∉X) : (cardB c f) x y=0:= by
  have h0 (x) (he:x∉X): Agrees X (surf c (spot x)) (0:Directions G n) := by
    intro i hi _; rw [surf_spot]; have hk : i≠(x,0):= by intro h; subst i; exact he hi
    simp [Pi.single_eq_of_ne hk]
  unfold cardB; rcases he with hx|hx
  · rw [hessian_agrees hG hv (h0 x hx) (show Agrees X _ (surf c (spot y)) from fun _ _ _=> rfl)]; simp [hessian_eq]
  rw [hessian_symm hv, hessian_agrees hG hv (h0 y hx) (show Agrees X _ (surf c (spot x)) from fun _ _ _=> rfl)]; simp [hessian_eq]

local notation "ρ" => p.supportExponent
local notation "cost" => (coverNumber p.B X)
local notation "ℓ" => (cost:ℝ)
variable {r:ℝ} (hr:0≤r)(hz:r*(6*(p.B:ℝ)+2)≤ p.supportExponent/2)
include hc h
lemma leaf_budget (x y:Site n) : ‖(A') x y‖≤ 3*u / p.threshold^2:= by
    have hd (x:Site n) := loose_dir (p:=p) o (surf c (spot x)) zero_lt_one 0 (Nat.zero_le _) (fun i => by simpa only [pow_zero,mul_one] using surf_spot_norm c hc x i)
    simpa only [Real.norm_eq_abs,cardB,one_mul] using (scaled_price hG hv h _ _ zero_lt_one zero_lt_one (hd x) (hd y))
omit hG h hv hc in
lemma reachE (x y:Site n)(hx:x∈X)(hy:y∈ X) (hr:0≤r) (hz:r*(6*(p.B:ℝ)+2)≤ (ρ)/2): beam r x y ≤ Real.exp ((ρ)* (ℓ)/2) := by
  unfold beam; apply Real.exp_monotone; have hx1 := Push.AbsoluteSums.Animals.price_pos p.B X; have hE : 1≤ ℓ := by exact_mod_cast (show 1≤ cost from (hx1.2 ⟨x,hx⟩ : 0<cost))
  have hW : (separation x y:ℝ) ≤ (ℓ)*(6*(p.B:ℝ)+2) := by
     apply le_trans (show _≤ (ℓ)*(4*(p.B:ℝ)+2)+ 2*(p.B:ℝ) from by exact_mod_cast Corona.extent X p.B hx hy); nlinarith only [mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg p.B)]
  have he := mul_le_mul_of_nonneg_left hW hr; refine he.trans ?_; rw [mul_comm (ℓ), ← mul_assoc,mul_comm]; linarith only [mul_le_mul_of_nonneg_right hz (zero_le_one.trans hE)]

def paper (p : BudgetPoint) := 3/p.threshold^2 * (p.B+p.B+1:ℝ)^8 * 8 * p.supportExponent⁻¹^2
omit h hG hv hc in
lemma paper_nn : 0≤ paper p:= by unfold paper; positivity
include hr hz
lemma leaf_fee : paid A' r ≤ paper p * p.mass X u := by
   let e:= Real.exp ((ρ)*(ℓ)/2); let v:=(3*u/p.threshold^2)*e
   have he : Real.exp ((ρ)*(ℓ))=e*e:=by unfold e; rw [← Real.exp_add]; ring_nf
   let D:ℝ:=X.card; have hx(i j : Site n): i∈X→j∈X→‖(A') i j‖*beam r i j≤v:=fun hi hj=> mul_le_mul (leaf_budget c hc hG h hv i j) (reachE i j hi hj hr hz) (beam_pos ..).le (by positivity [h.1])
   have hv':0≤v:=by unfold v e; positivity [h.1]
   have h0 : paid A' r≤ D*(D*v):= by
      unfold paid
      rw [← Finset.sum_subset (Finset.subset_univ X) (fun i _ hi => show ∑ j:Site n, ‖(A') i j‖*beam r i j=0 from Finset.sum_eq_zero (fun j _=> by rw [fly c hG hv (Or.inl hi),norm_zero,zero_mul]))]
      refine (Finset.sum_le_sum (g:=fun _=>D*v) (fun i hi=>?_)).trans_eq (by simp [D])
      rw [← Finset.sum_subset (Finset.subset_univ X) (fun j _ hj=> show ‖(A') i j‖*beam r i j=0 from by rw [fly c hG hv (Or.inr hj),norm_zero,zero_mul])]; exact (Finset.sum_le_sum (fun j hj=>hx i j hi hj)).trans_eq (by simp [D])
   let b:=(p.B+p.B+1:ℝ); have hD : D ≤ (ℓ)*b^4:= by unfold D b; exact_mod_cast (Corona.pays X p.B)
   have hg : (0:ℝ)≤ ℓ:=Nat.cast_nonneg _; have hJ:0≤D:=Nat.cast_nonneg _
   have hw : (ℓ)^2 ≤ 8*(ρ)⁻¹^2 * e:= by
      have hρ:=p.exponent_pos; have ht:=(poly_gate (orderM:=2) (show 0 ≤ (ρ)*(ℓ)/2 from by positivity)); rw [show ((2:ℕ).factorial:ℝ)=2 from by norm_num [Nat.factorial]] at ht; apply le_of_mul_le_mul_left _ (sq_pos_of_pos hρ)
      rw [show (ρ)^2 * (8*(ρ)⁻¹^2 * e)=8*e from by field_simp]; unfold e; linarith only [ht] -- lin normalized powers
   apply h0.trans; have hp:=p.threshold_pos;
   calc _ ≤ ((ℓ)*b^4)*(((ℓ)*b^4)*v) := mul_le_mul hD (mul_le_mul_of_nonneg_right hD hv') (mul_nonneg hJ hv') (by positivity)
        _ = (ℓ)^2*(b^8*v):= by ring
        _ ≤ 8*(ρ)⁻¹^2*e*(b^8*v):= mul_le_mul_of_nonneg_right hw (by positivity [hv'])
        _ = _:=by unfold v b BudgetPoint.mass paper; rw [he]; ring
end support

variable {δ z : ℝ}(hc : ‖c‖=1) (hG:G.Simple) (h:A.Valid p δ z)

def leafB := ∑' i,cardB c (A.E i)

variable {r:ℝ} (hr:0≤r)(hz:r*(6*(p.B:ℝ)+2) ≤ p.supportExponent/2)
include hr hz hc h hG
lemma leafy : Summable (fun i=> cardB c (A.E i)) ∧ paid (leafB c A) r ≤ paper p * (fuel n * δ):= by
    obtain ⟨b,hb,hB,he⟩:= payment_sum h.boundE
    have hh(i) := leaf_fee c hc hG (hb i) (h.regular.smooth i) hr hz; let h' := hB.mul_left (paper p)
    refine ⟨paid_available h' hr hh,(paid_all h' hr hh).trans ?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he paper_nn
omit hr hz
lemma leaf_identity (v:Floor n) : pulse (leafB c A) v v= Eread (A:=A) (surf c v):= by unfold pulse leafB; rw [utter_infinite (leafy c A hc hG h (r:=0) le_rfl (by rw [zero_mul]; exact div_nonneg p.exponent_pos.le zero_le_two)).1]; exact tsum_congr fun i=> pulse_card ..

-- upper with geomE (same currency as wave). only `m^3` claimed.

local notation "m" => Full.mesh n

omit hc h hG in
lemma umbrella {p:BudgetPoint} : ((100*(4*(p.B:ℝ)+2)/((2*Real.pi)*p.supportExponent))^3*18)/p.threshold^2 ≤ geomE p := by
    unfold geomE; nth_rw 1 [mul_add (1/p.threshold^2)]; apply le_trans (le_of_eq ?_) (le_add_of_nonneg_left ?_); rotate_left; positivity; ring

variable (hn:4≤ n.val)
include hn
lemma wraps : ‖pulse (leafB c A) 1 1‖ ≤ m^3*geomE p*(fuel n*δ):= by
    rw [leaf_identity c A hc hG h]; obtain ⟨b,hb,hB,he⟩:= payment_sum h.boundE
    let v:= surf c (1:Floor n); let g:= m^3*geomE p
    have hp:0≤g:=by unfold g geomE; have := Full.mesh_pos (n:=n); have := p.threshold_pos;have:=p.exponent_pos;have π:=Real.pi_pos; positivity
    have hh(i) : ‖logHessian (A.E i) v v‖≤ g*p.mass (A.reg i).support (b i):= by
       have hb':=p.loMass (A.reg i).support (b i) (hb i).1
       have h0 := (hb i).1.trans hb'
       by_cases hX: Nonwrapping (A.reg i).support (A.reg i).site
       · have hv(x:Site n) : IsAffineDirection x v:= by
           refine ⟨fun j=>if j=0 then c else 0,fun _ _=>0,fun e=>?_⟩; unfold v; rw [surf_apply c _ e.1 e.2]; simp
         rw [h.regular.vanish i hX _ _ (hv _) (hv _),norm_zero]; exact mul_nonneg hp h0
       have hD(j) := loose_dir (p:=p) j v zero_lt_one 0 (Nat.zero_le _) (fun i=> by simpa only [Pi.one_apply,norm_one,pow_zero,mul_one] using surf_norm c hc (1:Floor n) i)
       simp_rw [one_div, inv_inv] at hD
       apply (sparse_fee c hc hG (h.regular.smooth i) (A.reg i).site v hn hX (A.reg i).anchor (hb i) (hD _)).trans
       apply mul_le_mul_of_nonneg_right _ h0; refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (umbrella (p:=p)) (by exact pow_nonneg Full.mesh_pos.le _)); ring
    unfold Eread; refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hh (hB.mul_left g)
    refine ((Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hh (hB.mul_left g)).tsum_le_tsum hh (hB.mul_left g)).trans ?_; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he hp
end YM.MatchingLedger.Spring
