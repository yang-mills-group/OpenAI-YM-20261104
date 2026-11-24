import YM.UVExt.ProfileRay
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.UVExt.FormalThermal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Finite-mesh contour control of real-variable jets for bodies of thermal form

One side of the interpolation mesh may have to change with the underlying real field; allows data-dependent switch of the BOUND only, without differentiating such a switch. No UV path hypothesis here.
-/
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.EnergyRay.Thermal
open Filter Set Finset ContinuousLinearMap
open scoped Topology ContDiff BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def nodes (u : ℂ) (δ : ℝ) {n : ℕ} (i k : Fin (n+1)) : ℝ := u.re + δ*(i.val:ℝ)-δ*(k.val:ℝ)
def side {p q : ℝ} (s : ℝ) {n : ℕ} (i : Fin (n+1)) := if 0 ≤ s then s+i.val*q else s-i.val*q
variable {n : ℕ} (u : ℂ) (b : ℝ) {δ D:ℝ} (hδ:0<δ) (hp:(4*(n+1):ℕ)*δ ≤ u.re) (hd:|u.im|≤ δ)
local notation "J" => Fin (n+1)
local notation "r" => nodes u δ (n:=n)
def speed (n:ℕ) := (4:ℝ)*(n+2)
include hδ
lemma nodes_sep : ∀ i j:J,i ≠ j → ∀ k:J, δ ≤ ‖r i k-r j k‖ ∧ δ ≤ ‖r k j-r k i‖ := by
    intros i j hij k
    have hh : |(i.val:ℝ)-(j.val:ℝ)| ≥ 1 := by
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h|h
        · have ho := show (i.val:ℝ)+1 ≤ j.val by exact_mod_cast Nat.add_one_le_of_lt h
          rw [abs_of_nonpos (by linarith)]; linarith
        · have ho := show (j.val:ℝ)+1 ≤ i.val by exact_mod_cast Nat.add_one_le_of_lt h
          rw [abs_of_nonneg (by linarith)]; linarith
    have hL := mul_le_mul_of_nonneg_left hh hδ.le
    rw [show r i k-r j k=δ*(i.val-j.val) by unfold nodes; ring, show r k j-r k i=δ*(i.val-j.val) by unfold nodes; ring,Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
    rw [mul_one] at hL; exact ⟨hL,hL⟩
lemma room (i : Fin (n+1)) : δ*i.val ≤ (n:ℝ)*δ := mul_comm (n:ℝ) δ ▸ (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hδ.le)
include hp
lemma nodes_pos (i j:J) : 3*u.re/4 ≤ r i j := by
    have hz:=room hδ j; push_cast at hp; have h:0≤δ*i.val:= by positivity
    unfold nodes; linarith
include hd in
lemma nodes_distance (i j:J) : ‖u - (r i j:ℂ)‖ ≤ speed n*δ := by
    apply (le_trans (Complex.norm_le_abs_re_add_abs_im (u-r i j))); simp only [Complex.sub_re, Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero]
    have hi:= room hδ i; have hj:= room hδ j; have h:0≤δ*i.val ∧ 0≤δ*j.val:=⟨by positivity, by positivity⟩
    unfold nodes speed; cases le_total (δ*i.val) (δ*j.val) with
    | inl h => rw [abs_of_nonneg (by linarith)]; linarith
    | inr h => rw [abs_of_nonpos (by linarith)]; linarith
include hd
lemma ice (i k:J) : ‖u‖ ≤ (1+speed n*δ/u.re)^2 * r i k := by
  have hU:0<u.re:=(show 0<(↑(4*(n+1):ℕ):ℝ)*δ by positivity).trans_le hp
  let a:=speed n*δ/u.re; have ha:a≥0:=by unfold a speed; positivity
  let w:=r i k; have hw:3/4*u.re ≤ w:=by rw [show 3/4*u.re=3*u.re/4 by ring]; exact nodes_pos u hδ hp i k
  have hh:= (norm_sub_norm_le u (w:ℂ)).trans (nodes_distance u hδ hp hd i k); rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<w by linarith)] at hh
  have hR : w*a*2 ≥ speed n*δ := by
    rw [show speed n*δ = a*u.re by unfold a; rw [div_mul_cancel₀ _ (ne_of_gt hU)]]
    nlinarith
  dsimp [w,a] at *; nlinarith [sq_nonneg (a),mul_nonneg (sq_nonneg a) (show 0<w by linarith).le]

abbrev cap (n:ℕ) (k : ℝ) := speed n^n * k
omit hp hδ hd
inductive Form where
 | coal (size : ℕ)
 | soot
 | plain
def grade : Form → ℕ
 | .coal n => n
 | .soot => 1
 | .plain => 0
private lemma speed_large : 1≤speed n := by unfold speed; norm_cast; omega

variable {b A : E→ℝ} {d : ℕ} {x : E}
variable (f : ℂ → E → ℂ) (g : ℝ→ E→ ℝ)
def Fits (t : Form) : Prop := match t with
 | .coal k => ∃ b A : E→ℝ, (∀ (z:ℂ) i,f z i=(Primitive.thermal (A i) (b i) k).run z) ∧ ∀ (z:ℝ), 0<z → ∀ i, f z i=(g z i:ℂ)
 | .soot => ∃ b : E→ℝ, (∀ (z:ℂ) i,f z i=(Primitive.split (b i)).run z) ∧ ∀ (z:ℝ), 0<z → ∀ i, f z i=(g z i:ℂ)
 | .plain => ∃ A : E→ℝ, (∀ (z:ℂ) i,f z i=(A i:ℂ)) ∧ ∀ (z:ℝ),0<z → g z=A
-- have to assume smooth b through needed order OR representation is locally read as zero at the probes. keep b as witness.
structure CoalAt (x : E) (n k : ℕ) (f : ℂ → E → ℂ) (b : E → ℝ): Prop where
   heat : ∃ A : E→ℝ, ∀ (z:ℂ) v, f z v=(Primitive.thermal (A v) (b v) k).run z
   mask : ContDiffAt ℝ n b x ∨ ∀ z, f z=ᶠ[𝓝 x] 0
   realNews : ∀ (z:ℝ),0<z → ∀ i, f z i=(g z i:ℂ)

include hp hδ hd
lemma glance {W : ℝ→ℝ} (d : ℕ) {a : ℝ}
   (hS : 0≤a)
   (h : ∀ i j:J, ConnectedActivityE6.Blaze.Brush n (W (r i j)) a (g (r i j)) x) (H : CoalAt g x n d f b): ConnectedActivityE6.Blaze.Brush n (speed n^n*((1+speed n*δ/u.re)^d)* (∑ i:J, (W (r i 0)+W (r 0 i)))) a (f u) x := by
 obtain ⟨⟨A,hA⟩,hM,hG⟩:= H
 have hU:0<u.re:=(show 0<(↑(4*(n+1):ℕ):ℝ)*δ by positivity).trans_le hp
 let k (i:J):= if 0≤b x then r i 0 else r 0 i
 have hk i:0<k i:= by unfold k; split <;> linarith [nodes_pos u hδ hp i (0:J),nodes_pos u hδ hp (0:J) i]
 have hw : 0 ≤ ∑ i:J,(W (r i 0)+W (r 0 i)) := sum_nonneg (fun i _=> add_nonneg (h i 0).nonneg (h 0 i).nonneg)
 rcases hM with hM|hM
 swap; · have hV : (ConnectedActivityE6.Blaze.Brush n 0 a (0 : E→ℂ) x) := by change _root_.YM.ConnectedActivityE6.Blaze.Brush n 0 a (fun _=>0) x; simpa using (ConnectedActivityE6.Blaze.Brush.certified (k:=n) (x:=x) hS (0:ℂ))
         exact (hV.shimmy (hM u)).climb (mul_nonneg (by positivity [speed_large (n:=n)]) hw) le_rfl
 let F z v:= (A v:ℂ)*Complex.exp (z*(b v)); let t z := Complex.exp (Complex.log z*((d:ℂ)/2))
 have he z : f z = fun v=>t z*F z v := by ext v; rw [hA z v]; unfold Primitive.run; dsimp [F,t]; rw [Complex.exp_add]; apply mul_left_comm
 have ht {z:ℝ} (hz:0<z) : t z = (Real.sqrt z:ℂ)^d := by
   have ht := Primitive.standard 1 0 d z hz; unfold Primitive.run at ht; simp only [Complex.ofReal_zero, mul_zero,one_mul,add_zero,Complex.ofReal_one,Real.exp_zero] at *; exact (by rw [mul_one] at ht; exact ht)
 have hF {j} (hj:j≤n) : ∀ i:J, ContDiffAt ℝ j (fun v=>(Real.sqrt (k i)^d:ℂ)*F (k i) v) x := by
     intro i; rw [← ht (hk i),← he]; have hB:= hG _ (hk i); rw [funext hB]; apply Complex.ofRealCLM.contDiff.contDiffAt.comp x
     unfold k; split <;> apply ContDiffAt.of_le ((h _ _).smooth) (by exact_mod_cast hj)
 have fee : ‖t u‖=Real.sqrt ‖u‖^d := by
    have hh := Primitive.thermal_cost 1 0 d u hU
    rw [Primitive.standard 1 0 d u.re hU] at hh
    unfold Primitive.run at hh; unfold t
    simp only [Complex.ofReal_zero,mul_zero,one_mul,add_zero,Real.exp_zero, Complex.ofReal_one,mul_one] at *
    simp only [Complex.norm_real,_root_.norm_pow,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hh
    rwa [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Real.sqrt_pos.mpr hU).ne')] at hh
 -- same effect for each j via n+1 samples.
 have lemmaJ (j : ℕ)(hj:j≤n) :
    let w:= (1+speed n*δ/u.re)^d
    ContDiffAt ℝ j (F u) x ∧ ‖iteratedFDeriv ℝ j (fun z=>t u*F u z) x‖≤w*speed n^n*(∑ i:J, ‖iteratedFDeriv ℝ j (fun z=>(Real.sqrt (k i):ℂ)^d*F (k i) z) x‖):= by
      refine Thermal.thermal_response (A:=fun i=>(A i:ℝ)) x (fun u v=>rfl) _ (hM.of_le (by exact_mod_cast hj)) k (Fintype.card_fin _) hj hδ ?_ ?_ (by positivity [speed_large (n:=n)]) ?_ hk ?_ (hF hj) fee
      · intro i j hij; unfold k; split
        next=> exact (nodes_sep u hδ i j hij 0).1
        next=> exact (nodes_sep u hδ j i hij.symm 0).2
      · intro i; unfold k; split <;> exact nodes_distance u hδ hp hd _ _
      · intro i; unfold k; split <;> exact ice u hδ hp hd _ _
      intro i; unfold k nodes; split
      next h => simpa using mul_nonneg (show 0≤δ*(i.val:ℝ) by positivity) h
      next h => simpa using mul_nonpos_of_nonneg_of_nonpos (show 0≤δ*(i.val:ℝ) by positivity) (not_le.mp h).le
 obtain ⟨HV,-⟩:=lemmaJ n le_rfl
 rw [he u]; refine ⟨contDiffAt_const.mul HV, hS,fun j hj=> (lemmaJ j hj).2.trans ?_⟩
 rw [mul_comm (speed _ ^ _),mul_assoc ((1+speed n*δ/u.re)^d* speed n^n)]
 apply mul_le_mul_of_nonneg_left _ (by positivity [speed_large (n:=n)]); rw [sum_mul]
 refine sum_le_sum fun i hi=> ?_
 rw [← ht (hk i),← he, funext (hG _ (hk i))]
 have h' h₁ h₂ := Complex.ofRealLI.norm_iteratedFDeriv_comp_left (h h₁ h₂).smooth (i:=j) (show (j:ℕ∞ω)≤n from by exact_mod_cast hj)
 by_cases hy:0≤b x
 · simp only [k,if_pos hy]; change ConnectedActivityE6.Blaze.normJ j (Complex.ofRealLI ∘ _) x ≤ _
   rw [ConnectedActivityE6.Blaze.normJ,h' i 0]; exact ((h i 0).climb (le_add_of_nonneg_right ((h 0 i).nonneg)) le_rfl).order j hj
 simp only [k,if_neg hy]; change ConnectedActivityE6.Blaze.normJ j (Complex.ofRealLI ∘ _) x ≤ _
 rw [ConnectedActivityE6.Blaze.normJ, h' 0 i]
 exact ((h 0 i).climb (le_add_of_nonneg_left ((h i 0).nonneg)) le_rfl).order j hj
def cash (W : ℝ→ℝ) := W u.re + speed n^n*(∑ i:J,(W (r i 0)+W (r 0 i)))
def deck := 1+(speed n)*δ/u.re

omit hδ hp hd in
lemma pure {Z : ℝ→ℝ} (d : ℕ) (h : ∀ i,0≤Z i) (hp : 0≤deck (n:=n) u (δ:=δ)) : speed n^n*(deck (n:=n) u (δ:=δ))^d*(∑ i:J,(Z (r i 0)+Z (r 0 i))) ≤ cash (n:=n) u (δ:=δ) Z*(deck (n:=n) u (δ:=δ))^d :=
 le_trans (by ring_nf; exact le_rfl) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (h _)) (pow_nonneg hp _))

lemma soot_jets {W:ℝ→ℝ} {x : E} {a:ℝ} {f:ℂ→E→ℂ} {g:ℝ→E→ℝ} (h : ∀ i j:J, ConnectedActivityE6.Blaze.Brush n (W (r i j)) a (g (r i j)) x) (hS : 0≤a) (hh : Fits f g .soot) : ConnectedActivityE6.Blaze.Brush n (cash (n:=n) u (δ:=δ) W*(deck (n:=n) u (δ:=δ))^2) a (f u) x := by
 obtain ⟨b,hb,hX⟩:=hh
 have hv : nodes u δ (0:J) (0:J)=u.re := by simp [nodes]
 have hU : 0 < u.re := (show 0 < (↑(4*(n+1):ℕ):ℝ)*δ by positivity).trans_le hp
 have h0:=h 0 0; rw [hv] at h0
 have hC : 0≤cash u (δ:=δ) (n:=n) W := add_nonneg h0.nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans speed_large) n) (sum_nonneg (fun (i:J) (_:i∈Finset.univ)=> add_nonneg (h i 0).nonneg (h 0 i).nonneg)))
 have heat (z:ℝ)(h:0<z)v : Real.exp (z*(b v))=1+g z v := by have hx:=hX z h v; rw [hb z v] at hx; change Complex.exp ((z:ℂ)*(b v)) - 1=_ at hx; push_cast at *; exact Complex.ofReal_injective (by push_cast; exact sub_eq_iff_eq_add'.mp hx)
 let F(z:ℂ)(v:E):=Complex.exp (z*b v)
 have hB:ContDiffAt ℝ n b x := by
   have hLog v : b v = u.re⁻¹*Real.log (1+g u.re v) := by rw [← heat u.re hU v,Real.log_exp,← mul_assoc,inv_mul_cancel₀ hU.ne',one_mul]
   rw [funext hLog]; exact contDiffAt_const.mul (ContDiffAt.log (contDiffAt_const.add h0.smooth) (by rw [← heat u.re hU x]; exact (Real.exp_pos _).ne'))
 have he z: f z = fun v=>F z v-1 := funext (hb _)
 have hSmooth z: ContDiffAt ℝ n (F z) x := Complex.contDiff_exp.contDiffAt.comp x (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x hB))
 rw [he]; refine ⟨(hSmooth u).sub contDiffAt_const,hS,?order⟩
 intro j hJ
 rcases j with (_|j)
 · rw [ConnectedActivityE6.Blaze.normJ, norm_iteratedFDeriv_zero,pow_zero,mul_one]; unfold F; apply (Primitive.split_cap _ hU _).trans
   rw [show Complex.exp (↑u.re*↑(b x))-(1:ℂ)=(g u.re x : ℝ) by simpa only [hb,Primitive.run] using (hX u.re hU x),Complex.norm_real]
   have h₁ : ‖u‖ / u.re ≤ deck (n:=n) (δ:=δ) u ^2 := (div_le_iff₀ hU).mpr (by unfold deck; simpa only [hv] using ice u hδ hp hd (0:J) (0:J))
   apply (mul_le_mul h₁ (h0.bound.trans ?_) (norm_nonneg _) (by positivity [h₁])).trans_eq (mul_comm _ _)
   unfold cash; exact le_add_of_nonneg_right (mul_nonneg (pow_nonneg (zero_le_one.trans speed_large) n) (sum_nonneg (fun i _=> add_nonneg (h i 0).nonneg (h 0 i).nonneg)))
 · have hEq (z : ℂ) : iteratedFDeriv ℝ (j+1) (f z) x=iteratedFDeriv ℝ (j+1) (F z) x := by rw [he z, fun_iteratedFDeriv_sub_apply ((hSmooth z).of_le (by exact_mod_cast hJ)) contDiffAt_const,iteratedFDeriv_succ_const,Pi.zero_apply, sub_zero]
   let k (i:J) := if 0≤b x then r i 0 else r 0 i
   have hK i: 0<k i:= by unfold k; split <;> linarith [nodes_pos u hδ hp i (0:J),nodes_pos u hδ hp (0:J) i]
   have hF {j} (hj:j≤n) : ∀ i:J, ContDiffAt ℝ j (fun v=>(Real.sqrt (k i)^0:ℂ)*F (k i) v) x := fun i => by rw [pow_zero]; exact contDiffAt_const.mul ((hSmooth _).of_le (by exact_mod_cast hj))
   suffices hL: ‖iteratedFDeriv ℝ (j+1) (fun z=>F u z) x‖≤speed n^n*(∑ i:J, ‖iteratedFDeriv ℝ (j+1) (f ↑(k i)) x‖) by
     rw [ConnectedActivityE6.Blaze.normJ, show (fun z=> F u z-1)=f u from (he _).symm,hEq u]; apply hL.trans
     let S0 := speed n^n * ∑ i:J,(W (r i 0)+W (r 0 i))
     have hs0 : 0≤S0 := mul_nonneg (by positivity [speed_large (n:=n)]) (sum_nonneg (fun _ _=> add_nonneg (h _ _).nonneg (h _ _).nonneg))
     have ht0 : 1≤(deck (n:=n) (δ:=δ) u)^2 := one_le_pow₀ (le_add_of_nonneg_right (by unfold speed; positivity))
     apply le_trans (b:=S0*a^(j+1)) _ ?_
     swap; · apply mul_le_mul_of_nonneg_right _ (by positivity); unfold cash; change _ ≤ (W u.re+S0)*_
             apply le_trans (le_add_of_nonneg_left h0.nonneg) (le_mul_of_one_le_right (add_nonneg h0.nonneg hs0) ht0)
     unfold S0; rw [mul_assoc (speed _ ^ _)]; -- Wait goal speed*sum ≤ sum..., after rw ...
     apply mul_le_mul_of_nonneg_left _ (by positivity [speed_large (n:=n)]); rw [sum_mul]
     apply sum_le_sum; intro i _
     simp_rw [funext (hX _ (hK i))]; by_cases hx:0≤b x <;> simp only [k,if_pos,if_neg,ite_false,hx] <;> change ConnectedActivityE6.Blaze.normJ (j+1) (Complex.ofRealLI ∘ _) _ ≤ _
     · rw [ConnectedActivityE6.Blaze.normJ, Complex.ofRealLI.norm_iteratedFDeriv_comp_left (h i 0).smooth (by exact_mod_cast hJ)]
       exact ((h i 0).climb (le_add_of_nonneg_right (h 0 i).nonneg) le_rfl).order _ hJ
     · rw [ConnectedActivityE6.Blaze.normJ, Complex.ofRealLI.norm_iteratedFDeriv_comp_left (h 0 i).smooth (by exact_mod_cast hJ)]
       exact ((h 0 i).climb (le_add_of_nonneg_left (h i 0).nonneg) le_rfl).order _ hJ
   have hR : ContDiffAt ℝ (j+1) (F u) x ∧ ‖iteratedFDeriv ℝ (j+1 : ℕ) (fun z=> (1:ℂ)*F u z) x‖≤ (1 + speed n * δ / u.re)^0*speed n^n*(∑ i:J, ‖iteratedFDeriv ℝ (j+1:ℕ) (fun z=>(Real.sqrt (k i):ℂ)^0 * F (k i) z) x‖) := by
      refine Thermal.thermal_response (A:=fun v:E=>(1:ℝ)) x (fun u v=>by unfold F; simp) _ (hB.of_le (by exact_mod_cast hJ)) k (Fintype.card_fin _) hJ hδ ?_ ?_ (by positivity [speed_large (n:=n)]) ?_ hK ?_ (hF hJ) (by simp : ‖(1:ℂ)‖= _)
      · intro i j hij; unfold k; split
        next=> exact (nodes_sep u hδ i j hij 0).1
        next=> exact (nodes_sep u hδ j i hij.symm 0).2
      · intro i; unfold k; split <;> exact nodes_distance u hδ hp hd _ _
      · intro i; unfold k; split <;> exact ice u hδ hp hd _ _
      · intro i; unfold k nodes; split
        next h => simpa using mul_nonneg (show 0≤δ*(i.val:ℝ) by positivity) h
        next h => simpa using mul_nonpos_of_nonneg_of_nonpos (show 0≤δ*(i.val:ℝ) by positivity) (not_le.mp h).le
   simp only [pow_zero,one_mul] at hR; simp_rw [hEq] -- adjust
   exact hR.2
end YM.UVExt.EnergyRay.Thermal
