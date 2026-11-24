import YM.OPE.Therm.CorePatch
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
/-!
# Multipay one signature in each small pocket

Each draw redone only from interior links, its own (usually unobserved) patch law.
Costs Hoeffding at finite α. Trustees not needed. DLR circumtoll later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Portolan
open Function Set Filter RG Lattice Wilson MeasureTheory Cells House Cradle
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n:Side} {G:Gauge} {U V : Config G n}
local notation "𝒞" => Config G n
local notation "E" => Edge (Site n)
local notation "η" => prior G n
local notation "Ex"=> Real.exp
variable {W f: Config G n → ℝ} {X Y:Finset (Edge (Site n))}
lemma tower (h:X ⊆ Y)(hf:Envelope f)(U:𝒞): press Y (press X f) U= press Y f U:= by
   let F V:= f (meld Y V U);
   have ht V: press X f (meld Y V U)=press X F V:= by
      refine integral_congr_ae (Eventually.of_forall fun W=> congr_arg f (funext fun i=>?_)); unfold meld; by_cases hx:i∈X
      · simp [hx,h hx]
      by_cases hY:i∈Y<;> simp [hx,hY]
   unfold press; -- unfolded too much
   change (∫ V,press X f (meld Y V U)∂η)= ∫ V,F V∂ η; simp_rw [ht]; exact fresh X (enclosed hf (meld_meas measurable_id measurable_const))
lemma ledger (z:ℝ){X:Finset E}{W f:𝒞→ℝ}(h:Envelope W)(hw:∀ U,0≤ W U)(he:Envelope f)(hf:∀ U, ‖f U‖≤1)(hg:∀ U,press X (fun V=>f V*W V) U=0)(U:𝒞) :
    press X (fun V=> Ex (z*f V)*W V) U ≤ Ex (z^2/2) * press X W U:= by
   let b:=Real.cosh z; let a:=Real.sinh z; let c:=Ex (z^2/2)
   have ht V: Ex (z*f V) ≤ c+a * f V:= by
      rw [mul_comm]; exact (Real.exp_mul_le_cosh_add_mul_sinh (hf V) z).trans (by unfold a c; rw [mul_comm (f V)]; exact add_le_add_left (Real.cosh_le_exp_half_sq _) _)
   let F V:= c* W V; let Y' V:= a*(f V* W V)
   have hF:Envelope F:=Envelope.mul (Envelope.const _) h; have hY: Envelope Y':=Envelope.mul (Envelope.const _) (he.mul h)
   have hh:(fun V=> Ex (z*f V)*W V)≤ fun V=>F V+Y' V:= fun V=> (mul_le_mul_of_nonneg_right (ht V) (hw V)).trans_eq (by unfold F Y'; ring)
   refine (press_mono X (((Envelope.mul (Envelope.const z) he).exp).mul h) (hF.add hY) hh U).trans_eq ?_
   rw [press_add X hF hY]; have ht' : press X Y' U=a*0:=by rw [press]; change (∫ V, a* _ ∂η)=_; rw [integral_const_mul]; exact congr_arg (a*·) (hg U)
   rw [ht',mul_zero,add_zero]; exact integral_const_mul c (fun V=> W (meld X V U))
lemma party {A:Type*}{X:A→Finset (Edge (Site n))}(z:ℝ)(J:Finset A)(h:Envelope W)(hW:∀ U,0≤ W U)(U:𝒞)
    (f:A→ Config G n→ℝ)(he:∀ i∈J,Envelope (f i))(hf:∀ i∈J,∀ U, ‖f i U‖≤1)(ha:∀ i∈J, X i⊆Y)(hb: ∀ i∈J,∀ j∈J,i≠j→ stills (X i) (f j))(hg:∀ i∈J,∀ U, press (X i) (fun V=> f i V*W V) U=0) :
    press Y (fun V=> (∏ i∈J, Ex (z*f i V))*W V) U ≤ (Ex (z^2/2))^(J.card) * press Y W U:= by
   induction J using Finset.induction_on with
   | empty=> simp only [Finset.prod_empty,one_mul,Finset.card_empty,pow_zero,le_refl]
   | insert i J hi ih=>
      let B(U:𝒞):=∏ i∈J,Ex (z*f i U); let a:= Ex (z^2/2); simp only [Finset.forall_mem_insert] at he hf ha hb hg;
      have hB: Envelope B:= branch _ _ fun i hi=> ((Envelope.const _).mul (he.2 i hi)).exp
      have hm: stills (X i) B:= fun U V hu=> Finset.prod_congr rfl fun j hj=> by rw [hb.1.2 j hj (fun H=> hi (H ▸ hj)) U V hu]
      have hF:= ((Envelope.const z).mul he.1).exp; have hi':= ih he.2 hf.2 ha.2 (fun i hi=> (hb.2 i hi).2) hg.2
      have hP(U:𝒞) := ledger z h hW he.1 hf.1 hg.1 U
      let L U:= (Ex (z*f i U)* W U)* B U; let R U:= W U* B U; let K U:= a*(R U); have hL: Envelope L:= (hF.mul h).mul hB; have hR: Envelope R:= h.mul hB; have hK : Envelope K:= (Envelope.const a).mul hR
      have hx : ∀ U, press (X i) L U ≤ press (X i) K U:=by
         intro V; rw [show K=(fun U=> (a*W U)*B U) from funext fun U=> (mul_assoc _ _ _).symm]; unfold L; rw [pressmul (h:=hm),pressmul (h:=hm)]; unfold press; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_right (hP V) (Finset.prod_nonneg fun _ _=> (Real.exp_pos _).le)
      simp only [Finset.card_insert_of_notMem hi,pow_succ' _ J.card,mul_assoc]
      simp_rw [Finset.prod_insert hi]
      rw [show (fun V=> Ex (z*f i V)*B V*W V)=L from funext fun V=> mul_right_comm ..]
      apply le_trans ?_ (mul_le_mul_of_nonneg_left hi' (Real.exp_pos _).le)
      rw [← tower ha.1 hL]; refine (press_mono Y (held_mass _ hL) (held_mass _ hK) hx U).trans_eq ?_; rw [tower ha.1 hK,show K=(fun U=> a*(B U* W U)) from (by ext U; unfold K R; rw [mul_comm _ (W U)])]; exact integral_const_mul a (fun V=> B (meld Y V U)* W (meld Y V U))
variable (T:Tiling n){R:Rep G n}{r:ℕ}{q:ℕ}{τ C a:ℝ} (P : Site n → Finset (Edge (Site n))) (W:Site n→ Config G n→ℝ)
def value (J:T.Cell→ Finset (Site n))(z:ℝ)(i:T.Cell)(U:𝒞):= ∑ j∈J i, z* W j U
def fare (J:T.Cell→ Finset (Site n))(z:ℝ)(i:T.Cell): ℝ:= (J i).card*(z^2/2)
lemma lodge (hv:T.kind=.site)(h:Stove.Chart R r C a)(z:ℝ)(he:∀ i, Attempt R r τ q i (W i) (P i))(J:T.Cell→ Finset (Site n))(hf:∀ i,J i⊆lease T i (parcel R r q)) (hz:∀ i, ((J i:Set (Site n))).Pairwise (fun x y=>q+q < separation x y)) :
    Programs T R r τ (value T W J z) (fare T J z):= by
   have ha(x): Envelope (W x):=⟨(he x).hb,1,(he x).unitBound⟩
   refine ⟨fun i U V hp=>?_,fun i=>?_,fun i=>?_,fun i U=>?_⟩
   · unfold value; apply Finset.sum_congr rfl; intro j hj; exact congr_arg (z*·) ((he j).warm U V (hp.mono fun _ hx=> House.holds T (room_bill T hv (hf i hj) hx)))
   · unfold fare; positivity
   · exact Envelope.sum _ _ fun j=> (Envelope.const z).mul (ha j)
   have hT := party (X:=P) (Y:=edges T i) z (J i) (cell_env T τ h i) (fun _=>cell_nonneg ..) U W (fun i _=> ha i) (fun i _=> (he i).unitBound) (fun j hj=> (he j).trunks.trans (room_bill T hv (hf i hj))) (fun x hx y hy hxy=> spares (he y).warm (Disjoint.mono_right (he x).trunks ((orbits (s:=q) (t:=q) (hz i hx hy hxy)).symm))) (fun j hj=> approved T hv h (hf i hj) (he j))
   unfold fare; rw [Real.exp_nat_mul]; unfold press vigor value; simp_rw [Real.exp_sum, mul_comm (cell T R r τ i _)]; exact hT
end YM.OPE.Therm.Portolan
