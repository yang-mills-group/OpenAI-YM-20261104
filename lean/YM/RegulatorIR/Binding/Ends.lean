import YM.RegulatorIR.Binding.Flags
import YM.PertExtension.PTBills

/-! Terminal ports use the same diagram polynomials. Zeroth contour
coefficient irrelevant for this positive-order connection. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.Field Geometry.End Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Series Series.Radial Series.Tested Diagram.Formal Diagram Diagram.Gaussian Budget Budget.Packet Budget.Layer Budget.Tuple PowerSeries GaussianScore Tree Tree.Forest Step Ledger Ledger.Sky
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical PowerSeries
variable {G:Gauge}{I E:Type}[Fintype E][Fintype I]{f:Side}{s m e:ℕ}

def hover (G:Gauge): Medium G Empty Empty:= ⟨(fun _=> isEmptyElim),(fun _=>0)⟩
abbrev ZeroO (K: Horizon G f→ℝ)(A:Layer (Book G f) (Book G f))(U:Orders (Book G f)) := Clip (F:=0) (V:=Last.shoot f G) (paw K) (hover G) (Embedding.refl _) (Function.Embedding.ofIsEmpty) A 0 U

omit [Fintype I] in
lemma press_zero (T:Packet I 0) (K:Layer I I) : crop (Embedding.ofIsEmpty (α:=Empty)) (draft K T) (Fin.elim0)=T Fin.elim0:=by
 unfold crop;rw [draft]; change symmetry T _= _
 rw [Packet.symmetric_already T (fun e x=> congr_arg T (Subsingleton.elim ..))]; congr 1
lemma ink_empty (f:Orders Empty)(w:Empty→ℝ) r: flavor r w f= PowerSeries.mk fun i=>note (f i 0):=by
 ext1 i;rw [flavor_lo,packed, PowerSeries.coeff_mk,Finset.sum_eq_single_of_mem 0 (show 0∈Finset.range (i+r+1) by simp),render];
 · simp [note,Diagram.word]; congr
 intro j _ he;rw [render]; cases j
 · contradiction
 next j => simp
omit [Fintype I] in
lemma again (U:Orders I): Cluster.present (Embedding.refl I) U=U:= by ext1 e; ext1 r; ext1 x; exact offer_eq _ _ x

namespace RangeR
variable {T V U:Orders (Book G f)} {g:ℝ→ℝ}{κ:Horizon G f→ℝ}
variable {A:Layer (Book G f) (Book G f)}
-- identical scalar used by `vita`
def expect (m:ℕ) (A:Layer (Book G f) (Book G f)) (T V U:Orders (Book G f)) (e:ℕ):ℝ:= note (endHeat m A (logHeat A (T+U) true) V e 0)

lemma tongue (R : RangeR G f κ g s m T V) (h:ZeroO κ A U)(hf: Even f.val):
    Aspiration g (fun i=> coeff i (PowerSeries.X^s*PowerSeries.mk (expect m A T V U))):= by
 have H:= Clip.victory h R.basis (Last.carries hf) R.marks R.inscription
 let X:= apogee R.Val
 let Y:= tip R.Mark
 let E := R.E ⊕ Cotree f
 let D:= manuscript X Y 0; let Q':=manuscript X 1 0
 have hd : D= (PowerSeries.X^s*PowerSeries.mk (expect m A T V U))* Q':=by
    unfold D; rw [show manuscript X Y 0= Q' * _ * _ from H.stamped (0:Meadow G Empty)] -- perhaps rw
    rw [ink_empty (Clip.stencil h m T V)];
    have hv (r) : note (Clip.stencil h m T V r 0)=expect m A T V U r:= by
       unfold Clip.stencil collectO note expect supply; rw [again,again];exact press_zero ..
    simp_rw [hv]; dsimp only [Q']; ring
 have hq : coeff 0 Q'≠0:=by
    unfold Q'; rw [show manuscript X 1 0=PowerSeries.C _ * _ * _ from H.bare 0, coeff_zero_eq_constantCoeff_apply, map_mul,map_mul, ← coeff_zero_eq_constantCoeff_apply,← coeff_zero_eq_constantCoeff_apply,← coeff_zero_eq_constantCoeff_apply, exp_start,mul_one,coeff_zero_C]; exact (mul_pos (Real.exp_pos _) H.awake).ne'
 let d:=fun t:ℝ=> (t^Laplace.dim G E)⁻¹*rightSum R.Val R.Mark t
 let q:=fun t:ℝ=> (t^Laplace.dim G E)⁻¹*rightSum R.Val 1 t
 have he : Aspiration d (fun i=> coeff i D):= by simp_rw [D,manuscript, PowerSeries.coeff_mk];exact wind R.basis R.inscription R.archive2 hf
 have hb : Aspiration q (fun i=> coeff i Q'):= by simp_rw [Q',manuscript, PowerSeries.coeff_mk];exact wind R.basis (shapeOne (G:=G)) R.archive1 hf
 have hs:= he.quotient hb hq; unfold divide Tested.term at hs
 rw [show PowerSeries.mk (fun i=> coeff i D)=D from PowerSeries.ext (fun i=>coeff_mk ..),show PowerSeries.mk (fun i=> coeff i Q')=Q' from PowerSeries.ext (fun i=>coeff_mk ..), hd,mul_assoc, PowerSeries.mul_inv_cancel _ (by rwa [coeff_zero_eq_constantCoeff_apply] at hq),mul_one] at hs
 intro k;obtain ⟨c,hc,hg⟩:= hs k
 refine ⟨c,hc,?_⟩; filter_upwards [hg,eventually_pos] with t ht hr
 convert ht using 1; unfold d q; simp only [Pi.sub_apply, Pi.div_apply]; rw [mul_div_mul_left _ _ (by positivity), R.turn]

lemma LaurentEnd (R:RangeR G f κ g s m T V)(h:ZeroO κ A U)(hf:Even f.val) : Aspiration (fun t=> (t⁻¹)^s*g t) (expect m A T V U) := by
 have hv:∀ i,s > i → coeff i ((PowerSeries.X)^s*PowerSeries.mk (expect m A T V U))=0:=fun i hi=> by rw [coeff_X_pow_mul',if_neg (by omega)]
 convert (R.tongue h hf).shift hv using 1 <;> try rfl
 ext1 i
 rw [coeff_X_pow_mul', if_pos (Nat.le_add_right s i), show s+i-s=i from by omega,coeff_mk]
end RangeR
end YM.RegulatorIR.Binding
