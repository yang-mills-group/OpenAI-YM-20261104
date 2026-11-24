import YM.WilsonComparison.Finite.Covariance
import YM.AlbaMS.Barr.Tears
import YM.MS.Swirl.Came

/-!
# Wick projection on the Master propagator after finite Fourier/sign change

Intertwine the actual, complete MS terminal symbol functional (on its Mini domain)
and the finite-site Wick operation used by the axial-independence/ghost-projection
proofs. Arbitrary rank-bounded insertions, including ghost legs. Both use left
symbol derivatives, not ordinary monomial coefficients, and *exponentiate*
the contraction operator (1/2 included by `Master`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonComparison.Finite
open MS MS.Landau MS.Tone MS.City MS.Orbit MS.Swirl MS.Swirl.Near
open MSBar MSBar.Bric MSBar.Loft MSBar.Inlay MSBar.Cutis MSBar.Cutis.Winter
open Bric.Coil Lattice
open scoped BigOperators Classical
variable {A K R : Type} {p : A → Bool} {r v : ℕ} {G : Gauge} {n : Side}
section Forget
variable [CommRing R]

def symbols (p:A→Bool) (R : Type) [CommRing R] : Coil p R →ₗ[R] Koszul.Raw A R:= (vestry p R).subtype
lemma symbols_v (x:Coil p R) : symbols p R x = ⇑x := rfl
lemma cross_sting (b c : Bool) (z : R) : Bric.sting (b && c) z = MS.Koszul.cross b c * z := by
  cases b <;> cases c <;> simp [MS.Koszul.cross]
lemma symbols_symm (x:Coil p R) : Koszul.Symm p (symbols p R x) := fun l i j k=> by
  rw [symbols_v,x.trusted, cross_sting]
lemma concord_of_symm {x:Koszul.Raw A R} (h:Koszul.Symm p x) : Concord p x := by
  intro l k i j; rw [cross_sting]; exact h l i j k
lemma symbols_limit {x:Coil p R} : Cap x v ↔ MS.Book.Limit (symbols p R x) v := by
  constructor
  · intro h l hl; by_contra! hx; specialize h l hx; omega
  intro h l hl; by_contra! hx; exact hl (h l (by omega))
lemma eq_band (p : A→Bool) (l:List A) : Koszul.degree p l = band p l:= by
  induction l with | nil=> rfl|cons x l IH=>rw [Koszul.degree_cons,band_cons, IH]
lemma symbols_pure {b:Bool} {x:Coil p R} (h : Coil.Tone b x) : Koszul.Pure p b (symbols p R x) := by
  intro l hv; by_contra! hx
  exact hv ((eq_band p l).trans (h l hx))
lemma symbols_D (x:Coil p R) (i:A) : symbols p R (D i x)=Koszul.D i (symbols p R x):= rfl
lemma symbols_plane (x:Coil p R) (i:Bool) : symbols p R (plane i x)=Koszul.sign p i (symbols p R x):= by
  rw [symbols_v]; ext l; rw [polar,cross_sting,Koszul.at_sign,eq_band]; rfl
lemma symbols_mul (x y:Coil p R) : symbols p R (x*y)=Koszul.product p (symbols p R x) (symbols p R y):= by
  ext l; induction l generalizing x y with
  | nil => rw [Koszul.nil_product]; exact tap_mul ..
  | cons a l ih=>
    rw [MS.Koszul.D_eval a (symbols p R _),← symbols_D, Bric.Coil.mulD, map_add,Pi.add_apply,
      ih (D a x) y, ih (plane (p a) x) (D a y)]
    rw [MS.Koszul.D_eval a (Koszul.product p _ _), Koszul.D_product,Pi.add_apply]; rw [symbols_D,symbols_D,symbols_plane]
lemma symbols_put (z:R) : symbols p R (put p z)=Koszul.coin z := rfl
lemma symbols_one : symbols p R 1=Koszul.coin 1 := rfl
end Forget
section Wick
variable [Fintype A]
lemma symbols_touch (L : Cog.Grain A) (x:Coil p ℂ) : symbols p ℂ (touch L Finset.univ x)=Cog.frame L (symbols p ℂ x):= by
  rw [touch_apply,map_sum, fpΩ]
  simp_rw [map_sum,map_smul,symbols_D]
  rfl
lemma symbols_pe (L : Cog.Grain A) (x:Coil p ℂ) : symbols p ℂ (pe L Finset.univ r x)=tep L r (symbols p ℂ x):= by
  rw [pe_apply, tep, LinearMap.smul_apply, map_smul, show falt ℂ r=MS.Puff.Actors.phase r from ?_]
  · congr 1; induction r with|zero=> rfl|succ i IH=> rw [pow_succ',pow_succ',Module.End.mul_apply,Module.End.mul_apply,symbols_touch,IH]
  norm_num [falt,MS.Puff.Actors.phase]

lemma view_symbols (L : Cog.Grain A) (x:Coil p ℂ) (h:FinRank x) :
    View L (symbols p ℂ x)= wither L Finset.univ x []:= by
  have he:=h.choose_spec
  change Shot L (symbols p ℂ x) []= _
  rw [dawn L (symbols_limit.mp he), withers he (by omega : h.choose≤2*h.choose)]
  change effect L h.choose _ []= symbols p ℂ (twig L Finset.univ h.choose x) []
  rw [effect,LinearMap.sum_apply, twig_apply,map_sum]; simp_rw [symbols_pe]
end Wick
section Master
abbrev encodeMomentum := shot Finset.univ fieldChange (legalChange (G:=G) (n:=n))

lemma fourier_view (x : LightQ G n ℂ) (h:FinRank x) : View (Master G n true) (symbols σbranch ℂ (encodeMomentum x))=
    Fritz.eval (fun i j=>((extoll G n 1).hop i j:ℂ)) x := by
  rw [view_symbols]; unfold encodeMomentum; rw [shot_wither _ (fun i _ j _=> (covariance i j).symm) h, shot_nil]
  exact ⟨_,h.choose_spec.shoots⟩
lemma real_view (x : LightQ G n ℝ) (h:FinRank x) : View (Master G n true) (symbols σbranch ℂ (encodeMomentum (Wind ø Complex.ofRealHom x)))=
    ((Fritz.eval (extoll G n 1).hop x:ℝ):ℂ) := by
  rw [fourier_view]
  · change wither (fun i j=> Complex.ofRealHom ((extoll G n 1).hop i j)) _ _ [] = _
    rw [← blown Complex.ofRealHom h]; rfl
  exact ⟨_,Cap.seep _ _ h.choose_spec⟩
end Master
end YM.WilsonComparison.Finite
