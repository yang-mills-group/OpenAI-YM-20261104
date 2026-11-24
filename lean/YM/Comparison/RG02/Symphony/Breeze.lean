import YM.Comparison.RG02.Symphony.Table
/-!
# Per full-wave coefficient test of a canonical Offer

 Keep actual P budget through torus polarization. May include mismatches between
 i+j=0 vs not. Up to 4 in the budget explicitly for full tensor pairing (R_G loops
 uses full Hessian, not halved, and phase grids with every sample normalized
 per-cell). This is still at exactly one mesh side. Full growing limits not claimed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly
open Matrix Push.Loops Laurent Bloch YM.Work.F05
open scoped Topology BigOperators Classical ContDiff
-- Fintypes with DecidableEq, Matrix carrier change only norm requests. Bounds entrywise.
variable {G:Gauge} {c:Side} {π:SpecK G} {N:ℕ→Side}
namespace Breeze
-- X evaluated on p preserving same sign (FieldAction vs - log). entry test includes price
-- every i j. no requiring that off-plane errors already zero.
def Rule (A:Matrix (BondKey G c) (BondKey G c) ℝ)(s:SpecK G)(T:ℝ):Prop := ∀ (k:Site c) i p, Matches p i→ ∀ u v, ‖sample (linksGrid G c) (linksGrid G c) (cmat A) k i u v - (if k+i=0 then s p u v else 0)‖ ≤ T
variable (Q : Matrix (BondKey G c) (BondKey G c) ℝ) (k i:Site c) (u v:Axes G)
local notation "Π" A=> Matrix.toLinearMap₂' ℂ (S₁:=ℂ) (S₂:=ℂ) A
local notation "L"=> linksGrid G c
-- columns
private def column (p:Site c)(u:Axes G): BondKey G c → ℂ := fun x=> cell p (L x).1 * ((Pi.single u 1):Axes G→ℂ) (L x).2
private lemma line (p:Site c)(u:Axes G) : column p u= plane L p *ᵥ Pi.single u 1:= funext fun x=> (plane_apply _ _ _ x).symm
private def wind (p:Site c)(u:Axes G)(z:ℂ): BondKey G c → ℝ := fun x=> (column p u x * z).re
private def bowl (u:Axes G)(z:ℂ): TypeFace 1→ G.ColorIndex→ℂ := fun i j=> (Pi.single u z : Axes G→ℂ) (axisEquiv.symm i,j)
private lemma wind_is (p:Site c)(u:Axes G)(z:ℂ) : chartEquiv G c (wind p u z)= wave p (bowl u z):= by
    funext x; rcases x with ⟨x,i⟩; obtain ⟨i,rfl⟩:=axisEquiv.surjective i; rw [coord_map,chartEquiv_apply]; ext j
    change ( (cell p x * ((Pi.single u 1 : Axes G→ℂ) (i,j)))*z).re=(cell p x * (Pi.single u z : Axes G→ℂ) (axisEquiv.symm (coord i),j)).re
    rw [show axisEquiv.symm (coord i)=i from Equiv.symm_apply_apply ..]; by_cases h:(i,j)=u <;> simp [h]
private lemma wind_paid (u:Axes G){z:ℂ}(h:‖z‖≤1) : ∀ i j, ‖bowl u z i j‖≤1:= by intro i j; unfold bowl; by_cases he:(axisEquiv.symm i, j)=u <;> simp [*]
private lemma real (x y:BondKey G c→ℝ) : (Π(cmat Q)) (cvec x) (cvec y)= Complex.ofReal (x ⬝ᵥ (Q*ᵥ y)) := by rw [Matrix.toLinearMap₂'_apply',cmat_mulVec,cvec_dot]
private lemma quadrature (k:Site c)(u:Axes G) : column k u=cvec (wind k u 1) + Complex.I • cvec (wind k u (-Complex.I)):= by
    ext1 j
    change _=(↑(((column k u j)*1).re):ℂ)+Complex.I * (↑(((column k u j)* ( -Complex.I)).re):ℂ)
    rw [mul_one, mul_neg, Complex.neg_re, Complex.mul_I_re,neg_neg, mul_comm Complex.I,Complex.re_add_im]
local notation "V"=> (Fintype.card (Site c):ℝ)
private lemma pair (k i:Site c)(u v:Axes G) : (V : ℂ) * sample L L (cmat Q) k i u v =(Π(cmat Q)) (column k u) (column i v) := by
    let a:= (Π (sample L L (cmat Q) k i)); let p:Axes G→ℂ:=Pi.single u 1; let q:Axes G→ℂ:=Pi.single v 1
    have he : sample L L (cmat Q) k i u v=a p q:= by unfold a p q; rw [Matrix.toLinearMap₂'_apply',mulVec_single_one,single_dotProduct, one_mul]; rfl
    rw [he]; unfold a; rw [Push.Loops.sample, line k u,line i v,toLinearMap₂'_apply', toLinearMap₂'_apply', Matrix.smul_mulVec,dotProduct_smul]; simp only [smul_eq_mul]; rw [← mul_assoc, site_card]; push_cast; rw [mul_inv_cancel₀ (pow_ne_zero _ (side_ne c)),one_mul,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
variable {T:ℝ} (h:∀ (i j:Site c)(σ τ:TypeFace 1→G.ColorIndex→ℂ),(∀ x y,‖σ x y‖ ≤ 1) → (∀ x y,‖τ x y‖≤ 1) → let L₀:= (chartEquiv G c).symm; |L₀ (wave i σ) ⬝ᵥ (Q*ᵥ L₀ (wave j τ))| ≤ (Fintype.card (Site c):ℝ)*T)
include h
private lemma whole {a b:ℂ} (hp:‖a‖≤1)(hv:‖b‖≤1) : ‖(Π(cmat Q)) (cvec (wind k u a)) (cvec (wind i v b))‖ ≤ V*T := by
   have he:= h k i _ _ (wind_paid u hp) (wind_paid v hv); dsimp only at he; rw [← wind_is,← wind_is, ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply] at he; rw [real]; simpa using he
lemma pointed : ‖sample L L (cmat Q) k i u v‖ ≤ 4*T := by
    have hi : ‖(-Complex.I)‖≤1:= by simp
    have hh : ‖(1:ℂ)‖≤1:= by simp
    have hz : 0 < V := Nat.cast_pos.mpr Fintype.card_pos
    apply le_of_mul_le_mul_left (a:=V) ?_ hz
    rw [← Real.norm_of_nonneg hz.le,← Complex.norm_real,← norm_mul, Breeze.pair]; rw [quadrature k u, quadrature i v]
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]
    let a:= wind k u 1; let b:=wind k u (-Complex.I); let e:= wind i v 1; let f:= wind i v (-Complex.I)
    let I:=Complex.I; have hI:‖I‖=1:=Complex.norm_I
    let q(x y: BondKey G c→ℝ):= (Π (cmat Q)) (cvec x) (cvec y); change ‖q a e+I • q b e + I •(q a f + I • q b f)‖ ≤ ‖(V:ℂ)‖ *_
    have hu {x y:ℂ}{t p:ℝ}(he:‖x‖≤t)(hx:‖y‖≤p) : ‖x+I•y‖≤ t+p:= (norm_add_le ..).trans (add_le_add he (by rw [norm_smul, hI,one_mul]; exact hx))
    apply (hu (hu (show ‖q a e‖≤V*T from Breeze.whole Q k i u v h hh hh) (show ‖q b e‖≤V*T from whole Q k i u v h hi hh)) (hu (show ‖q a f‖≤V*T from whole Q k i u v h hh hi) (show ‖q b f‖≤V*T from whole Q k i u v h hi hi))).trans_eq; rw [Complex.norm_real,Real.norm_of_nonneg hz.le]; ring
omit h
lemma accepts_zero (h:Compares L L (cmat Q) π 0) : Rule Q π 0 := by
    intro k i p hp u v; split
    next hh=> rw [eq_neg_of_add_eq_zero_left hh,h.exact_sample hp, sub_self,norm_zero]
    next hh=> rw [h.off k i hh, Matrix.zero_apply, sub_self, norm_zero]
lemma shifted {Q' : Matrix (BondKey G c) (BondKey G c) ℝ}{t:ℝ} (h:Rule Q π t) (he: ∀ k i u v,‖sample L L (cmat Q') k i u v‖≤T) : Rule (Q+Q') π (t+T) := by
   intro k i p hp u v; rw [map_add, sample_add,Matrix.add_apply,add_sub_right_comm]; exact (norm_add_le ..).trans (add_le_add (h k i p hp u v) (he k i u v))
lemma referral {H: ∀ i, Matrix (BondKey G (N i)) (BondKey G (N i)) ℝ} {b:ℕ→ℝ}(he: ∀ i,Rule (H i) π (b i))(hv: Tendsto b atTop (𝓝 0))(hp: ∀ p:Momentum, star p=p → ContinuousAt π p) : LinkMirror H π:= by
   intro p f k h hf hh; apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro v
   let y i:= N i; let z(i:ℕ):=sample (linksGrid G (y i)) (linksGrid G (y i)) (cmat (H i)) (-(k i)) (k i)
   have h₁ : Tendsto (fun j=> z j i v- π (f j) i v) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _=> norm_nonneg _) (fun j=> by simpa only [neg_add_cancel, if_pos] using he j (-(k j)) (k j) (f j) (hh j) i v) hv)
   have h₂:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ((hp p h).tendsto.comp hf) i) v
   simpa only [Function.comp_apply,sub_add_cancel,zero_add,z] using h₁.add h₂
end Breeze
end YM.Comparison.RG02.Symphony
