import YM.AlbaMS.Barr.Tree
/-!
# axial tree pick & covariance law

Jac point basis with uniform footprint all colors. Compute Wick line for tree
variables without any ghost or antifield. Lattice gauge parameter later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Barr.Axial
open Set Function Filter IsNilpotent Matrix Odom Token
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Tune Odom Lattice Nexus Loft Cutis Cutis.Winter
variable {E I :Type*}[Fintype E][Fintype I][DecidableEq E][DecidableEq I]
open Shunt
variable {G : Gauge}{n: Side} (G) {Ω: Net E I}
abbrev cuts (s:Finset E): Finset (Flit G E) := s ×ˢ (Finset.univ:Finset G.ColorIndex)
structure Window (n:Side) where
  s : Finset (Foil n)
  left : Matrix (Nail n true) (Foil n) ℝ
  w : Shunt (gradD n) s left
lemma Truce (h:Even n.val) : Nonempty (Window n):=by obtain ⟨Q,V,h⟩:=obtainS (gradD n) (longU n)ᵀ (guest h); exact ⟨⟨Q,V,h⟩⟩
namespace Window
variable {G} (P:Window n)
def partner (a:ℝ):= (a^3)⁻¹ • dotC G P.left
variable {A:Precision.ChartRatio G}(hp:Precision.LocalRatio A){a:ℝ}
lemma womb (h:Even n.val)(ha:0<a): Shunt (phys (Root G A n true hp) a).X (cuts G P.s) (P.partner (G:=G) a) :=by
  apply Shunt.scale (X:=(waveLots _).X) _ _ _ (mul_inv_cancel₀ (by positivity : a^3≠0)) -- matrix expected
  rw [gradLots hp h]; constructor
  · unfold dotC; rw [chip_prod,P.w.one,chip_one]
  · rintro ⟨i,c⟩ hi ⟨j,d⟩; unfold dotC; rw [chip_prod]; change ite (c=d) _ _= (_:Matrix (Env G n) _ ℝ) _ _; dsimp only; rw [P.w.root _ (show i∈P.s from (Finset.mem_product.mp hi).1)]; by_cases ht:c=d<;> simp [ht,Matrix.one_apply]
  rintro ⟨i,c⟩ ⟨j,d⟩ hh; have he:j∉P.s:=fun ht=> hh (Finset.mem_product.mpr ⟨ht,Finset.mem_univ _⟩); simp only [dotC,chip,P.w.zero _ j he, ite_self, Matrix.of_apply] -- maybe simp order
-- tree complement. `Root.a` bookkeeping, Area. verify actual Hess positive, no non-gauge zero boson.
def safeCov (hp:Precision.LocalRatio A)(a:ℝ): Fritz (Env G n) (Sand G n) ℝ:= torc (gain G n a) (phys (Root G A n true hp) a).X (P.partner a)
lemma safe_core (h:Even n.val)(ha:0<a) : (P.safeCov hp a).Fund (phys (Root G A n true hp) a):= torc_right _ _ (P.womb hp h ha) (owner hp h ha).toNormal
lemma peg_to (i:Env G n)(h:Even n.val)(ha:0<a)(hi:i.1∈P.s) (j:Env G n):(P.safeCov hp a).H i j=0:= (P.womb hp h ha).torcH _ (Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩) _
lemma root_to (i:Env G n)(h:Even n.val)(ha:0<a)(hi:i.1∉P.s)(j:Sand G n):(P.safeCov hp a).U i j=0:= (P.womb hp h ha).zero j i (fun hv=> hi (Finset.mem_product.1 hv).1)
lemma price_co (u:Env G n →ℝ)(h:Even n.val)(ha:0<a)(hu:∀ i,i.1∈P.s→u i=0): (P.safeCov hp a).H*ᵥ ((phys (Root G A n true hp) a).Z *ᵥ u) = u:=by
  let L:=phys (Root G A n true hp) a; let T:=P.safeCov hp a; have he : T.H*L.Z=1-L.X*T.U.transpose:= eq_sub_of_add_eq' (by rw [← show L.Z.transpose=L.Z from L.Z_sym]; exact (P.safe_core hp h ha).resonance)
  have ht: T.U.transpose *ᵥ u=0:=by
    ext1 x; apply Finset.sum_eq_zero; intro i _; by_cases hb:i.1∈P.s; · change T.U _ _* u i=0; rw [hu i hb]; exact MulZeroClass.mul_zero _
    exact (congr_arg (·*u i) (P.root_to hp i h ha hb x)).trans (zero_mul _)
  change T.H*ᵥ (L.Z *ᵥ u) = u; rw [Matrix.mulVec_mulVec,he, Matrix.sub_mulVec, Matrix.one_mulVec,← Matrix.mulVec_mulVec u, ht, Matrix.mulVec_zero, sub_zero]
lemma positive (h:Even n.val)(ha:0<a)(u:Env G n →ℝ)(he:u≠0)(hu:∀ i,i.1∈P.s→u i=0): 0<u ⬝ᵥ ((phys (Root G A n true hp) a).Z *ᵥ u):=by
  have H:=(owner hp h ha).root; nth_rw 1 [← star_trivial u]; refine lt_of_le_of_ne (H.dotProduct_mulVec_nonneg u) fun hx=> he ?_; nth_rw 1 [← P.price_co hp u h ha hu]; rw [(H.dotProduct_mulVec_zero_iff u).1 hx.symm, Matrix.mulVec_zero]
end Window
end YM.MSBar.Barr.Axial
