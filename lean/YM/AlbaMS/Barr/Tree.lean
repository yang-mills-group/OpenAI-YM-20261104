import YM.AlbaMS.Barr.Dose

/-!
# Axial linear tree slice certification

Works on graph Nett, actual incidence with or without no root (latter impossible). `Shunt`
means a set of link bonds selecting a complete independent minor for the based
ghost in the specified kinetic conventions. Use this rank definition of tree-cert,
which is what the tree gauge at the trivial orbit needs. No graph-theoretic claim
about arbitrary choices not certified. Use Matrix basis argument to construct at
least one. Nonlinear Faddeev Jacobian before fixing these links not evaluated.
With compressed H on Root to exactly this chart verify. Atmosphere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Barr.Axial
open Set Function Filter IsNilpotent Matrix Odom Token
open scoped BigOperators Classical Topology Matrix
open Bric Coil Inlay Inlay.Net Tune Odom Lattice Nexus Loft Cutis Cutis.Winter
variable {X Gc E B R S:Type*}[CommRing R][CommRing S][Fintype E][Fintype B][DecidableEq E][DecidableEq B]
-- Φ basis from tree ordered. partner Δ root identities.
structure Shunt (X:Matrix E B R)(Q:Finset E)(Y:Matrix B E R): Prop where
 one : Y*X=1
 root : ∀ i∈Q,∀ j,(X*Y) i j=(1:Matrix E E R) i j
 zero i j : j∉Q→ Y i j=0
lemma obtainS (X:Matrix E B ℝ)(Y:Matrix B E ℝ)(h:Y*X=1):∃ Q V,Shunt X Q V:=by
  let b (i:B) : B→ℝ:= Pi.single i 1
  let R:=fun i:E=> X i; have hu: Submodule.span ℝ (Set.range R)=⊤:= by
    apply Submodule.eq_top_iff'.mpr; intro x
    let a:=Submodule.span ℝ (Set.range R); have he j : b j=∑ i:E,Y j i • R i:=by
      funext i; rw [Finset.sum_apply]; change _ = (Y*X) j i; rw [h,Matrix.one_apply]; simp [b,Pi.single_apply,eq_comm]
    rw [show x=∑ i:B,x i • b i from ?_]; apply a.sum_mem; intro i _; rw [he]; exact a.smul_mem _ (a.sum_mem fun i _=> a.smul_mem _ (Submodule.subset_span (Set.mem_range_self _)))
    funext i; simp [Finset.sum_apply,b,Pi.single_apply]
  obtain ⟨ι,p,hp,hS,hW⟩:=exists_linearIndependent' ℝ R; letI : Finite ι:= Finite.of_injective p hp; letI : Fintype ι:= Fintype.ofFinite _ -- need finite instance provided by hp
  let V : Module.Basis ι ℝ (B→ℝ):=Module.Basis.mk hW (hS.trans hu).ge
  let Z:= Matrix.of fun (i:B)(e:E)=> ∑ j:ι, if e=p j then V.repr (b i) j else 0
  let s:=Finset.univ.image p
  have he (i:B)(a:ι) : Z i (p a)= V.repr (b i) a:=by simp [Z,hp.eq_iff]
  have hg (i:B)(a:E)(h:a∉s): Z i a=0:=by refine Finset.sum_eq_zero fun j _=> ?_; rw [if_neg]; rintro rfl; exact h (Finset.mem_image.mpr ⟨_,Finset.mem_univ j,rfl⟩); -- fix
  have hl (a:ι): V a=X (p a):=Module.Basis.mk_apply hW _ _
  refine ⟨s,Z,⟨?_, ?_, hg⟩⟩; · ext i j; rw [Matrix.mul_apply, ← Finset.sum_subset (s₁:=s) (Finset.subset_univ _) (fun v _ hv=> by rw [hg i v hv]; exact MulZeroClass.zero_mul _),Finset.sum_image]; swap;exact fun _ _ _ _ h=>hp h; simp_rw [he,← hl]; have h:=congr_fun (V.sum_repr (b i)) j; rw [Finset.sum_apply] at h; refine Eq.trans h ?_; simp [b,Pi.single_apply,eq_comm,Matrix.one_apply]
  rintro i hi k; obtain ⟨e,he',rfl⟩:=Finset.mem_image.1 hi; by_cases ht:k∈s
  · obtain ⟨v,_,rfl⟩:=Finset.mem_image.1 ht; rw [Matrix.mul_apply,Matrix.one_apply]; simp_rw [he,← hl];
    let L := V.coord v; change (∑ i:B, V e i * L (b i))=_; rw [show (∑ i:B,V e i*L (b i))= L (V e) from ?_,Module.Basis.coord_apply,Module.Basis.repr_self]; by_cases h:e=v<;>simp [h,hp.eq_iff];
    nth_rw 2 [show V e=∑ i:B, V e i • b i from ?_];rw [map_sum]; simp_rw [map_smul]; rfl; funext j; simp [b,Finset.sum_apply,Pi.single_apply]
  rw [Matrix.mul_apply]; simp_rw [hg _ k ht]; simp [show ¬ p e=k from fun ha=> ht (ha ▸ hi)]

namespace Shunt
variable (P:Fritz E B R)(U:Lot E B R){X:Matrix E B R}{Y:Matrix B E R}{Q:Finset E}
lemma scale (h:Shunt X Q Y)(a b:R)(ha:a*b=1): Shunt (a • X) Q (b • Y) where
 one:=by rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul,ha,one_smul,h.one]
 root i hi j:=by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,ha,one_smul,h.root _ hi _]
 zero i j hj:= by simp [Matrix.smul_apply,h.zero _ _ hj]
lemma ringmap (h:Shunt X Q Y)(A:R→+*S): Shunt (X.map A) Q (Y.map A) where
 one:=by rw [← Matrix.map_mul,h.one,Matrix.map_one _ A.map_zero A.map_one]
 root i hi j:=by rw [← Matrix.map_mul, Matrix.map_apply,h.root _ hi _]; by_cases hi:i=j<;> rw [Matrix.one_apply,Matrix.one_apply] <;> simp [hi]
 zero i j hj:=by simp [h.zero _ _ hj]
abbrev lp (X : Matrix E B R)(Y: Matrix B E R): Matrix E E R:= 1-X*Y
lemma zeroX (h:Shunt X Q Y): lp X Y*X=0:=by rw [lp,Matrix.sub_mul,Matrix.one_mul,Matrix.mul_assoc,h.one,Matrix.mul_one,sub_self]
lemma left0 (h:Shunt X Q Y)(i)(hi:i∈Q)(j:E): lp X Y i j=0:=by simp [lp,h.root _ hi j]
lemma eye (h:Shunt X Q Y){j:E}(hj:j∉Q)(i): lp X Y i j=(1:Matrix E E R) i j:=by unfold lp; simp only [Matrix.sub_apply,Matrix.mul_apply,h.zero _ _ hj,mul_zero,Finset.sum_const_zero,sub_zero] -- may need _ cast

def torc (X : Matrix E B R)(Y : Matrix B E R): Fritz E B R where
 H:=lp X Y*P.H*(lp X Y)ᵀ
 U:= Yᵀ
 symm i j:=by let Z:=lp X Y*P.H*(lp X Y)ᵀ; exact congr_fun (congr_fun (show Zᵀ=Z by unfold Z; rw [transpose_mul, transpose_mul,P.H_t,transpose_transpose,Matrix.mul_assoc]) j) i
lemma torc_right (h:Shunt U.X Q Y)(hi:P.Normal U): (torc P U.X Y).Fund U where
 long:=by rw [torc,transpose_transpose]; exact h.one
 resonance:=by unfold torc; simp only [transpose_transpose, Lot.Z_sym];
               rw [Matrix.mul_assoc (lp U.X Y*P.H)]; rw [show (lp U.X Y)ᵀ*U.Z=U.Z from ?_, Matrix.mul_assoc,hi.sub_inv, Matrix.mul_sub, Matrix.mul_one, show lp U.X Y * _=0 from (by unfold Fritz.boom; rw [← Matrix.mul_assoc,h.zeroX,Matrix.zero_mul]),sub_zero,lp,add_sub_cancel]
               rw [lp,transpose_sub,transpose_one, Matrix.sub_mul, Matrix.one_mul,transpose_mul,Matrix.mul_assoc]; rw [show U.Xᵀ*U.Z=0 from ?_, Matrix.mul_zero,sub_zero]; nth_rw 1 [← U.Z_sym]; rw [← transpose_mul,hi.nilg, transpose_zero]
lemma torcH (h:Shunt X Q Y){i:E}(hi:i∈Q)(j:E): (torc P X Y).H i j=0:=by change (lp X Y * P.H * (lp X Y)ᵀ) i j=0; rw [Matrix.mul_assoc]; simp [Matrix.mul_apply,h.left0 i hi] -- fix
end Shunt
end YM.MSBar.Barr.Axial
