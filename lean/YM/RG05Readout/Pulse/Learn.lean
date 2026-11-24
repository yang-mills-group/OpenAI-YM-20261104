import YM.RG05Readout.Test.Common
import Mathlib.LinearAlgebra.Dual.Lemmas
/-! Joint Body product. Compute ring via reading directional derivatives.
Representation is ordinary repeated jets, uses EXACT coordinate Levers.
No off-lattice extension.A future grammar can choose other monomial
 coordinates but must transform derivative weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Pulse
open Tensor Analysis Function Filter Set MeasureTheory Native
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}
section jet
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
-- print directional slot on arbitrary jet Body.Scaled ℝ
abbrev vectorB (d:ℕ)(u:E4) : ↥(Orb d)→ₗ[ℂ]ℂ where
   toFun x:= Tensor.diagonal x.val u
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
abbrev tube {d:ℕ}(b : Letter d) : ↥(Orb (depth b)) →ₗ[ℂ]ℂ:= LinearMap.proj (R:=ℂ) (φ:=fun _=>ℂ) b.snd ∘ₗ (writeC _).toLinearMap
lemma connector (k:Letter d) : ∃ c:E4→₀ℂ, tube k= ∑ i ∈ c.support,c i • vectorB (depth k) i:= by
    let y:= vectorB (depth k); let z:= tube k; have h:⨅ i, LinearMap.ker (y i) ≤ LinearMap.ker z:=by
       intro f hf; suffices he:f=0 by rw [he]; exact Submodule.zero_mem _
       have ht: ∀ i,(y i) f=0:=(Submodule.mem_iInf _).1 hf
       exact Subtype.ext (Tensor.ext_diag _ _ (show Sym _ from f.property) (fun _ _=> rfl) (funext ht))
    obtain ⟨c,hc⟩:= Finsupp.mem_span_range_iff_exists_finsupp.mp (FiniteDimensional.mem_span_of_iInf_ker_le_ker h); exact ⟨c,hc.symm⟩
noncomputable def ink (k:Letter d)(u:E4):ℂ:= ((connector k).choose) u* (↑((depth k).factorial:ℝ)⁻¹:ℂ)
noncomputable def paint (k:Letter d):Finset E4:=((connector k).choose).support
lemma sample (k:Letter d) (x:E4)(f:Body) : readJ k x f= ∑ i∈ paint k, ink k i*Tensor.diagonal (iteratedFDeriv ℝ (depth k) f.val x) i:=by
    change tube k (records x (depth k) f)=_; rw [(connector k).choose_spec,LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _
    change ((connector k).choose i)* Tensor.coeff f.val (depth k) x (fun _=> i)=_
    unfold ink; simp only [← mul_assoc,Tensor.coeff, Tensor.diagonal,smul_apply,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]
abbrev smoothP (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E]: Submodule ℂ (E→ℂ):= {
    carrier:={t|ContDiff ℝ ∞ t}
    zero_mem':= (contDiff_const (c:=(0:ℂ)) (E:=E) (𝕜:=ℝ) (n:=∞))
    add_mem' := fun {a b} ha hb => ContDiff.add (f:=a) (g:=b) (show ContDiff ℝ ∞ a from ha) (show ContDiff ℝ ∞ b from hb)
    smul_mem' := fun c a ha=> ContDiff.const_smul (f:=a) c (show ContDiff ℝ ∞ a from ha) }
abbrev Complexion (E:Type*)[NormedAddCommGroup E][NormedSpace ℝ E]:=↥(smoothP E)
local notation "X"=> Complexion E
lemma lit (f:Complexion E)(k:ℕ): ContDiff ℝ k f.val := (show ContDiff ℝ ∞ f.val from f.property).of_le (WithTop.coe_le_coe.mpr le_top)
lemma lamp (f:Complexion E)(x:E): ContDiffAt ℝ ∞ f.val x := (show ContDiff ℝ ∞ f.val from f.property).contDiffAt
noncomputable def one (u:E): X →ₗ[ℂ] X where
    toFun z:= ⟨D u z.val,show ContDiff ℝ ∞ (D u z.val) from contDiff_iff_contDiffAt.mpr (fun x=> dSmooth (lamp z x) u (by simp))⟩
    map_add' f g:= Subtype.ext <| funext fun x=> by
        change fderiv ℝ (f.val+g.val) x u=fderiv ℝ f.val x u+fderiv ℝ g.val x u; rw [fderiv_add (lit f 1|>.contDiffAt.differentiableAt (x:=x) one_ne_zero) (lit g 1|>.contDiffAt.differentiableAt one_ne_zero)]; rfl
    map_smul' a f:=Subtype.ext <| funext fun x=> by
         change fderiv ℝ (a • f.val) x u=a • fderiv ℝ f.val x u; rw [fderiv_const_smul (lit f 1|>.contDiffAt.differentiableAt (x:=x) one_ne_zero)]; rfl
noncomputable def tires (u:E) : ℕ→ X→ₗ[ℂ] X
    | 0=> LinearMap.id
    | k+1=> tires u k ∘ₗ one u
lemma rim_flat (u:E)(n:ℕ)(x:E)(f:X): (tires u n f).val x= Tensor.diagonal (iteratedFDeriv ℝ n f.val x) u:=by
    induction n generalizing f with
    | zero => change f.val x=_; simp only [Tensor.diagonal,iteratedFDeriv_zero_apply]
    | succ n ih=> rw [tires,LinearMap.comp_apply,ih]; unfold Tensor.diagonal; rw [show (fun _:Fin (n+1)=>u)=Fin.cons u (fun _=>u) by ext1 i; refine Fin.cases ?_ (fun j=> ?_) i<;>rfl, Analysis.cons_inner ((lit f _).contDiffAt)] ;rfl
abbrev pie (f g:X)(n:ℕ)(x:E):Prop:= iteratedFDeriv ℝ n f.val x=iteratedFDeriv ℝ n g.val x
lemma pie_one (u:E){x:E}{f g:X}(h:pie f g (k+1) x): pie (one u f) (one u g) k x:=by
    ext1 v; have he(p:X):iteratedFDeriv ℝ _ (one u p).val x v= _:= (Analysis.cons_inner (lit p _|>.contDiffAt) u v).symm; rw [he,he,h]
lemma pie_tires (u:E){f g:X}{x:E}(h:pie f g (k+n) x): pie (tires u k f) (tires u k g) n x:=by
    induction k generalizing f g with
    | zero=> rw [zero_add] at h; exact h
    | succ k ih=> rw [show k+1+n=k+n+1 by omega] at h; exact ih (pie_one u h)
noncomputable def fork (r:ℝ)(x:E):X →ₗ[ℂ] X where
    toFun p:= ⟨fun u=> p.val (x+r • u), ContDiff.comp (show ContDiff ℝ ∞ p.val from p.property) (contDiff_const.add (contDiff_id.const_smul r))⟩
    map_add' _ _:=rfl
    map_smul' _ _:=rfl
lemma leanG (r:ℝ)(x:E)(u:E)(p:X): one u (fork r x p)=(↑r:ℂ) • fork r x (one u p):= Subtype.ext <| funext fun y=> by
    let A(z:E):=x+r • z; have hi: HasFDerivAt A (r • ContinuousLinearMap.id ℝ E) y:= (hasFDerivAt_id y|>.const_smul r).const_add x
    change fderiv ℝ (p.val ∘ A) y u=(↑r:ℂ)* (fderiv ℝ p.val (A y) u); rw [(((lit p 1).contDiffAt.differentiableAt (x:=A y) one_ne_zero).hasFDerivAt.comp y hi).fderiv]; change fderiv ℝ p.val (A y) (r • u)=_; rw [map_smul]; rfl -- real complex?
lemma tire_fork (r:ℝ)(x:E)(u:E)(f:X)(k:ℕ): tires u k (fork r x f) =(↑r:ℂ)^k • (fork r x (tires u k f)):=by induction k generalizing f with | zero=> rw [pow_zero,one_smul]; rfl| succ k ih=> rw [tires,LinearMap.comp_apply,LinearMap.comp_apply,leanG,map_smul,ih,smul_smul,pow_succ']
end jet
end YM.RG05Readout.Pulse
