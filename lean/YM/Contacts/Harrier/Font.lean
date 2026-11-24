import YM.Contacts.Harrier.Spokes
import YM.Push.FINITE_DETECTION.Leading
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
-- test-letter stratum via real symmetric tensors (can rotate/mix as fixed linear coordinates)
namespace Font
open Tensor MultiNext.SignedSource Powers
variable (v:Cards)
def cash (k:ℕ): Submodule ℝ (Tensor.T E4 ℝ k) where
    carrier := {f| Tensor.Sym f}
    zero_mem':=fun _ _=> rfl
    add_mem' {u v} hu hv p q:=by simp only [_root_.add_apply,hu p q,hv p q]
    smul_mem' a _ h p q:= by simp only [_root_.smul_apply,h p q] -- binder?
abbrev salary (k:ℕ)(x:E4)(v: ↥Cards) : cash k := ⟨Tensor.coeff v.val k x,coeff_symm (Cards.able v k|>.contDiffAt)⟩
def gather (k:ℕ)(x:E4) : (↥Cards) →ₗ[ℝ] (↥(cash k)) where
   toFun v:= salary k x v
   map_add' p q:= Subtype.ext ( Tensor.coeff_add ((Cards.able p k).contDiffAt) ((Cards.able q k).contDiffAt))
   map_smul' _ p:= Subtype.ext (Tensor.coeff_smul _ ((Cards.able p k).contDiffAt))
def tally (k:ℕ) : ↥(cash k) →ₗ[ℝ] ↥Cards where
   toFun T:= Cards.pure T.val
   map_add' _ _:=rfl
   map_smul' _ _:=rfl
abbrev CardID (t:ℕ):= Fin (Module.finrank ℝ (cash t))
def basis (t:ℕ) := Module.finBasis ℝ (cash t)
abbrev plait (j:CardID t'): Cards:= tally _ (basis t' j)
abbrev grade (v:CardID k) : ↥(cash k)→L[ℝ] ℝ:= LinearMap.toContinuousLinearMap ((basis k).coord v)
abbrev pay (v:CardID k) : ↥Cards →ₗ[ℝ] ℝ:= (grade v).toLinearMap.comp (gather k 0)
lemma grade_base (a b:CardID k) : grade a (basis k b)= if a=b then 1 else 0:= by change (basis k).coord a (basis k b)=_; by_cases h:a=b; subst b; simp; simp [h]
lemma tally_funded (v:CardID k)(x:E4): gather k x (plait v)=basis k v:= by apply Subtype.ext; exact Push.FiniteDetection.Kelvin.diag_response _ ((basis k v).2) _
lemma tally_home (i:CardID k): Powers.home (plait i).val k:= lit _
lemma vanish (hq:i≠k)(T:Tensor.T E4 ℝ k): Tensor.coeff (Tensor.diagonal T) i 0=0:= by
   apply Tensor.ext_diag _ _ (coeff_symm ((diag_smooth T _).contDiffAt)) (fun _ _=>rfl); ext x; change Radial.jet (Tensor.diagonal T) i x=0; rw [Milling.radiant (diag_smooth T ω|>.contDiffAt.analyticAt) k i (fun p v=> Tensor.homogeneous T p v) x]; exact if_neg hq -- orientation
@[simp] lemma pay_base (a b:CardID k):pay a (plait b)=if a=b then 1 else 0 := (congr_arg (grade a) (tally_funded b 0)).trans (grade_base a b)
@[simp] lemma pay_close (a:CardID i)(b:CardID k)(h:i≠k): pay a (plait b)=0:= by change grade a (gather i 0 (plait b))=_; rw [show gather i 0 (plait b) =0 from Subtype.ext (vanish h _),map_zero]
lemma reflect (f:Cards)(h:Powers.home f.val i): f=∑ x:CardID i,pay x f • plait x:= by
   let X:=gather i 0 f; calc
    _= tally i X:= Subtype.ext (Powers.tensor_form h)
    _= tally i (∑ x:CardID i,pay x f • basis i x):= congr_arg _ (Module.Basis.sum_repr (basis i) X).symm
    _= _:= by simp only [map_sum,map_smul]
lemma scale_word (j:CardID k)(z:E4)(t:ℝ): gather i 0 (Cards.onRoute z t (plait j))=t^i • gather i z (plait j):= by
   let f:Cards:=plait j; let V(x:E4):=f.val (z+x); let T:= t • ContinuousLinearMap.id ℝ E4; have he:i ≤ i:= le_rfl; apply Subtype.ext; change Tensor.coeff (V ∘ T) i 0= t^i • Tensor.coeff f.val i z; unfold Tensor.coeff; rw [ContinuousLinearMap.iteratedFDeriv_comp_right T (show ContDiff ℝ i V from (Cards.able f i).comp (contDiff_const.add contDiff_id)) _ (Nat.cast_le.mpr he),T.map_zero]; unfold V; rw [iteratedFDeriv_comp_add_left,add_zero,smul_comm (t^i)]; apply congr_arg ((i.factorial:ℝ)⁻¹ • ·); ext x; simp only [_root_.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,T,ContinuousLinearMap.id_apply]; simpa using (iteratedFDeriv ℝ i f.val z).map_smul_univ (fun _=>t) x
lemma translate (j:CardID k)(z:E4)(t:ℝ): Cards.onRoute z t (plait j)=∑ i∈Finset.range (k+1), tally i (t^i • gather i z (plait j)):= by
   let p:= plait j; let V:= (basis k j).val; apply Subtype.ext; ext y; change Tensor.diagonal V (z+t•y)=_; rw [Push.FiniteDetection.Kelvin.diag_translate V (basis k j).2]; simp only [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]; exact sum_congr rfl fun i hi=> Tensor.homogeneous _ y t
-- above moments follow from this finite expansion
lemma above (h:k < i)(v:CardID k)(z:E4)(t:ℝ): gather i 0 (Cards.onRoute z t (plait v))=0 := by rw [translate,map_sum]; refine sum_eq_zero fun j hj=>?_ ; apply Subtype.ext; exact vanish (show i≠j from by have hh:= Finset.mem_range.mp hj; omega) _
lemma pay_center (a b:CardID k)(z:E4)(s:ℝ):pay a (Cards.onRoute z s (plait b))=s^k*(if a=b then 1 else 0):= by change grade a (gather _ _ _)=_; rw [scale_word,tally_funded,map_smul,grade_base]; rfl
lemma pay_above {a:CardID i}{b:CardID k}(h:k < i) (z:E4)(s:ℝ): pay a (Cards.onRoute z s (plait b))=0:= by change grade a (gather _ _ _)=_; rw [above h,map_zero]
lemma choice_bill [NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y](P:X→L[ℝ] Y):∃ a≥(0:ℝ),∀ x, ‖P x‖ ≤ a*‖x‖:= ⟨_,norm_nonneg P, ContinuousLinearMap.le_opNorm P⟩
lemma pay_cost (j:CardID k):∃ C≥(0:ℝ),∀ (v:Cards)(D:ℕ)(b:ℝ), k≤D→ Costs D v b→ ‖pay j v‖ ≤ C*b:= by
   obtain ⟨c,hc,H⟩:=choice_bill (X:=↥(cash k)) (Y:=ℝ) (grade j); refine ⟨c*(k.factorial:ℝ)⁻¹,by positivity,fun v D b ht h=> (H _).trans ?_⟩; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (show ‖Tensor.coeff v.val k 0‖ ≤ _ from by unfold Tensor.coeff; rw [norm_smul, Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (h _ ht 0 (by simp)) (by positivity)) hc
end Font
end
end YM.Contacts.Harrier
