import YM.QuadraticLocal.Deletion.Crop
import YM.QuadraticLocal.Hearth
/-!
# Rotated bookings after setting markers to zero

Transfer past a mark state with absent contributions. Preserves support and
flags even when all the material is zero. Use for proportional budget exactly
zero instead of infimum of estimates on a changed interpretation/stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Deletion
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open Throng
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {T J : Type*} {w : V → ℝ} {a α β γ k b r :ℝ} {B : ℕ}
variable {P : ℕ→ ForcedAddress G n} {F : Code G n} {S:Set V}
variable (hw: ∀ i,0<w i)
lemma zero_cost {I:Type*}{Y:I→Support n}{f:I→ℝ} (h:Hit Y B f a 0)(i:I)(hx:(Y i).Nonempty) : f i=0:=by
    obtain ⟨x,hx⟩:= hx; have hv:= (h x).1 i; have hh:= ( (h x).2.1.le_tsum i (fun j _=>(h x).1 j) ).trans (h x).2.2; simp only [if_pos hx] at hv hh; exact (mul_right_cancel₀ (Real.exp_ne_zero _) ((le_antisymm hh hv).trans (zero_mul _).symm)) -- orientation
variable (L:Lamps T J G p o R)
include hw in
lemma absent (h:L.Paid w B a 0) (i:J)(t:T)(U:Config G n): L.light t i U=0:=by
   obtain ⟨f,hf,hG,hP⟩:=h.budget; let p:= L.address i; have hp: p.site∈L.ground i:= p.anchor; have he:= Lamps.light_size L i t U (hG i t p.site hp); have hh:= zero_cost hP i ⟨_,hp⟩; exact norm_le_zero_iff.mp (show ‖L.light t i U‖ ≤ 0 from ((mul_eq_zero.mp hh).resolve_left (Poly.worth hw _).ne') ▸ he)
variable (H: QuadraticLocal.Hard T p P F o R)
include hw in
lemma quietMode (h:Hard.Pair H w B a b 0) {i:R.Mode}(he:i≠R.quiet)(t:T)(U:Config G n)(j:ℕ): (H.hard t j U).part i=0:=by
   obtain ⟨f,hf,hG,h⟩:=h.cashout; have hv:= zero_cost h j ((P j).inventory_ne.mono (P j).inventory_sup); let u:= f j; change Hard.active w u=0 at hv; have ht:= Poly.member hw i (GridRenewal.Rain.fresh u); rw [Hard.hotPart,if_neg he, show Poly.price w (GridRenewal.Rain.fresh u)= 0 from hv] at ht; exact norm_le_zero_iff.mp ((hf j t U i).1.trans ((le_of_eq ((hf j t U).norm i).symm).trans ((nonpos_of_mul_nonpos_right ht (Poly.worth hw i))))) -- Norm API ht direction check
lemma blank_accepts (x:Poly R) : Throng.Hard.active w (crop R ∅ x)=0:=by unfold Throng.Hard.active; rw [show GridRenewal.Rain.fresh (crop R ∅ x)=0 from ?_,Poly.zero_price]; ext1 i; rw [Hard.hotPart, Deletion.zeroMode,Poly.part_nil]; split <;> simp -- try
private lemma noLamp (i:R.Mode)(hi:i≠R.quiet): ¬preserve i.val ∅:= fun h=>hi (Subtype.ext (show i.val=∅ from Finset.eq_empty_iff_forall_notMem.mpr fun x hh=> Set.notMem_empty _ (h _ hh)))
lemma emptyL : (sink ∅ L).Paid w B a 0:=by
   refine ⟨fun _ : J=> 0, fun _=> le_rfl, fun i t x hx=> ?_, fun i=>?_ ⟩
   · unfold sink; dsimp only; rw [if_neg (noLamp _ (L.live i))]; exact bound_weaken (bound_const _) (le_of_eq norm_zero)
   simp only [sink,Lamps.ground,mul_zero,zero_mul,ite_self]; exact ⟨fun i=>le_rfl, summable_zero,le_of_eq tsum_zero⟩ -- maybe
include hw in
lemma emptied (h:H.Paid w B a b): Hard.Pair (cork ∅ H) w B a b 0:= by
    obtain ⟨f,hf,hG⟩:= h.wages; let g i:= crop R ∅ (f i); refine ⟨g,fun i t U=>Deletion.cover ∅ _ _ (hf i t U),fun i=>budget_mono (hG i) (fun j=>by split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl) (fun j=>by split; exact mul_le_mul_of_nonneg_right (Deletion.paid ∅ hw _) (Real.exp_pos _).le; exact le_rfl),fun i=>?_⟩
    simp only [g,blank_accepts,zero_mul,ite_self]; exact ⟨fun i=>le_rfl, summable_zero,le_of_eq tsum_zero⟩

variable {X0:Rep G n} (M:Gallery T J o X0 R)
variable (h:M.E.Paid w B a 0)(hV: Hard.Pair M.K w B a b 0)
local notation "T!"=> offer S M
variable [Fintype V]
include h hV hw
lemma free (t:T)(U:Config G n): (T!).density t U=M.density t U:=by
    have hv:(T!).E.log t U=M.E.log t U:= by
       unfold Lamps.log; refine tsum_congr fun j=>?_ ; rw [show (T!).E.frame j t U= _ from Deletion.frame S M.E j t U]; unfold Lamps.frame; rw [absent hw M.E h, Poly.send_zero]; apply map_zero
    have hX: (T!).K.hard t= M.K.hard t:= by
       funext i v; ext1 q; change (crop R S _).part q=_; rw [watching]; split; exact rfl; next H=> exact (quietMode hw M.K hV (fun he=>H (by simp [he,preserve,Census.quiet])) t v i).symm
    unfold Gallery.density Gallery.gas; rw [hv,hX]
omit h hV hw
end YM.QuadraticLocal.Deletion
