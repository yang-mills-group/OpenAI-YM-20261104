import YM.OPE.Compatible.Bust.Vault
/-!
# Slices on Seats. color energy∞.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08
open scoped Topology BigOperators Classical
variable {I K E:Type}{m r i j n k:ℕ}{C D:ℝ}
-- any row pointcall, vary by index
structure RowB (I:Type) where
   val : Row I I
   fare : ℝ
   positive : 0≤fare
   lease (i j:I)(x:Cover) : ‖val i j x‖ ≤ fare
abbrev throat (A:RowB I)(x:Page I (r+2)):= A.val (x 0).2 (mort x 0).2 (poke x)
def dent (A:RowB I)(x:stave m (r+2) I): stave m (r+2) I:= plant m (tunnel A.val (seed m (r+2) I x)) (A.fare*‖x‖) (by
    let f:=seed m (r+2) I x; let t i:=figure m i * ‖f i‖; let C:= A.fare; have he:=humor (m:=m) x; apply budget_minor (g:=fun i=> C*t i) _ (fun i=> mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _)); swap
    · refine ⟨fun i=> mul_nonneg A.positive (he.1 _), he.2.1.mul_left C, ?_⟩; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left he.2.2 A.positive
    intro i; unfold t tunnel;rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (A.lease ..) (norm_nonneg _)) (zero_le_one.trans (payer m _))).trans_eq (by ring))
lemma nailD (A:RowB I)(x:stave m (r+2) I): seed m _ I (dent (m:=m) A x)=tunnel A.val (seed m _ I x):=by unfold dent;rw [botany]
lemma launchD (A:RowB I)(x:stave m (r+2) I): ‖dent (m:=m) A x‖≤A.fare*‖x‖:=by unfold dent; exact kept_stalk _ -- elaboration
lemma meltDown (x:stave m (r+2) I): soot m (Sack.rope melt (seed m _ I x)) ‖x‖:=((Sack.cart _ (humor (m:=m) x) zero_le_one (payer m) (fun i=>show figure m (melt i) ≤ figure m i*1 from by rw [mul_one]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast ((notched (mort i)).trans (notched i))) m))).tips (by rw [mul_one])
def stirC (I:Type)(m r:ℕ): stave m (r+2) I→L[ℝ] stave m r I:=LinearMap.mkContinuous {
    toFun x:= plant m (Sack.rope melt (seed m _ I x)) ‖x‖ (meltDown (m:=m) x)
    map_add' x y:= seed_inj m _ _ (by rw [botany,map_add,map_add,botany,botany,Sack.rope_add _ (tiller _ x) (tiller _ y)])
    map_smul' c x:= seed_inj m _ _ (by rw [botany,map_smul,map_smul,botany]; ext i; unfold Sack.rope; rw [Pi.smul_apply]; change _= c*( ∑' i,_); rw [← tsum_mul_left]; apply tsum_congr; intro j; rw [Pi.smul_apply];split_ifs;rfl;rw [mul_zero]) }
    1 (fun x=> (kept_stalk (meltDown (m:=m) x)).trans_eq (one_mul _).symm)
lemma stirLeg (A:RowB I)(p:stave m (r+2) I): seed m _ _ (stirC I m r (dent (m:=m) A p))=pad A.val (seed m (r+2) I p):=by let x:=dent (m:=m) A p; rw [show seed m _ _ (stirC I m r x)=_ from botany m _ ‖x‖ (meltDown (m:=m) x), show seed m (r+2) _ x =_ from nailD A p]; rfl
-- strong
lemma dentF (A:RowB I)(i j:ℕ):∃ D:stave i (j+2) I→L[ℝ] stave i (j+2) I,⇑D=dent (m:=i) A∧‖D‖ ≤ A.fare :=by -- coerce
    let D: stave i (j+2) I→ₗ[ℝ] stave i (j+2) I:= {
       toFun :=dent (m:=i) A
       map_add' x y:=seed_inj i _ _ (by rw [nailD,map_add,map_add,nailD,nailD]; ext1 u; simp [tunnel,add_mul])
       map_smul' c x:=seed_inj i _ _ (by rw [nailD,map_smul,map_smul,nailD]; ext1 u; simp [tunnel];ring) }
    let T:=D.mkContinuous A.fare (fun x=>launchD (m:=i) A x); exact ⟨T,rfl,T.opNorm_le_bound A.positive fun x=>launchD (m:=i) A x⟩
