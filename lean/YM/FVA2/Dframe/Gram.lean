import YM.FVA2.Dframe.Trace
import YM.Next.MAXWELL.Core
import Mathlib.Topology.Instances.Matrix
/-!
# The reflected pair and positivity on the actual physical sectors

At every fixed finite horizon. Here `yes`: use the substantial supplied
positive free point Gram result `Maxwell.Free.detects`; `positive`: the
nonsingular positive Gram test for any choice of complex-linearly-independent
fields in `Sec`. `wish` lets us use this positivity on limits of
finite-regulator Grams (no self-adjointness assumption before the limit).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Dframe.Gram
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.Menus MS.High MS.Wind MS.Theater MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open Table.Pairing
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {n d k:ℕ}{G:Gauge} {Z:Type}
variable (a:Axis) (x:E4)
abbrev γ (a:Axis)(x:E4): Points 2:= closedUp a (points fun _:Fin 1=> x) (points fun _:Fin 1=>x)
lemma γsep (h:0<x a) : γ a x∈conf _:= by have hp:single (points fun _:Fin 1=>x) a:= ⟨injective_of_subsingleton _,fun _=>h⟩; exact Table.Pairing.spans hp hp
abbrev mate (p:Sec G d) : Sec G d:= ori (Signed.reflect a) d (Normalize.reel d p)
def duo (p q:Sec G d): Tags G d 2:= ![ mate a p,q]
variable (V:Point G d 2) (p q: Sec G d)
def cost : ℂ:= V ( duo a p q )
private lemma first (u: Sec G d): V.toLinearMap (duo a p q) 0 (mate a u)= cost a V u q:=by rw [MultilinearMap.toLinearMap_apply,cost]; apply congr_arg; funext i; fin_cases i <;> simp [duo]
private lemma last (u:Sec G d): V.toLinearMap (duo a p q) 1 u= cost a V p u:=by rw [MultilinearMap.toLinearMap_apply,cost]; apply congr_arg; funext i; fin_cases i <;> simp [duo]
abbrev highQ (a:Axis)(V:Point G d 2)(p:Sec G d): Sec G d→ₗ[ℂ] ℂ:= V.toLinearMap (duo a p 0) 1
abbrev highP (a:Axis)(V:Point G d 2)(p:Sec G d): Sec G d→ₛₗ[starRingEnd ℂ] ℂ := (V.toLinearMap (duo a 0 p) 0).comp (( ori (Signed.reflect a) d ).comp ( reel d ))
lemma costQ : cost a V p q= highQ a V p q:=(last a V p 0 q).symm
lemma costP : cost a V p q= highP a V q p:=(first a V 0 q p).symm
lemma price : cost a (Normalize.scene (γ a x) d) p q = Maxwell.Free.score a x p.val q.val:= by
    unfold Maxwell.Free.score cabinet cost; rw [screen]; apply congr_arg; funext i; fin_cases i;
    · change (mate a p).val=( Fin.append _ _ ) ( Fin.castAdd 1 (0:Fin 1)); rw [Fin.append_left]; rfl
    change q.val=( Fin.append _ _ ) ( Fin.natAdd 1 (0:Fin 1)); rw [Fin.append_right]
lemma yes (h: 0<x a) (hz:p≠0): 0< cost a (Normalize.scene (γ a x) d) p p:= by rw [price]; exact Maxwell.Free.detects _ _ h _ (fun H=> hz (Subtype.ext H))
variable [Fintype Z] (v:Z→Sec G d)
-- linearly independent real+complex *test* basis, any
open scoped Matrix
open Matrix
-- standard complex Matrix
abbrev stage (a:Axis) (V:Point G d 2)(v:Z→Sec G d): Matrix Z Z ℂ := Matrix.of (fun i j=> cost a V (v i) (v j))
abbrev Join (v:Z→Sec G d)(B:Z→ℂ): Sec G d:= ∑ i,B i • v i
lemma account (T:Z→ℂ)(z:Z): (stage a V v *ᵥ T) z= cost a V (v z) (Join v T):= by rw [costQ,Join,map_sum]; unfold mulVec dotProduct; simp_rw [stage, of_apply,costQ,map_smul ]; exact Finset.sum_congr rfl fun i _=> mul_comm ..
lemma magnitude (T:Z→ℂ): star T ⬝ᵥ (stage a V v *ᵥ T)= cost a V (Join v T) (Join v T):= by
 let A:=Join v T; rw [costP]; nth_rw 2 [Join]; simp_rw [map_sum,(highP a V (Join v T)).map_smulₛₗ]; unfold dotProduct; refine Finset.sum_congr rfl (fun i _=>?_); rw [account a V v T i, costP]; rfl -- map rewrote under conv?
lemma positive (h: 0<x a) (he:LinearIndependent ℂ v) (T:Z→ℂ)(hu:T≠0): 0< star T ⬝ᵥ ( stage a ( Normalize.scene (γ a x) d ) v *ᵥ T ):= by rw [ magnitude ]; exact yes a x _ h (fun C=> hu (funext (Fintype.linearIndependent_iff.mp he T C)))
variable [DecidableEq Z]
lemma nonsing (h:0 < x a) (he:LinearIndependent ℂ v) : IsUnit ( stage a (Normalize.scene (γ a x) d) v ):= by
 let D:= stage a (Normalize.scene (γ a x) d) v; apply Matrix.mulVec_injective_iff_isUnit.mp; apply (Matrix.mulVecLin D).ker_eq_bot.mp; apply Matrix.ker_mulVecLin_eq_bot_iff.mpr; intro T hn; by_contra H; obtain hz:= positive a x v h he T H; rw [show stage a (Normalize.scene (γ a x) d) v *ᵥ T=0 from hn,dotProduct_zero] at hz; exact lt_irrefl _ hz
omit [DecidableEq Z] [Fintype Z] in
lemma walk {I:Type*}{L:Filter I} (w:I→Point G d 2)(H:∀v:Tags G d 2,Tendsto (fun i=> w i v) L (𝓝 (V v))): Tendsto (fun i=>stage a (w i) v) L (𝓝 ( stage a V v )):= by apply tendsto_pi_nhds.mpr; intro x; apply tendsto_pi_nhds.mpr; intro y; exact H _
lemma wish {I:Type*}{L:Filter I} {R:Matrix Z Z ℂ} {D:I→ Matrix Z Z ℂ} (φ:I→Z→ℂ)(h:IsUnit R)(hw:Tendsto D L (𝓝 R))(H:Tendsto (fun i=>D i *ᵥ φ i) L (𝓝 0)): Tendsto φ L (𝓝 0):= by
    have he:= (Matrix.isUnit_iff_isUnit_det _).mp h; have he' := he.ne_zero; let T:= fun p: Matrix Z Z ℂ × ( Z→ℂ )=> p.1 *ᵥ p.2; have hp:Continuous T:= Continuous.matrix_mulVec continuous_fst continuous_snd; have hv: ContinuousAt (Ring.inverse) R.det:= by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ he'
    have hi:Tendsto (fun i=> (D i)⁻¹) L (𝓝 R⁻¹):= (continuousAt_matrix_inv R hv).tendsto.comp hw; have hh:= (hp.tendsto ( R⁻¹, 0 )).comp (hi.prodMk_nhds H); change Tendsto (fun i=> (D i)⁻¹ *ᵥ (D i *ᵥ φ i)) L (𝓝 (R⁻¹ *ᵥ 0)) at hh; rw [mulVec_zero] at hh
    have he : ∀ᶠ i in L, (D i).det ≠ 0:= (( continuous_id.matrix_det.continuousAt.tendsto.comp hw ).eventually ( eventually_ne_nhds he' ))
    apply hh.congr'; filter_upwards [he] with i hi; exact Eq.trans ( Matrix.mulVec_mulVec .. ) ( show ((D i)⁻¹ * D i) *ᵥ (φ i)=_ from (by rw [ nonsing_inv_mul ( D i ) (isUnit_iff_ne_zero.mpr hi), one_mulVec ]) )
end YM.FVA2.Dframe.Gram
