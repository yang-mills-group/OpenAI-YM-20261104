import YM.X.Feyn.Base
import YM.X.Gauss.Shift
import YM.Push.FINITE_DETECTION.NoLinear
/-!
First parity gauge change. `mist` physical Feyn Haar (finite geom). global adjoint, average paid.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Feyn
open Function Filter Set MeasureTheory Lattice Wilson PertExtension PertExtension.Chart PertExtension.Orb
open Pert.Orb (Potential positiveLinks takeLink wilson action dLin bridge bridgeEquiv gZ takeDiv form curL formL)
open Series Series.Radial GaussianScore
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (he:Even n.val)
local notation "E" => Potential G n
local notation "A" => Dir G n

def paint (u:G.El):Module.End ℝ E:=
   (LinearMap.pi fun i:Key n=> G.adjoint u ∘ₗ takeLink i).codRestrict _ fun p i=> show G.adjoint u (p.val _)=-G.adjoint u _ from by rw [p.property i,map_neg];rfl
lemma un_paint (u:G.El)(x:E): paint u (paint u⁻¹ x)=x:= by ext1; funext i; exact (G.adjoint_mul ..).symm.trans (by simp;rfl)
lemma invari_div (u:G.El)(x:E)(j) : takeDiv j (paint u x)=G.adjoint u (takeDiv j x):= by
    change (∑ i: Axis, ((paint u x).val (j,i) - (paint u x).val (j-step i,i)))=G.adjoint u (Pert.Orb.divB x.val j); unfold Pert.Orb.divB; rw [map_sum]; exact Finset.sum_congr rfl fun i _=>Eq.symm (map_sub (G.adjoint u) (x.val _) (x.val _))
lemma invari_cur (u:G.El)(x:E)(i a b) : curL i a b (paint u x)=G.adjoint u (curL i a b x):= by
   unfold curL; simp only [LinearMap.coe_mk, AddHom.coe_mk]; unfold Pert.Orb.cur; simp only [map_sub,map_add]; rfl
lemma conjugLink (u:G.El)(x:G.Color): G.lieExp (G.adjoint u x)=u*G.lieExp x*u⁻¹:= by
   apply G.mat_injective; simp only [G.mat_lieExp,G.mat_mul,G.mat_inv]; rw [G.mat_adjoint,G.exp_conjugate]; rfl
lemma invariantLink {X:Type*}(u:G.El)(x:E)(O: Config G n→X)(h:GaugeInvariant O): O (positiveLinks (paint u x))=O (positiveLinks x):= by
   rw [show positiveLinks (paint u x)= gauge (fun _=>u) (positiveLinks x) from funext fun i=> conjugLink u (x.val i)]; exact h _ _
lemma glob (O:Config G n→ ℝ)(h:GaugeInvariant O)(hc: ContDiffAt ℝ ω (O ∘ positiveLinks) 0) (u:G.El)(x:E)(j:ℕ):jet (O ∘ positiveLinks) j (paint u x)=jet (O ∘ positiveLinks) j x:= by
   simp_rw [homogeneous_derivative _ _ j (hc.of_le le_top),← map_smul (paint u),comp_apply,invariantLink u _ O h]

lemma invari_sym (u:G.El)(x y:E): cost.P (paint u x) (paint u y) = cost.P x y:= by
   change form _ _ = form x y; unfold form; simp only [invari_cur]
   have he : ∀ x y:G.Color,Inner.inner ℝ (G.adjoint u x) (G.adjoint u y)=Inner.inner ℝ x y:= fun x y=>by simp only [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,←map_add,G.norm_adjoint]
   simp only [he]; congr 2; apply Finset.sum_congr rfl; intro i hi; change Inner.inner ℝ (takeDiv i _) (takeDiv i _) = _; rw [invari_div,invari_div, he]; rfl

def mist : Measure E:= (Module.finBasis ℝ E).addHaar
instance : (mist (G:=G) (n:=n)).IsAddHaarMeasure:= by unfold mist; infer_instance

def fog : (E→ℝ)→ℝ := cost.average mist
set_option maxHeartbeats 550000 in
lemma art_cont (x:Potential G n) : Continuous (fun u:G.El=>paint u x):= by
    apply Continuous.subtype_mk; exact continuous_pi (fun i:Key n=> Push.FiniteDetection.Low.adjoint_cont (x.val i))
lemma art_meas (x:E): Integrable (fun u:G.El=>paint u x) G.probHaar:= (art_cont x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma art_zero (hg:G.Simple)(x:E): ∫ u,paint u x ∂G.probHaar=0:= by
    ext1; funext i; let T:= (takeLink i (n:=n) (G:=G)).toContinuousLinearMap; change T (∫ u,paint u x ∂G.probHaar)=(0:G.Color); rw [← T.integral_comp_comm (art_meas x)]; exact Push.FiniteDetection.Low.colorMean hg (x.val i)
set_option maxHeartbeats 550000 in
lemma blank (hg:G.Simple)(p:E→ℝ)(hp:Gauss.Plausible p)(h:∀ u x,p (paint u x)=p x) (v:Module.Dual ℝ E): fog (p* (⇑v))=0:= by
   refine Gauss.untouched (cost (G:=G) (n:=n)) mist G.probHaar paint (fun u=>paint u⁻¹) (fun u x y=>?_) (fun i=>LinearMap.ext (un_paint i)) art_meas (art_zero hg) p hp h v
   rw [← invari_sym u (paint u⁻¹ x) y, un_paint]
end YM.PositionX.Feyn
