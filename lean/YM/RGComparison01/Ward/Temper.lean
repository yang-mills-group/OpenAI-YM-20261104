import YM.RGComparison01.Ward.Cannet
import YM.RGComparison01.Ward.Mont

/-!
# Auxiliary-radius covariance theorem

 Need larger Ward band even in Auxiliary used for the actual Mark pricing.
 Assume untinted actual comparison on that larger band, in TRUE Taylor norm
 (will use Reels.premier over Station). Obtain Re-centered comparison on
 the smaller angular pricing band, in that band's budget. The new output is
 globally posed without any Render/Probe-on-f claims -- only independent input
 data and the explicit root projection. Not identifying it by JUST the numerical
 comparison; the LANG is fixed first here. Identification with the required PT
 coefficient/renderings remains another claim.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Ward
open Function Filter MeasureTheory RG Pressure Pressure.Stores Pressure.Tube Gauge Wilson
open Lattice Next.Fluctuations Push Push.Uniform Push.AbsoluteSums Precision Exterior
open Work.E03 Work.F03 ConnectedActivityE6 SliceRows Blaze Brush Metric
open scoped Matrix.Norms.Frobenius Topology ContDiff InnerProductSpace Classical BigOperators
variable {G:Gauge}{c:Side}{j k :ℕ}{p r u d v A:ℝ}
local notation "T"=> Uniform.Primary c G
local notation "Y"=> Positions (Uniform.Primary c G)
variable (F : Config G c→ℝ)(f:Positions (Uniform.Primary c G)→ℝ)
structure Duplex (G:Gauge)(k:ℕ) where
   C:Visage G k
   rate:ℝ
   positive:0≤rate
   fits(c:Side)(x:Positions (Uniform.Primary c G)): ‖x‖≤1→ Mode Ward.awake x k rate
lemma polarized (G:Gauge)(k:ℕ): Nonempty (Duplex G k):=by
   obtain ⟨h⟩:= vista G k; obtain ⟨d,hv,hF⟩:= gates G k; exact ⟨h,d,hv,hF⟩

namespace Duplex
variable (D: Duplex G k)
-- PAYABLE all auxiliary moves in exactly these cuffs; Big disk booked separately.
structure Blurb (D:Duplex G k)(c:Side)(p r u:ℝ) :Prop where
   rootF : p ≤ r
   letC : 0 ≤ p
   paid  : Visage.berth G c k D.rate*p ≤ D.C.radius
   circle : D.C.wing c D.rate*p+u <r -- u≥0 allocated
-- on smaller p-on-window, estimate P fits
variable (o:Site c) {S:Set (Config G c)}
variable (hB:Blurb D c p r u) (he:∀ z:G.El,∀ V∈S,toral o z V∈S ∧ F (toral o z V)=F V)
   (hf : ContDiff ℝ (↑k:WithTop ℕ∞) f)
variable (h:∀ x:Positions (Uniform.Primary c G), ‖x‖+u<r → awake x ∈ S → Brush j A r⁻¹ (F ∘ awake - f) x) -- j ≤ k
include hB he hf h
variable (hk:1 ≤ k) (hp: p ≤ 1) (hP: 0<p) (ht:j≤k)
variable (hS: ∀ x: Positions (Uniform.Primary c G),awake x∈ S→ ∀ᶠ y: Positions (Uniform.Primary c G) in 𝓝 x,awake y∈S)
local notation "T'"=> D.C.wing c D.rate
def conjCost (D:Duplex G k)(n:ℕ)(c:Side):= evolCost n (D.C.wing c D.rate)
include hk hp hP ht hS
lemma sways (x:Positions (Uniform.Primary c G))(hx: ‖x‖<p)(hX: awake x∈ S): Brush j (D.conjCost j c*A) p⁻¹ ((F-D.C.chant o f)∘awake) x:= by
   let F' (i:Y) (z:G.El):= F (awake i) - f (D.C.encode o (awake i) z)
   have hg' i: Continuous (f ∘ D.C.encode o (awake i)) := by
     have ht : Continuous (fun z:G.El => ((awake i),z)) := continuous_const.prodMk continuous_id
     let V : Config G c:= awake i
     let X (z:G.El):=(V,z)
     have h₀ := Continuous.comp (D.C.drape o) (show Continuous X from ht)
     have hu : ((fun v:Config G c×G.El => D.C.encode o v.1 v.2)∘ X)=D.C.encode o (awake i):= rfl
     rw [hu] at h₀
     exact hf.continuous.comp h₀
   have hm i: Continuous (F' i) := by
     exact (show Continuous (fun z:G.El=> (fun _=> F (awake i)) z-(f ∘ D.C.encode o (awake i)) z) from continuous_const.sub (hg' i))
   have he' y : ((F-D.C.chant o f)∘awake) y = ∫ z,F' y z ∂G.probHaar:=by
      let g:=f∘D.C.encode o (awake y)
      have hg: Continuous g:= hg' y
      change F _ - D.C.chant o f (awake y)=∫ z,F (awake y)-g z ∂G.probHaar; rw [integral_sub (integrable_const _) (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)),integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]; rfl
   refine (Ward.pour (k:=j) F' x ?_ (Eventually.of_forall fun i=> (hm i).measurable)).shimmy (Eventually.of_forall he')
   have ha y (hy: ‖y‖<p) (hy': awake y∈ S) (z:G.El) : let V:= D.C.encode o (awake y) z
                   awake V∈S ∧ F (awake V)=F (awake y):=by
      dsimp only; rw [show awake _=toral o z (awake y) from D.C.award _ _ _ (fun i=> ((Visage.earnings o z (D.fits c) hk _ hy.le hp).2 i).trans hB.paid)]; exact he z _ hy'
   filter_upwards [continuous_norm.continuousAt (gt_mem_nhds hx),hS x hX] with y hy hy' z
   let V (i:Y):= D.C.encode o (awake i) z; change ‖y‖<p at hy; have hy'' := ha y hy hy' z -- S in hS
   have he : ‖V y‖ ≤ T'*p:= D.C.drops _ _ (D.fits c) hk y hy.le hp
   have hg:= h (V y) (lt_of_le_of_lt (add_le_add_left he u) hB.circle) hy''.1
   refine (Ward.liftR V _ _ hP hB.rootF (tuned V y hP hp ((D.C.shot _ _ (D.fits c) _ (hy.le.trans hp)).smaller ht) he) hg).shimmy ?_
   filter_upwards [continuous_norm.continuousAt (gt_mem_nhds hy),hS y hy'] with y' hv hv'
   unfold F'; dsimp only [Function.comp_apply,Pi.sub_apply]; rw [show F (awake (V y'))=F (awake y') from (ha y' hv hv' z).2]
end Duplex
end YM.RGComparison01.Ward
