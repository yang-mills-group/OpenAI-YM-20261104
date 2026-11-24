import YM.FVAAlt2.First.Leg
import YM.FVAAlt2.Shop.Solution
/-! The derived analytic LOG cylinder has precise linear coefficients `wideLinear`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Pairing
open Lattice Finset Filter Function Wilson Source Labels
open MS MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native MS.Book MS.Plane MS.Theater MS.Landau
open Pert Pert.Orb MS.Cylinder.Lab
open scoped ContDiff BigOperators Topology Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}(p:Key G)
set_option quotPrecheck false
local notation "Ω"=> Lane4 G
local notation "a"=> Q p
local notation "I"=> paper p.1 × Conn G
local notation "σ"=> Lattice.Links ℤ G.Color
open RG11.FirstW (pointU tensor_front tensor_ride)
/-- record real derivative coefficient on native leg -/
def duke (i:I):ℝ:= fderiv ℝ (written p) 0 (priv (Q:=paper p.1) i)
def wh (p:Key G) : Lattice.Links ℤ G.Color→ₗ[ℝ] ℝ:= (Labels.axes G p.1).coord p.2 ∘ₗ Bare.wideLinear G p.1 1 (0:Cover)
lemma duke_wide (v:σ): ∑ i:I, (v i.1.val) i.2 * duke p i= wh p v:=by
 let z:a:= fun i=> v i.val; let w:= (G.lieExp ∘ v); let f(t:ℝ):= Bare.tensorJet 1 (pointU v t) 0 p.1; let L:Labels.Taylor G p.1→L[ℝ] ℝ:= ((Labels.axes G p.1).coord p.2).toContinuousLinearMap
 have hf : HasDerivAt f (Bare.wideLinear G p.1 1 (0:Cover) v) 0:= by
     rw [←tensor_front v]; rw [iteratedDeriv_one]; exact ((show ContDiff ℝ ∞ f from (tensor_ride v 1 _ p.1).1).differentiable (by simp) _).hasDerivAt
 have hU(t:ℝ): L (f t) = written p (t • z):= stencil_is p (t • v)
 have he : HasDerivAt (fun t:ℝ=> t • z) z 0:= by simpa using (hasDerivAt_id' (0:ℝ)).smul_const z
 have hg: HasDerivAt (fun t:ℝ=> written p (t • z)) (fderiv ℝ (written p) 0 z) 0:=by
    nth_rw 1 [show (0:a)=(0:ℝ) • z from (zero_smul ℝ z).symm] -- affects statement? Need design
    exact ( HasFDerivAt.comp_hasDerivAt (l:=written p) (f:=fun t:ℝ=>t • z) 0 (show HasFDerivAt _ _ _ from (show DifferentiableAt ℝ (written p) ((0:ℝ) • z) from (zero_smul ℝ z).symm ▸ (born p).differentiableAt (by simp)).hasFDerivAt) he )
 have hk : HasFDerivAt L L (f 0):= ContinuousLinearMap.hasFDerivAt (𝕜:=ℝ) (E:=Labels.Taylor G p.1) (F:=ℝ) L
 have hl:= hk.comp_hasDerivAt (f:=f) 0 hf
 change HasDerivAt (fun r=>L (f r)) (wh p v) 0 at hl
 simp_rw [hU] at hl; rw [hl.unique hg]
 rw [ ← (Shop.bar G (paper p.1)).sum_repr z,map_sum]; refine Finset.sum_congr rfl fun i _=>?_; rw [map_smul,Shop.privbar,show (Shop.bar G _).repr z i=v i.1.val i.2 from Shop.coord_isob («I»:=paper p.1) (G:=G) i z];rfl
abbrev tally (c:Lane4 G):=∑ i:I, Shop.onew (i.1.val,i.2) c * (duke p i:ℂ)
lemma shop_one(c:Ω): Tone.run (origin p) [c]= tally p c:=by
 unfold Tone.run origin Sew.art; rw [study,eq_pull, pull_cons]; apply Finset.sum_congr rfl; intro i _; rw [pull_nil];rfl
lemma shop_eq : mask 1 (Tone.run (origin p))= mono (tally p):=by
 funext l; rcases l with _ |⟨c,_|⟨c',l⟩⟩; exact strange [] (by simp); exact (enough [c] (by simp)).trans (shop_one p c); exact strange _ (by simp; omega)
end YM.FVAAlt2.Pairing
