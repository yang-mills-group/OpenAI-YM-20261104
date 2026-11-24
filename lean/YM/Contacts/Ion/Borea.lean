import YM.Contacts.Ion.Bench
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
open Spark
-- No minimal size nor even period assumption for spin commutation; full chart. Measured hot is exactly its mirror (observed in orbit block before gauge).
variable {f:Side}(S:StepData m f)(h:Even f.val)
local notation "Λ"=> (SplitSpace (G:=G) S)
local notation "Θ" => (Forestry S)
local notation "Κ"=> (Precision.AxisChart G Θ)
local notation "L" => shineDance S
local notation "E"=> tribe S Θ
local notation "Ξ" => orderTurn Align.inverse
local notation "Σv"=> stash S Θ
open PertExtension.GaussianScore
variable {S}
def twist : Κ →L[ℝ] Κ:= (LinearMap.toContinuousLinearMap ( {
   toFun := fun x:Κ=>(E).symm (spin_active (E x))
   map_add':= fun x y=> by apply (E).injective; simp only [map_add, ContinuousLinearEquiv.apply_symm_apply]; funext i; exact neg_add ..
   map_smul':= fun q x=> by apply (E).injective; simp only [map_smul, ContinuousLinearEquiv.apply_symm_apply, RingHom.id_apply]; funext i; exact (smul_neg q (E x (pall i))).symm -- casts
 } : Κ→ₗ[ℝ] Κ))
local notation "T" => (twist (G:=G) (S:=S))
lemma unite (x:Κ): Ξ (Σv x)= Σv (T x):= transit S x
lemma untwist (x:Κ): E (T x)= spin_active (E x):= (E).apply_symm_apply _
lemma taut : Involutive T:= fun x=> (E).injective (by rw [untwist,untwist]; funext i; unfold spin_active; rw [pall_inv, neg_neg])
variable {J:Astro G S}{R P:FreeResolvent.FaceRow}(B:Beam S G J P R b)
local notation "Ω" => court B
local notation "Η"=> (order S Θ P (G:=G)) -- precedence
local notation "κx"=> treeMatrix G S Θ P
local notation "σx" => covariance G S Θ P
lemma niter (x y: Κ): (Ω).P x y= E y ⬝ᵥ (κx*ᵥ E x):= rfl
def rulant : Λ →ₗ[ℝ] Module.Dual ℝ Λ := (2:ℝ)⁻¹ • (((LinearMap.dualMap (L).toLinearMap).comp (Ω).P).comp (L).toLinearMap)
def wickLaw : Law Λ where
    P:=rulant B
    turns x y:= by change (2:ℝ)⁻¹* (Ω).P (L x) (L y)=_ ; rw [(Ω).turns]; rfl
    slope:=by
       obtain ⟨c,hc,hy⟩:= (Ω).slope; refine ⟨c/2, half_pos hc, fun x=> ?_⟩; change _ ≤ ((2:ℝ)⁻¹* (Ω).P (L x) (L x))/2; have he:= le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg x) (spot_pay S x) 2) hc.le) (hy (L x)); linarith only [he]
    smooth:= by change Continuous (fun x:Λ=> (2:ℝ)⁻¹*(Ω).P (L x) (L x)); exact ((Ω).smooth.comp (L).continuous).const_mul _
def lesson (i:Lines G f 1): Module.Dual ℝ Λ:= (attend S Θ i).comp (L).toLinearMap
local notation "Μx" => wickLaw B
variable {Q:House (Lines G f 1)}(A: Chest Q P)(Lh: sealed Q 3)
include A Lh
lemma slope (x y:Κ) : (Ω).P (T x) y=(Ω).P x (T y):= by rw [niter,niter,untwist,untwist,covenant B A Lh,skew]
include h
omit A Lh in
lemma pilots (v:Λ): T (L v)=L v:= (E).injective (by rw [untwist]; exact illuminate S h v)
lemma landing_funds (i:Lines G f 1): let U:= (Ω).inverse (attend S Θ i); L ((Μx).inverse (lesson i))= U+T U:= by -- implicit S
    intro U; let Z:= U+ T U; let q: Λ:= fun i=> Z (attic S i); have hV: T Z=Z:= by unfold Z; rw [map_add,taut,add_comm]
    have he:L q= Z:= by
       let p:= E Z; have hh: spin_active p=p:= (untwist Z).symm.trans (congr_arg (E) hV); have he:= supply S h p hh; change L (fun i=>((E).symm (E Z)) (attic S i))= (E).symm (E Z) at he; simpa using he
    have hk: (Μx).P q=lesson i:= LinearMap.ext fun x=> by
       change (2:ℝ)⁻¹*((Ω).P (L q) (L x))=attend S Θ i (L x); rw [he]; unfold Z; rw [map_add,LinearMap.add_apply,slope B A Lh,pilots h, show (Ω).P U=_ from (Ω).applies _]; ring -- args
    rw [←hk,Law.solves]; exact he
lemma extension_wick (i j: Lines G f 1) : (Μx).wick (lesson i) (lesson j) = σx i j- σx i (shadow j):= by
    let q:= (Ω).inverse (attend S Θ i); change Σv (L ((Μx).inverse _)) j=_; rw [show L ((Μx).inverse (lesson i))=_ from landing_funds h B A Lh i, map_add,←unite,Pi.add_apply,luminosity,←Spark.wick_rises B, ←Spark.wick_rises B]; rfl
end Align
end
end YM.Contacts.Lyre
