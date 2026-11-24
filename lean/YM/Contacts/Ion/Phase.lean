import YM.Contacts.Ion.Pure
namespace YM.Contacts.Lyre
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie Harrier Sequent
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k i r l j M D:ℕ}{ζ σ:ℝ≥0}
open UVNext PricedKernels Next.Free Lattice Tree FreeResolvent
open PertExtension.Orb MeasureTheory
namespace Align
open Spark
-- No minimal size nor even period assumption for spin commutation; full chart. Measured hot is exactly its mirror (observed in orbit block before gauge).
variable {f:Side}(S:StepData m f)(h:S.patch.Branches S.kernel G)
local notation "ιX"=>Align.inverse
local notation "Ξ"=>orderTurn ιX
local notation "ΞX"=> Link G m
local notation "Φ" => flax G S
local notation "Θ" => House.Dir (Yard G S)
def shadow (q:Lines G m 1) : Lines G m 1:= (-q.1-step (axisEquiv.symm q.2.1),q.2)
lemma stow : Involutive (shadow (G:=G) (m:=m)):= fun ⟨x,i⟩=>Prod.ext (by unfold Align.shadow; simp) rfl
lemma luminosity (v:ΞX)(i:Lines G m 1): Ξ v i= -v (shadow i):= by rcases i with ⟨x,i,b⟩; obtain ⟨i,rfl⟩:=axisEquiv.surjective i; simp only [coord_map,shadow,show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply i]; exact (flip_price ιX v x i b) -- defeq
lemma invert_spin (x: ΞX): Ξ (Ξ x)=x:= funext fun i=> by rw [luminosity,luminosity,neg_neg,stow]
lemma dot_car (x y:ΞX): Ξ x ⬝ᵥ Ξ y=x ⬝ᵥ y:= by unfold dotProduct; simp_rw [luminosity,neg_mul_neg]; exact Equiv.sum_comp (Equiv.ofBijective shadow stow.bijective) (fun i=> x i*y i)
lemma polarity (x y:ΞX): Ξ x ⬝ᵥ y=x ⬝ᵥ Ξ y:= by rw [← dot_car x (Ξ y),invert_spin]
lemma morning {X:Type}[Fintype X]{v w:X→ℝ}(hx:∀ x,x ⬝ᵥ v=x ⬝ᵥ w): v=w:= sub_eq_zero.mp (dotProduct_self_eq_zero.mp (show (v-w) ⬝ᵥ (v-w)=0 from by rw [dotProduct_sub,hx (v-w),sub_self]))
include h
lemma branding (V: Config G f)(U:Config G m)(i:SLink m) : dawn S (Lattice.pull ιX 0 V) (Lattice.pull ιX 0 U) i=dawn S V U (reflect i):= by
   let x:= U (reflect i); let y:= S.prediction V (art S) (reflect i); unfold dawn; rw [split_pure S h,flip_channel,flip_channel]; change G.price (x⁻¹ * (y⁻¹)⁻¹)=G.price (x*y⁻¹); rw [show x⁻¹ *(y⁻¹)⁻¹=x⁻¹*(x*y⁻¹)⁻¹*(x⁻¹)⁻¹ from by group,G.price_conj,G.price_inv]
lemma snap_hot (x:ΞX)(y:Link G f): hot S (weave S (Ξ x,Ξ y))=hot S (weave S (x,y)):= by simp only [hot_spec, Spark.grow, blooms]; rw [show input G m (Ξ x)=Lattice.pull ιX 0 _ from (flip_links ιX x).symm, show input G f (Ξ y)=Lattice.pull ιX 0 _ from (flip_links ιX y).symm]; change S.kernel.penalty * ∑ i,dawn S (Lattice.pull _ _ _) (Lattice.pull _ _ _) i= S.kernel.penalty*∑ i,dawn S (input G f y) (input G m x) i; simp_rw [branding S h]; exact congr_arg (_*·) (Equiv.sum_comp (Equiv.ofBijective reflect (show Involutive (reflect (n:=m)) from reflect_reflect).bijective) _)
lemma cease (x:ΞX)(y:Link G f)(k:ℕ): jet (hot S) k (weave S (Ξ x,Ξ y))=jet (hot S) k (weave S (x,y)):= by
   let U:= ΞX × Link G f; let L: U →L[ℝ] U := ContinuousLinearMap.prodMap Ξ Ξ; let p:= weave (G:=G) S; have he : hot S ∘ (p.comp L)=hot S ∘ p:=funext fun v=> snap_hot S h v.1 v.2; change jet _ _ ((p.comp L) (x,y))=_; rw [← Garf.woven (hot_ana h) (p.comp L),he,Garf.woven (hot_ana h) p]
lemma hunger (y: Link G f): Ξ (Φ*ᵥ y)=Φ *ᵥ Ξ y := by
   let x:= Φ *ᵥ y; let d:= Ξ x- Φ *ᵥ Ξ y; let u:= S.kernel.penalty; have hp:= S.kernel.penalty_pos; have he:=cease S h x y 2; rw [spice _ h,spice _ h] at he; simp only [Spark.grow,blooms,←show Φ *ᵥ y=x from rfl] at he; change u*(d ⬝ᵥ d)/2=u*((Φ *ᵥ y-Φ *ᵥ y) ⬝ᵥ _)/2 at he; simp only [sub_self,dotProduct_zero,mul_zero] at he; apply sub_eq_zero.mp
   exact dotProduct_self_eq_zero.mp ((mul_eq_zero.mp ((show u*(d ⬝ᵥ d)=0 from by linarith only [he]))).resolve_left hp.ne')
end Align
end
end YM.Contacts.Lyre
