import YM.RG05Readout.Flatten.Rubric
import YM.RG05Readout.Pulse.Groups
/-!
# Cropping with W slots at ancestor.Period genuine

Include full Link product. Spawn before evaluation F on paired profile at n+1
 so one-subsystem sign laws apply. Here threshold normalization;
 field transport and angular frames separately.Slot members at their own horizons.
 Cup held at root independent of all other copies. Product computes *all* site
 choices with full test (not varying costs). Perturbative not defined here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Pulse
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station
open Records Basket Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{I J V:Type}[DecidableEq V][Fintype V]
    {j b k D:ℕ}
set_option quotPrecheck false
local notation "t!"=> (1,false)
local notation "A"=> C.S.a
local notation "Λ"=> C.S.toDepth
local notation "X!"=> C.side N p
local notation "Y!"=> C.side b p
local notation "G!"=>C.S.gridPoint
local notation "o!"=> C.S.place
local notation "R"=> C.path.rep N p N
local notation "ρ₀"=>C.S.radius p
local notation "W!"=> Wave V
local notation "J!"=> Cloud V
section root
variable (s:V→ℕ)(x:(i:V)→Palette C (s i))(y:V→Site (C.side N p))
def key (C:Family G)(N p d:ℕ)(v:Palette C d) (b:Address.Mark C d)(z:Site (C.side N p)): Goods G (C.side N p):= val v b • stepUp t! z (Local.presented (C.localSection (kept b.1)) 0 (C.path.rep N p N).p.threshold (Extra.Histories.Size.axis (C.labels.level (kept b.1)) b.2))
lemma entrance_real (v:Palette C d)(z:Site X!)(q:Body): stepUp t! z (entrance C d N p v 0 q)= ∑ i:Mark C d,readJ i.1 0 q • key C N p d v i z:=by
   rw [entrance,Records.rot_sum]; refine Finset.sum_congr rfl (fun i _=>?_); unfold key; rw [rot_scalar,rot_scalar]; exact smul_comm ..
-- hold RG germ.Store.Bin
local notation "T!"=> (i:V)→Mark C (s i)
noncomputable def harpoon : W!→ₗ[ℂ] Goods G X! where
    toFun f U:=∑ j:T!, (perform s (fun i=>(j i).1) f).val 0 *∏ i:V, key C N p (s i) (x i) (j i) (y i) U
    map_add' f g:= funext fun i=> by simp_rw [map_add]; simp only [AddMemClass.coe_add,Pi.add_apply,add_mul,Finset.sum_add_distrib] -- edit
    map_smul' c a:= funext fun i=> by simp_rw [map_smul];simp only [SetLike.val_smul,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum, RingHom.id_apply]
local notation "Z!"=> harpoon (C:=C) (N:=N) (p:=p) s x y
lemma hooked (f: V→Body) (U:Config G X!) :
   Z! (joint Finset.univ f) U=∏ i:V, stepUp t! (y i) (entrance C (s i) N p (x i) 0 (f i)) U :=by
    change (∑ j:T!,_)=_; simp_rw [finale,entrance_real,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [Fintype.prod_sum]; exact Finset.sum_congr rfl (fun j _=> (Finset.prod_mul_distrib).symm)
lemma stung {r:ℝ}{z:J!}{f g:W!}(h:∀ i ≤ ∑ j:V,s j, pie f g i z) : Z! (fork r z f)=Z! (fork r z g):= by
    funext U
    change (∑ j:T!,_)=(∑ j:T!,_); refine sum_congr rfl (fun j _=> ?_); apply congr_arg (· * _); unfold perform; simp_rw [machine_roll,SetLike.val_smul,Pi.smul_apply]; let a := fun i=>(j i).1
    apply congr_arg₂ (· • ·) rfl; change (perform s a f).val (z+r • 0)=(perform s a g).val (z+r • 0); rw [smul_zero,add_zero]; exact performance s a (h _ (pegs_cost s a))
lemma continuous_fee {E:Type*}[TopologicalSpace E](f:W!)(r:ℝ){τ:E→ Cloud V}(hT:Continuous τ) (U:Config G X!) : Continuous (fun i=> Z! (fork r (τ i) f) U):=by
    let L:= Finset.univ (α:=V) |>.toList
    have he (j:T!): let a:=(fun i=>(j i).1); Continuous (fun i:E=> (perform _ a (fork r (τ i) f)).val 0):=by
       intro a; unfold perform; simp_rw [machine_roll]; change Continuous (fun i:E=> (↑r:ℂ)^ _ • (machine s a L f).val (τ i+r • 0)); simp_rw [smul_zero,add_zero]; exact (((lit (machine s a L f) 0).continuous.comp hT).const_smul ((r:ℂ) ^ pegs s a L))
    exact continuous_finsetSum _ (fun i _=> (he i).mul continuous_const)
omit [DecidableEq V] in
lemma fly_fork (f:W!)(x y:J!)(r t:ℝ): fork t x (fork r y f)= fork (r*t) (y+r • x) f:= Subtype.ext <| funext fun z=> by
    change f.val (y+r • (x+t • z))=f.val (y+r • x+_); rw [smul_add,smul_smul,add_assoc]
lemma shift_hook (q:Site X!)(f: W!) : stepUp t! q ((Z!) f)=harpoon (C:=C) (N:=N) (p:=p) s x (fun i=> y i+q) f:= by
   funext U; change (∑ j:T!, ((perform s _ f).val 0) * ∏ i:V, _)=∑ j:T!,_ ; refine sum_congr rfl (fun j _=> ?_); apply congr_arg ( (perform s _ f).val 0 * ·); refine prod_congr rfl (fun i _=> ?_); unfold key; simp only [Pi.smul_apply]; apply congr_arg (val (x i) (j i) • ·); exact congr_fun (shiftE ..) U -- edit
end root

section writer
variable (s:V→ℕ)(x:(i:V)→Palette C (s i))(o:V→ Site (C.side b p))(h:b ≤ N)
local notation "r"=> Λ h p
local notation "T"=> Site (r).count
local notation "hα"=> (↑(r).count.val:ℝ)⁻¹
noncomputable def scalp : W!→ₗ[ℂ] Goods G X!:= ∑ t:V→T,(∏ i:V,ratioX (r) (s i)) • (harpoon (C:=C) (N:=N) (p:=p) s x (fun i=> (r).assemble (o i,t i)) ∘ₗ fork ((↑(r).count.val:ℝ)⁻¹) (fun i=>placeR (r) (t i)))
local notation "Y!p"=> scalp (C:=C) s x o h
lemma carving (f:V→Body) : Y!p (joint Finset.univ f)= Basket.bunchG (C:=C) (N:=N) o s f x:=by
    funext U; unfold bunchG scalp; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,Finset.sum_apply]
    unfold clinic; simp_rw [lift_pol (hm:=le_refl N) (ht:=h), show ∀ z: Site X!, ((C.S.toDepth (le_refl N) p).embed z)=z from (Records.like_embed ·),Finset.sum_apply]; rw [Fintype.prod_sum]; refine Finset.sum_congr rfl (fun i _=> ?_);
    let q:= fun j:V=> feeR (r) (i j) (f j); have ht: fork hα (fun j=>placeR (r) (i j)) (joint Finset.univ f)=joint Finset.univ q:=rfl
    simp_rw [ht,Pi.smul_apply,smul_eq_mul,hooked,Finset.prod_mul_distrib]; rfl
lemma cuts (f g:W!)(he:∀ i ≤∑ j:V,s j,∀ t: V→T,pie f g i (fun j=>placeR (r) (t j))) : Y!p f=Y!p g:=by
     unfold scalp; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]; exact sum_congr rfl (fun i _=> congr_arg (_ • ·) (stung s x _ (fun j hj=> he j hj i)))
lemma wave_cont {E:Type*}[TopologicalSpace E](f:W!)(q:ℝ){u:E→J!}(H:Continuous u)(U:Config G X!): Continuous (fun i:E=> Y!p (fork q (u i) f) U):=by
    unfold scalp; simp_rw [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,Finset.sum_apply,Pi.smul_apply,fly_fork]; apply continuous_finsetSum; intro j _; have Hx:= continuous_fee s x (fun i=> (r).assemble (o i,j i)) f (q*hα) (H.add (continuous_const (y:=q • (fun i=>placeR (r) (j i):Cloud V)))) U; exact Hx.const_smul (∏ i:V,ratioX (r) (s i))
end writer

end YM.RG05Readout.Pulse
