import YM.RG05Readout.Pulse.Writer

/-! Every original input can be evaluated on its own fine copy while all slots retain the same signed spatial wave, residues, cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalReplicaWave
open RG05Readout RG05Readout.Pulse
set_option maxHeartbeats 200000
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
local notation "T!"=> (i:V)→Mark C (s i)
noncomputable def harpoon : W!→ₗ[ℂ] ((V → Config G X!)→ℂ) where
    toFun f U:=∑ j:T!, (perform s (fun i=>(j i).1) f).val 0 *∏ i:V, key C N p (s i) (x i) (j i) (y i) (U i)
    map_add' f g:= funext fun i=> by simp_rw [map_add]; simp only [AddMemClass.coe_add,Pi.add_apply,add_mul,Finset.sum_add_distrib] 
    map_smul' c a:= funext fun i=> by simp_rw [map_smul];simp only [SetLike.val_smul,Pi.smul_apply,smul_eq_mul,mul_assoc,Finset.mul_sum, RingHom.id_apply]
local notation "Z!"=> harpoon (C:=C) (N:=N) (p:=p) s x y
lemma hooked (f: V→Body) (U:V → Config G X!) :
   Z! (joint Finset.univ f) U=∏ i:V, stepUp t! (y i) (entrance C (s i) N p (x i) 0 (f i)) (U i) :=by
    change (∑ j:T!,_)=_; simp_rw [finale,entrance_real,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]; rw [Fintype.prod_sum]; exact Finset.sum_congr rfl (fun j _=> (Finset.prod_mul_distrib).symm)
lemma stung {r:ℝ}{z:J!}{f g:W!}(h:∀ i ≤ ∑ j:V,s j, pie f g i z) : Z! (fork r z f)=Z! (fork r z g):= by
    funext U
    change (∑ j:T!,_)=(∑ j:T!,_); refine sum_congr rfl (fun j _=> ?_); apply congr_arg (· * _); unfold Pulse.perform; simp_rw [machine_roll,SetLike.val_smul,Pi.smul_apply]; let a := fun i=>(j i).1
    apply congr_arg₂ (· • ·) rfl; change (perform s a f).val (z+r • 0)=(perform s a g).val (z+r • 0); rw [smul_zero,add_zero]; exact performance s a (h _ (pegs_cost s a))

end root
section writer
variable (s:V→ℕ)(x:(i:V)→Palette C (s i))(o:V→ Site (C.side b p))(h:b ≤ N)
local notation "r"=> Λ h p
local notation "T"=> Site (r).count
local notation "hα"=> (↑(r).count.val:ℝ)⁻¹
noncomputable def scalp : W!→ₗ[ℂ] ((V → Config G X!)→ℂ):= ∑ t:V→T,(∏ i:V,ratioX (r) (s i)) • (harpoon (C:=C) (N:=N) (p:=p) s x (fun i=> (r).assemble (o i,t i)) ∘ₗ fork ((↑(r).count.val:ℝ)⁻¹) (fun i=>placeR (r) (t i)))
local notation "Y!p"=> scalp (C:=C) s x o h
lemma carving (f:V→Body) : Y!p (joint Finset.univ f)= (fun U:V → Config G X!=>∏i,clinic C p N (s i) (x i) b (o i) t! (f i) (U i)):=by
    funext U; unfold scalp; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,Finset.sum_apply]
    unfold clinic; simp_rw [lift_pol (hm:=le_refl N) (ht:=h), show ∀ z: Site X!, ((C.S.toDepth (le_refl N) p).embed z)=z from (Records.like_embed ·),Finset.sum_apply]; rw [Fintype.prod_sum]; refine Finset.sum_congr rfl (fun i _=> ?_);
    let q:= fun j:V=> feeR (r) (i j) (f j); have ht: fork hα (fun j=>placeR (r) (i j)) (joint Finset.univ f)=joint Finset.univ q:=rfl
    simp_rw [ht,Pi.smul_apply,smul_eq_mul,hooked,Finset.prod_mul_distrib]; rfl
lemma cuts (f g:W!)(he:∀ i ≤∑ j:V,s j,∀ t: V→T,pie f g i (fun j=>placeR (r) (t j))) : Y!p f=Y!p g:=by
     unfold scalp; simp only [LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]; exact sum_congr rfl (fun i _=> congr_arg (_ • ·) (stung s x _ (fun j hj=> he j hj i)))

end writer
end YM.Integration.WilsonSeparatedOriginalReplicaWave
