import YM.MS.Cylinder.Roots
import YM.MS.RulesBV

/-!
# Real site and center sums with ghost phasing

`U` below denotes canonical BV bracket and Hessian. Position to mesh.
 Use same generic tests at continuum small rank eventually. `Note.Bond`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Koszul.Bonded
open Function Set Finset Plane Cylinder Lab
variable {R A I P Q : Type*} [CommRing R] {p:Sector A} (B:Bonded p I)
def district (B:Bonded p I) : Bonded (field p (P:=P)) (I× P) where
   plain:= B.plain.prodMap (Embedding.refl _)
   dual := B.dual.prodMap (Embedding.refl _)
   diff i j h:= B.diff i.1 j.1 (congr_arg Prod.fst h)
   wave i:= B.wave i.1

variable [Fintype I]
def Lap : On A P R:=∑ i:I, (B.fee i:R) • heart (B.dual i) (B.plain i)
lemma lap_at (F:Seed A P R): B.Lap F=∑ i:I, (B.fee i:R) • heart (B.dual i) (B.plain i) F:= by simp only [Lap,LinearMap.sum_apply,LinearMap.smul_apply]
lemma lap_traces (f:Seed A P R) {s:Finset P} (r:P→ Q)(h:BoundBy (s:Set P) f) (hr:Set.InjOn r (s:Set P)) : transport r (B.Lap f)= B.Lap (transport r f):= by simp only [B.lap_at,map_sum,map_smul]; exact Finset.sum_congr rfl (fun i _=> by rw [heart_transport _ _ f h hr])

section
variable [AddCommGroup P] [AddCommGroup Q]
def touch : Seed A P R→ₗ[R] On A P R:= ∑ i:I, (B.fee i:R) • root p (B.dual i) (B.plain i)
lemma touching (F H:Seed A P R): B.touch F H=∑ i:I, (B.fee i:R) • root p (B.dual i) (B.plain i) F H:=by simp only [touch,LinearMap.sum_apply, LinearMap.smul_apply]
lemma feel {s:Finset P}(r:P→+Q)(F H:Seed A P R) (h:BoundBy (s:Set P) F)(hv:BoundBy (s:Set P) H)(hr:InjOn r (s:Set P)): transport r (B.touch F H)= B.touch (transport r F) (transport r H):= by simp only [B.touching,map_sum,map_smul]; exact Finset.sum_congr rfl (fun i _=> by rw [trroot F H _ _ h hv hr])
end
section finite
variable [Fintype P]
lemma dbonds : ((B.district (P:=P)).BV : Op (Mode A P) R) = ∑ i:I, (B.fee i:R) • ∑ x:P,diffPair (B.dual i,x) (B.plain i,x):= by
    unfold BV loop; simp_rw [Finset.smul_sum]; exact Fintype.sum_prod_type ..
lemma lap_here (F:Seed A P R): (B.Lap F).val=B.district.BV F.val:=by simp_rw [B.lap_at,sum_stack,smul_stack,heart_finite,B.dbonds,LinearMap.sum_apply, LinearMap.smul_apply,LinearMap.sum_apply]
variable [AddCommGroup P]
lemma t_here (F H:Seed A P R): (B.touch F H).val= link B.district.BV true (field p) (sumHome F).val H.val:=by simp_rw [B.touching,sum_stack,smul_stack,roots_finite _ _ true (B.op _),B.dbonds,link_sum,link_scale,link_sum]
lemma l_bulk (F:Seed A P R): (sumHome (B.Lap F)).val=B.district.BV (sumHome F).val:= by rw [← B.lap_here,sumHome]; simp only [LinearMap.sum_apply,B.lap_at,map_smul,map_sum,← heart_shift]
lemma t_bulk (F H:Seed A P R): (sumHome (B.touch F H)).val=link B.district.BV true (field p) (sumHome F).val (sumHome H).val:= by simp_rw [B.touching,map_sum,map_smul,sum_stack,smul_stack,home_root _ _ _ _ true (B.op _),B.dbonds,link_sum,link_scale,link_sum]
end finite
end YM.MS.Koszul.Bonded
