import YM.AllOrder.Ker.Live
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Period
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Ker
open Lattice Laurent RG Gauge Filter Tree Metric Finset Bloch
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice
open Further.PhysicalPeriodLimitF933 Shingle Macrame
open Push.Uniform Precision Bid Wilson Push Exterior Pressure Function
open Matrix Complex
open scoped BigOperators Topology Classical ContDiff
variable {n m:Side} {k M:ℕ}{α β δ τ : Type}[Fintype α][Fintype β][Fintype δ][Fintype τ]
namespace Spine
-- Every capsule fan. Matrix borders.
def mpack (F:Matrix (Leaf n α) (Leaf n β) ℝ): Mat n α β 1:= fun i t=> F i (t 0)
omit [Fintype α] in
lemma he_pack (G : Mat n α β 1): mpack (headMatrix G) = G:= by funext i t; unfold mpack; rw [headMatrix_at]; exact congr_arg (G i) (funext fun i=>by fin_cases i; rfl)
omit [Fintype α] in
lemma unpack (G:Matrix (Leaf n α) (Leaf n β) ℝ) : headMatrix (mpack G)=G:= by ext i j; rw [headMatrix_at]; rfl

section work
lemma fielding (W:Window n m M)(F:Matrix (Leaf n α) (Leaf n α) ℝ) (E:Matrix (Leaf m α) (Leaf m α) ℝ) : Every (BookM W α) E F↔ Same (mpack F) (mpack E) W:=by
   rw [Shingle.intended]; let P:=BookM W α; let V:= fun j:Leaf m α=> (![j]:Fin 1→Leaf m α); have hh : Injective V:= fun i j h=> congr_fun h 0
   have he t (i:Leaf m α) : ∑ u∈robe W (β:=α) (k:=1) t,mpack E i u=∑ u∈parcel P (t 0),E i u:= by
      rw [show robe W t=(parcel P (t 0)).image V from ?_,Finset.sum_image hh.injOn]; · rfl
      ext u; simp only [tried, Finset.mem_image, Shingle.posted]; constructor
      · intro hu; refine ⟨u 0, congr_fun hu 0, funext fun j=>by fin_cases j; rfl⟩
      rintro ⟨k,hk,rfl⟩; exact funext fun j=>by fin_cases j; exact hk
   exact ⟨fun h i t=>by rw [he]; exact (h ..).symm, fun h i t=>((he ![t] i).symm.trans ((h i _).symm))⟩

lemma stationed (G:Mat n α α k)(w:Site n) : let W:= Macrame.parallel w; Same G G W↔ ∀ i t,G (turnM α w i) (turnM α w∘t)=G i t:=by
  intro W; let u:=turnM α (-w)
  have hh t: robe W (k:=k) (β:=α) t={u∘t}:= by
     ext x; simp only [tried, funext_iff, Finset.mem_singleton]; exact forall_congr' fun i=> swiv_eq w ..
  simp_rw [Same,hh,Finset.sum_singleton]; constructor
  · intro h i t; have hz : u ∘ (turnM α w ∘ t)=t:= funext fun i=> ((swiv_eq w ..).1 (rfl:turnM α w (t i)=_)).symm; rw [show turnM α w i = BookM W α i from rfl, h i _, hz]
  intro h i t; let L:=turnM α w; exact (congr_arg (G (L i)) (show t=L ∘ u ∘ t from (by funext i; exact (((swiv_eq w ..).2 (rfl:u (t i)=_))).symm))).trans (h i _)
-- submatrix bill
omit [Fintype α] [Fintype β] [Fintype δ] [Fintype τ] in
lemma up_pieces (F : Fan α β k)(d:δ→α)(f:τ→β)(i:Leaf n δ)(t:Fin k→Leaf n τ): pieces F n (Primitives.TwoWave.up d i) (Primitives.TwoWave.up f ∘ t)=pieces (fun i t=> F (d i) (f ∘ t)) n i t := by
 unfold pieces; apply tsum_congr; intro w
 split <;> rename_i h; · have hx : t= floated i.1 (Prod.snd ∘ t) w:= funext fun j=>Prod.ext (congr_arg (fun u:Leaf n β=>u.1) (congr_fun h j)) rfl; rw [if_pos hx]; rfl
 rw [if_neg (fun (ht : t= floated i.1 (Prod.snd ∘ t) w)=> h (funext fun l=>Prod.ext (congr_arg (fun u:Leaf n τ=>u.1) (congr_fun ht l)) rfl))]

lemma smol (W:Window n m M){R:Matrix (Leaf n α) (Leaf n α) ℝ}{S:Matrix (Leaf m α) (Leaf m α) ℝ}(h:Every (BookM W α) S R)(f:β→α)(hf:Injective f) : Every (BookM W β) (S.submatrix (Primitives.TwoWave.up f) (Primitives.TwoWave.up f)) (R.submatrix (Primitives.TwoWave.up f) (Primitives.TwoWave.up f)):= by
  let E(x:Side):= fun a:Leaf x β=> Primitives.TwoWave.up f a; let B:= BookM W β; let A:= BookM W α; have ht : Injective (E m):= fun i j h=> Prod.ext (congr_arg (fun x:Leaf m α=>x.1) h) (hf (congr_arg (fun x:Leaf m α=>x.2) h))
  apply (Shingle.intended ..).2; intro i j
  have he:= (Shingle.intended ..).1 h (E m i) (E n j); rw [show parcel A (E n j)=(parcel B j).image (E m) from ?_,Finset.sum_image ht.injOn] at he; · exact he
  ext x; simp only [posted,Finset.mem_image]; constructor
  · intro h; exact ⟨(x.1,j.2),Prod.ext (congr_arg (fun z:Leaf n α=>z.1) h) rfl,Prod.ext rfl (congr_arg (fun z:Leaf n α=>z.2) h).symm⟩
  rintro ⟨a,h,rfl⟩; exact congr_arg (E n) h

end work
end Spine
end YM.AllOrder.Ker
