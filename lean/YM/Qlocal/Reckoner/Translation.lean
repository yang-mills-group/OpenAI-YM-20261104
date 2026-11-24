import YM.Qlocal.Reckoner.Planet
import YM.Qlocal.Reckoner.Cardinals
import YM.Next.MULTISOURCE.Formal
/-! Export coefficients from the EMERGENCE algebra to any desired actual one.
Use also for precise deletion/call interactions. Bind estimator outputs to one coherent
model with tag loans.We show compatibility and prove the pressure conversion.
No requirement each surgery product have a realized monomial; disappeared marks
properly represented (also in old K products and prerender log sensors!).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner
open Function RG Lattice Wilson Pert.Attach MeasureTheory Filter Progress.DirectedRecipe Finset
open Marker RG03.Gather Push.AbsoluteSums RG3.Press
open scoped Topology ContDiff BigOperators Classical
open Publishing Parabola Integration.RiderTastePresentation Integration.LocalComparison Extra.Trajectories
variable {V I Ω J J' J₀ K α:Type}[DecidableEq V][DecidableEq I]{G:Gauge}{n:Side}{R:Census I}
variable {X: RG.Rep G n}{s:V→ Support n}{s':I→Support n} {A A' B B' u v a r t w δ:ℝ} {o: V→Site n}{o':I→Site n}
namespace Translation
open Planet
variable [Fintype V]
set_option quotPrecheck false
local notation "Ψ"=> Whole V
variable (T:V→R.Mode) (f:V→ℂ) (hp:∀ i,(T i).val.Nonempty)
local notation "b"=>fun i:V=> Poly.send (T i) (f i)
noncomputable def ticketL : Poly (Whole V)→ₗ[ℂ] Poly R:= ∑ i:(Whole V).Mode, LinearMap.smulRight (Poly.get i).toLinearMap (∏ j∈i.val,Poly.send (T j) (f j))
noncomputable abbrev stamp (p:(Whole V).Mode): R.Mode:= if h: Fits T p.val then unionTag T p.val h else R.quiet
abbrev falls (p:(Whole V).Mode):= if Fits T p.val then (∏ i∈p.val,f i) else 0
lemma accepts (v : Poly (Whole V)) : ticketL T f v=∑ i : (Ψ).Mode, v.part i • zProd (Z:=b) i.val:=by unfold ticketL; rw [LinearMap.sum_apply]; rfl
lemma ticket_send (p:(Whole V).Mode)(c:ℂ) : ticketL T f (Poly.send p c)= c • zProd (Z:=b) p.val:=by
 rw [accepts,Finset.sum_eq_single p]; · rw [Poly.part_send,if_pos rfl]
 · intro z hz hv; rw [Poly.part_send,if_neg hv, zero_smul]
 simp
lemma stamped (p:(Whole V).Mode)(c:ℂ) : ticketL T f (Poly.send p c)= Poly.send (stamp T p) (c*falls T f p):=by
 rw [ticket_send]; by_cases h: Fits T p.val
 · unfold zProd stamp falls; rw [tagged_prod T p.val h, MergeProof.Menu.sent, dif_pos h,if_pos h]
 rw [show zProd (Z:=b) p.val=0 from Classical.byContradiction (fun hv=>h (fits_of_tagged_prod T hv)),smul_zero,falls,if_neg h,mul_zero,Poly.send_zero]
noncomputable def morph : Poly (Whole V) →ₐ[ℂ] Poly R:= by
 let F:=ticketL T f; refine AlgHom.ofLinearMap F (by unfold F; change ticketL T f (Poly.send _ 1)=_; rw [ticket_send,one_smul]; exact Finset.prod_empty) ?_
 have ht(i): Poly.send (T i) (f i)* Poly.send (T i) (f i) =0:= by by_contra he; obtain ⟨z,h⟩:= merges_of_tagged_mul he; exact ((hp _).ne_empty (disjoint_self.mp h.1))
 have he (i j : (Whole V).Mode)(x y:ℂ): F (Poly.send i x*Poly.send j y)= F (Poly.send i x) * F (Poly.send j y):=by
    by_cases hb:Disjoint i.val j.val
    · let z:= pack (i.val∪j.val); have hz: Poly.merges i j z:= ⟨hb,rfl⟩; unfold F; rw [tagged_mul _ _ _ hz,ticket_send,ticket_send,ticket_send, show zProd (Z:=b) z.val=zProd (Z:=b) i.val* zProd (Z:=b) j.val from Finset.prod_union hb,mul_smul, smul_mul_assoc x, mul_smul_comm]
    unfold F; rw [show Poly.send i x* Poly.send j y=0 from Classical.byContradiction fun he=> hb ((merges_of_tagged_mul he).elim fun z hz=> hz.1), map_zero,ticket_send,ticket_send, smul_mul_assoc x,mul_smul_comm ]; unfold zProd; obtain ⟨u,hu,hv⟩:= Finset.not_disjoint_iff.mp hb; rw [← mul_prod_erase i.val _ hu,←mul_prod_erase j.val _ hv]; change _= x • y • (((b) u*_)* (_*_)); rw [mul_mul_mul_comm,ht,zero_mul,smul_zero,smul_zero]
 intro x y; rw [← Poly.studs x,← Poly.studs y]; simp_rw [Finset.sum_mul,Finset.mul_sum,map_sum,he,Finset.sum_mul,Finset.mul_sum]
variable (Z:Poly (Whole V))
include hp
local notation "P"=> morph T f hp
lemma sent (p:(Whole V).Mode)(c:ℂ): morph T f hp (Poly.send p c)= Poly.send (stamp T p) (c*falls T f p):= stamped T f p c
lemma issues (i:V): P (glyph i)= Poly.send (T i) (f i):=by
 change ticketL T f (Poly.send (pack {i}) 1)=_; rw [ticket_send,one_smul]; exact Finset.prod_singleton ..
lemma part (v:R.Mode): (P Z).part v=∑ i:(Whole V).Mode, if v=stamp T i then (Z.part i)*falls T f i else 0:= by
 nth_rw 1 [← Poly.studs Z]; simp_rw [map_sum,Poly.part_sum,sent,Poly.part_send]
lemma preserveQ : (P Z).part R.quiet= Z.part (Whole V).quiet:= by
 rw [part,sum_eq_single (Whole V).quiet]; rotate_left
 · intro l _ h; by_cases hy:Fits T l.val; swap; · simp only [falls,if_neg hy,mul_zero, ite_self]
   apply if_neg; unfold stamp; rw [dif_pos hy]; intro he
   obtain ⟨j,hj⟩:= Finset.nonempty_iff_ne_empty.mpr (fun hv:l.val=∅=>h (Subtype.ext hv)); obtain ⟨x,hx⟩:=hp j; have hv:x∈(unionTag T l.val hy).val:= Finset.mem_biUnion.mpr ⟨j,hj,hx⟩; rw [← he] at hv; exact Finset.notMem_empty _ hv
 · simp
 let p:= (Whole V); unfold stamp falls; rw [dif_pos (show Fits T (Census.quiet (Whole V)).val from fits_empty T), if_pos (show Fits T p.quiet.val from fits_empty T), if_pos (show R.quiet=unionTag T (Census.quiet p|>.val) (fits_empty T) from Subtype.ext (Finset.biUnion_empty.symm)), show (∏ i∈(Ψ).quiet.val,f i)=1 from Finset.prod_empty,mul_one] -- `..`
end Translation
end YM.Qlocal.Reckoner
