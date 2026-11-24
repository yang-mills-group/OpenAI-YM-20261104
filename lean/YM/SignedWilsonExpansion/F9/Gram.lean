import YM.SignedWilsonExpansion.F9.PaceB
import YM.SignedWilsonExpansion.F9.Adapter
import YM.XSpace.Terrain
import YM.Extra.FREE_DETECTOR_ALGEBRA.LabelTurn
import YM.Next.MAXWELL.Battery
/-!
# Native full-height observable reflected pair with Hermitian margin.

Legacy derivation uses Price.PublicWickGram for particular basis. Here arbitrary polarizations
include all rank-availability orientations. Exact MS kernel `dependent Eq2Position` later calls.
-/
set_option autoImplicit false
set_option maxHeartbeats 305000
noncomputable section
namespace YM.SignedWilsonExpansion.Commission.Gram
open WilsonCoeffUV.Bank Function Filter Set MeasureTheory Lattice
open scoped BigOperators Topology ContDiff Classical Matrix ComplexOrder
open Source Labels Maxwell Maxwell.Free Maxwell.Wick Extra Extra.FD XSpace XSpace.Normalize XSpace.Structure1
variable {ι σ σ':Type} {G:Gauge} {n r d:ℕ}
variable (l:Filter ι)(q:ι→ℝ)
variable [Fintype σ]
section pair
def vertex (a:Axis) : E4 := (2:ℝ)⁻¹•basis a
def nodes (a:Axis) : Points 2 := FD.couple (vertex a) (-(vertex a))

theorem apart (a:Axis) : vertex a - (-(vertex a)) = basis a := by
  unfold vertex
  module

private theorem face_axis (a:Axis) : FD.face (basis a) = Signed.reflect a := by
  apply Subtype.ext
  ext i j
  change FD.faceM (basis a) i j=_
  rw [reflect_entry]
  have one : ‖basis a‖=1 := basis_norm _
  simp [FD.faceM,FD.rr,YM.basis,Free.parity]
  grind

private theorem pull (x:WickPol G) (t:Signed) : FD.pullSol t.ortho x = reflectPol t.ortho x := by
  conv_lhs => arg 2; rw [← On.lift_recover x]
  rw [← FD.watch_rot,← On.lift_signed,On.lift_recover]

lemma opening (a:Axis): vertex a≠ -(vertex a):=by
    intro v; have hp:= congr_arg norm ((apart a).symm.trans (sub_eq_zero.mpr v)); rw [basis_norm,norm_zero] at hp; exact one_ne_zero hp
lemma nodes_conf (a:Axis): nodes a ∈ conf 2:= Extra.FD.couple_ok (opening a)
def flipE (a:Axis)(x:Sec G d): Sec G d:= Normalize.ori (Signed.reflect a) d (Normalize.reel d x)
def flipR (a:Axis)(d:ℕ): Sec G d→ₛₗ[starRingEnd ℂ] Sec G d:=(Normalize.ori (Signed.reflect a) d).comp (Normalize.reel d)
lemma setting (x y:Sec G d)(a:Axis) : scene (nodes a) d ![x, flipE a y]=duplex (vertex a) (-(vertex a)) x.val y.val:=by
    unfold duplex flipE; rw [ aligned_apply,apart,face_axis, Signed.reflect,pull, Normalize.screen ]; unfold FD.join; apply congrArg; ext1 v; fin_cases v <;> rfl
-- strict finite price and stability
variable (a:Axis)(B:Module.Basis σ ℂ (Sec G d)) (P:XSpace.Structure1.Point G d 2)
variable {E:Type}[AddCommGroup E][Module ℂ E]
abbrev BI (E:Type)[AddCommGroup E][Module ℂ E]:= MultilinearMap ℂ (fun _:Fin 2=> E) ℂ
lemma swap0 (x y z:E) : Function.update (![x,y]:Fin 2→E) 0 z=![z,y]:= funext fun i=> Fin.cases (by simp) (fun j=> by fin_cases j; simp) i
lemma swap1 (x y z:E) : Function.update (![x,y]:Fin 2→E) 1 z=![x,z]:=by ext1 i; fin_cases i <;> simp
-- Bilinear, not starred cost
noncomputable def actsB (L:BI E)(y:E): Module.Dual ℂ E where
   toFun x:= L ![x,y]
   map_add' x y':=by rw [← swap0 0 y (x+y'), MultilinearMap.map_update_add]; rw [swap0,swap0]
   map_smul' c x:=by rw [← swap0 0 y (c • x), MultilinearMap.map_update_smul,swap0]; rfl
noncomputable def acts (L:BI E): E→ₗ[ℂ]Module.Dual ℂ E where
   toFun y:= actsB L y
   map_add' x y:= by ext1 p; change L ![p,x+y]= L _ + L _; rw [← swap1 p 0 (x+y),MultilinearMap.map_update_add,swap1,swap1]
   map_smul' c x:= by ext1 p; change L ![p,c • x]=c • L _; rw [← swap1 p 0 (c • x),MultilinearMap.map_update_smul,swap1]
lemma coupled (L:BI E)(x y:E): acts L y x= L ![x,y]:=rfl
noncomputable abbrev basisT (a:Axis)(B:Module.Basis σ ℂ (Sec G d)) (P:XSpace.Structure1.Point G d 2) : σ→σ→ℂ:= fun i j=>P ![B j,flipE a (B i)]
lemma cone (x y: Sec G d): P ![x,flipE a y]=Adapter.assay (B.equivFun y) (B.equivFun x) (basisT a B P):=by
    nth_rw 1 [← coupled, ← B.sum_repr x, ← B.sum_repr y]; -- flipE plain def rewrite
    have hp: flipE a (∑ i, B.repr y i • B i)=∑ i,star (B.repr y i) • flipE a (B i):=by let Q:=flipR (G:=G) a d; change Q (∑ i,_) = _; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> Q.map_smulₛₗ _ _
    rw [hp,map_sum (acts P),LinearMap.sum_apply]; unfold Adapter.assay; apply Finset.sum_congr rfl; intro i _; rw [map_smul, LinearMap.smul_apply,map_sum, Finset.smul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul, smul_smul]; rfl
lemma transposes (q: (Sec G d →ₗ[ℂ] Sec G d)) (B':Module.Basis σ' ℂ (Sec G d)) (H : Function.Injective q) : LinearIndependent ℂ (fun i :σ'=> (q (B' i)).val) :=by
    -- no Fintype
    exact B'.linearIndependent.map' ((Maxwell.shellSector G d).subtype ∘ₗ q) (LinearMap.ker_eq_bot.mpr (Subtype.val_injective.comp H))
lemma prescribed : (Matrix.of (basisT a B (scene (nodes a) d))).PosDef:=by
    unfold basisT; simp_rw [setting]; exact FD.reflected_pd (opening a) _ (transposes (LinearMap.id) B Function.injective_id)
-- at ANY approaching kernel (not necessarily a Gram transformed itself (smeared geometry))
variable (pM':ι→BI (Sec G d)) (U:∀ i j :σ,Tendsto (fun v:ι=> (Gram.basisT a B (pM' v) i j:ℂ)) l (𝓝 (basisT a B (scene (nodes a) d) i j)))
include U
lemma house : ∃ k:ℝ,0<k ∧ ∀ᶠ v:ι in l,∀ x:Sec G d, k*‖B.equivFun x‖^2 ≤ (pM' v ![x,flipE a x]).re:=by
    let V:=basisT a B ∘ pM'; let Q:=basisT a B (scene (nodes a) d); have he : Tendsto V l (𝓝 Q):= tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=> U i j
    obtain ⟨k,δ,hk,hδ,hh⟩:= Adapter.stable Q (prescribed a B); exact ⟨k,hk,(he.eventually (Metric.closedBall_mem_nhds _ hδ)).mono fun i hi x=> (cone a B _ x x).symm ▸ hh (V i) (by simpa [Metric.mem_closedBall,dist_eq_norm] using hi) _⟩
end pair
end YM.SignedWilsonExpansion.Commission.Gram
