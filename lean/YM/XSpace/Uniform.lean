import YM.XSpace.PointKernels

/-!
# Technical consequence in the usual uniformity (compact, all permitted mesh points)
Point geometry only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Mesh
open Filter Function Set Lattice Expense Maxwell
open scoped Topology BigOperators ContDiff
variable {ι : Type*} {g : ι→ Mesh} {u : Filter ι} {G : Gauge} {n : ℕ}
variable (m : Mesh) (A : Initialize G) (d : Fin n → ℕ)

def note (v : ∀ i,On.Grade G (d i)) (x : Fin n→ m.p.Sites) : ℂ:= PowerSeries.coeff 0 ((A.atTuple m d x) v)
def MaxwellPoint (v : ∀ i,On.Grade G (d i)) (x : Points n): ℂ := Maxwell.Wick.moment G x (fun i=>(v i).val)
lemma smoothMaxwell (v : ∀ i,On.Grade G (d i)) {x} (hx : x ∈ conf n):ContDiffAt ℝ ∞ (MaxwellPoint d v) x := Maxwell.Wick.moment_smooth _ hx

lemma fits_compact (S : Stretched u g) (K : Set (Points n)) (h : IsCompact K): ∀ᶠ i in u,(g i).Fits K:=by
  obtain ⟨y,hy⟩ := (h.image continuous_norm).bddAbove
  filter_upwards [S.width.eventually_ge_atTop (16*y)] with n hn x hx i j
  exact (PiLp.norm_apply_le (x i) j).trans ((PiLp.norm_apply_le x i).trans ((hy (Set.mem_image_of_mem _ hx)).trans (by change 16*y≤ (g n).size at hn; linarith)))

lemma difference (x : ι→ Fin n → Cover) (c : ι→ Four ℝ) (i j : Fin n):
    Cross.far g (fun k=> x k i) (fun k=> x k j)=fun k=> (g k).rel (x k) (c k) i - (g k).rel (x k) (c k) j:= by funext k; rw [Cross.far,Cross.rcast_sub,smul_sub]; change _= (g k).coord (x k i)-_ - ((g k).coord (x k j)-_); rw [sub_sub_sub_cancel_right]; rfl

lemma uniform (S : Stretched u g) (K : Set (Points n)) (h : IsCompact K) (hp : K⊆conf _) (v : ∀ i,On.Grade G (d i)):
    ∃ C:ℝ,0<C ∧ ∀ᶠ i in u, ∀ x : Fin n→Cover,∀ c∈(g i).Box,(g i).rel x c∈K→ ‖note (g i) A d v (wrap (g i).p.side ∘ x)- MaxwellPoint d v ((g i).rel x c)‖ ≤ C*(g i).spacing :=by
  let X:= ι × (Fin n → Cover) × Four ℝ
  let m : X → Mesh:= fun x=> g x.1; let F (x : X):=x.1; let p (x : X):=x.2.1; let c(x:X):=x.2.2
  let z x:= (m x).rel (p x) (c x)
  let D:=setOf fun i:X=> c i∈(m i).Box∧z i∈ K; let U:= comap F u ⊓ 𝓟 D
  have HH:Tendsto F U u:= tendsto_iff_comap.mpr inf_le_left
  have hd:∀ᶠ i in U,i∈D:=Eventually.filter_mono inf_le_right (eventually_principal.mpr fun _ h=> h)
  have S' : Stretched U m:= S.wider HH
  have hk: Rate U m (fun i=> note (m i) A d v (wrap (m i).p.side ∘ p i)) (fun i=>MaxwellPoint d v (z i)):=Price.kv_point A S' p z d (fun i j hij=> ?_) (fun j=> ?_) (fun i j=> difference ..) (hd.mono fun i hi=> hp (show c i∈(m i).Box ∧ z i∈K from hi).2) _
  · obtain ⟨C,hC,H⟩:=hk.bounds; unfold U at H; rw [eventually_inf_principal,eventually_comap] at H
    exact ⟨C,hC,H.mono (fun i hi x c hv hh=> hi (i,x,c) rfl (show _∧_ from ⟨hv,hh⟩))⟩
  · let f (x : Points n):= x i-x j
    refine Cross.rout_of_compact (h.image (f:=f) (by unfold f; fun_prop)) ?_ _ ?_
    · rintro _ ⟨k,hk,rfl⟩; exact sub_ne_zero.mpr ((show Function.Injective k.ofLp from hp hk).ne hij)
    exact hd.mono (fun i hi=> Set.mem_image_of_mem f (show c i∈(m i).Box ∧ z i∈ K from hi).2)
  · exact hd.and (fits_compact S' K h)|>.mono (fun i hi=> Cross.near_sector _ (p i) _ (show c i∈(m i).Box∧_ from hi.1).1 K hi.2 (show c i∈(m i).Box ∧ _ from hi.1).2 j)
end YM.XSpace.Mesh
