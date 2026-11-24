import YM.RGComparison.Core16.Forge.Hut
/-!
# Tag coupling for displacement replacement

Single square-zero-family expectation must use this for WHOLE U(s) and W(t). Supports genuine
whenever likelihoods. Neighbor site tags shared by all touching bonds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge
open Function Filter Finset Lattice RG Wilson Tree Pressure MeasureTheory Push.GridApprox
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

section Couplings
variable {k R T:Type} [Fintype R] [Fintype T] [Fintype k]

lemma sample (a b:T→ℝ)(h1:∀i,0≤a i)(h2:∀i,0≤ b i)(ha:∑ i,a i=1)(hb:∑ i,b i=1):
   ∃ M:T→T→ℝ, Glued a b M ∧ ∀ i j,0<M i j→a=b→i=j:=by
   by_cases he:a=b
   · subst b; refine ⟨fun i j=> if i=j then a i else 0, ⟨fun i j=>by split; exact h1 i; rfl,?_,?_⟩,?_⟩
     · intro i; simp
     · intro i; simp
     · intro i j h _; by_contra! hh; simp [hh] at h
   refine ⟨fun i j=> a i*b j,⟨fun i j=>mul_nonneg (h1 i) (h2 j),fun i=>by rw [←mul_sum,hb,mul_one],fun j=>by rw [←sum_mul,ha,one_mul]⟩,fun _ _ _ hx=>False.elim (he hx)⟩

lemma village  [DecidableEq k] (u v : k→ T→ℝ)(h1:∀k i,0≤u k i)(h2:∀k i,0≤v k i)(ha:∀k,∑ i,u k i=1)(hb:∀k,∑ i,v k i=1) :
   ∃ M:(k→T)→(k→T)→ℝ, Glued (fun i=> ∏ j,u j (i j)) (fun i=>∏ j,v j (i j)) M ∧ ∀ i j, 0<M i j→∀p,u p=v p→i p=j p:=by
   choose Z hX hx using fun k=> sample (u k) (v k) (h1 k) (h2 k) (ha k) (hb k)
   let M (f g:k→T):= ∏ i, Z i (f i) (g i)
   refine ⟨M, ⟨fun i j=> prod_nonneg (fun k _=>(hX k).pos ..), fun i=>?_, fun j=>?_⟩, fun i j hh p=> hx _ _ _ ?_⟩
   · unfold M; simp_rw [← (hX _).west]; rw [Fintype.prod_sum]
   · unfold M; simp_rw [← (hX _).east]; exact (Fintype.prod_sum (κ:=fun _ : k=> T) (fun a r=> Z a r (j a))).symm -- η
   have h:0≤Z p (i p) (j p):=(hX p).pos ..; refine lt_of_le_of_ne h ?_; rintro e; exact hh.ne' (prod_eq_zero (mem_univ p) e.symm)

-- The common parent kernel and THEN conditional product. Exist/witness not reordered by positivity.
lemma partnered {a b:R→ℝ} (u v:R→ T→ℝ) {M:R→R→ℝ} {f:R→R→T→T→ℝ} (h:Glued a b M) (hp:∀i j,Glued (u i) (v j) (f i j)) :
    Glued (T:=R×T) (fun j=> a j.1*u j.1 j.2) (fun j=> b j.1*v j.1 j.2)
      (fun i j=> M i.1 j.1*f i.1 j.1 i.2 j.2) := by
    refine ⟨fun i j=> mul_nonneg (h.pos ..) ((hp ..).pos ..), ?_, ?_⟩
    · intro i; rw [Fintype.sum_prod_type]; dsimp only; simp_rw [← mul_sum, (hp ..).west]; rw [←sum_mul,h.west]
    intro j; rw [Fintype.sum_prod_type]; dsimp only; simp_rw [←mul_sum,(hp ..).east]; rw [←sum_mul,h.east]
end Couplings

namespace Hut
variable {G:Gauge} {c f:Side}{S: StepData c f}(hS:S.patch.Branches S.kernel G)(T:Forest S.ratio)(V:Config G c)
include hS
set_option maxHeartbeats 240000 in
lemma local_tags : (seam S T V).Meets (width S.patch):=by
    intro z x y R hXY
    let m (u:Sky G T.Free)(i:Site c) := S.patch.frameMass S.kernel (expandAt (hold S i) (T.drape u))
    let b (u:Sky G T.Free) (t:S.SitesChoice)(e:Edge (Site c)):= S.patch.predictorMass S.kernel (S.connector (T.drape u) t e)
    have hm (u : Sky G T.Free)(i:Site c)(j:S.patch.FrameTag):0≤ m u i j:=by unfold m Patch.frameMass; split; positivity; split <;> positivity
    have hb (u : Sky G T.Free)(t:S.SitesChoice)(e:Edge (Site c))(j:S.patch.Points):0≤ b u t e j:=by unfold b Patch.predictorMass; split; positivity; exact S.patch.weight_nonneg _
    obtain ⟨M,hM,he⟩:= village (m x) (m y) (hm x) (hm y) (fun _=>S.patch.frameMass_sum hS _) (fun _=> S.patch.frameMass_sum hS _)
    choose L hL hl using fun s t: S.SitesChoice=>village (b x s) (b y t) (hb x s) (hb y t) (fun _=> S.patch.predictorMass_sum (C:=S.kernel) _) (fun _=> S.patch.predictorMass_sum (C:=S.kernel) _)
    let P:=width S.patch
    let α(s:Sky G T.Free)(i:S.SitesChoice):=∏ j,m s j (i j)
    let β(s:Sky G T.Free)(i:S.SitesChoice)(j:S.BondChoice):=∏ e,b s i e (j e)
    let μ(s:Sky G T.Free)(i:S.Choices):=α s i.1 * β s i.1 i.2
    let K (i j:S.Choices):= M i.1 j.1 * L i.1 j.1 i.2 j.2
    have hp1 : Glued (α x) (α y) M := hM
    have hp2 (i j:S.SitesChoice): Glued (β x i) (β y j) (L i j):= hL i j
    refine ⟨K,?_,fun i j h p hp=> ?_⟩
    · rw [show swap _ x= μ x from rfl, show swap _ y=μ y from rfl]; exact partnered (β x) (β y) hp1 hp2
    change 0<M i.1 j.1*L i.1 j.1 i.2 j.2 at h
    have h1:= pos_of_mul_pos_left h ((hL ..).pos ..); have h2:= pos_of_mul_pos_right h (hM.pos ..)
    let l:= root S p
    have hv: R+P < separation z l:= Nat.lt_of_not_ge (fun hz=>hp ((member ..).2 hz))
    have ht q (hq:q∈neighborsOf (pad T) P l):x q=y q:=by
        apply hXY; intro hi; refine (not_lt_of_ge ((separation_triangle _ (pad T q) _).trans (Nat.add_le_add ((member ..).1 hi) ((separation_comm ..).trans_le ((member ..).1 hq))))) hv
    rcases p with p|p
    · exact congr_arg G.price (stele ht)
    have hh: l=hold S p.1:= rfl
    have hf (u:Site c)(hu : separation l (hold S u) + reach S.patch ≤ P) : i.1 u=j.1 u := he i.1 j.1 h1 _ (funext fun k=> (site_dep S hS u (wires ht hu) k).2)
    have ha:= stitch hS (b:=p) (hf p.1 (by rw [hh,separation_self]; unfold P width; omega)) (hf (p.1+step p.2) (by rw [hh]; unfold P width; have hP:= neighbour (S:=S) p; omega)) ht
    have hz := hl _ _ i.2 j.2 h2 p (show b x i.1 p=b y j.1 p from by unfold b; rw [ha]); change Push.BetaTransport.linkEnergy S (V p * (S.prediction (T.drape x) i p)⁻¹)= Push.BetaTransport.linkEnergy S (V p * (S.prediction (T.drape y) j p)⁻¹); unfold StepData.prediction; rw [ha,hz]
end Hut
end YM.RGComparison.Core16.Forge
