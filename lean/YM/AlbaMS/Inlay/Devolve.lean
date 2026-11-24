import YM.AlbaMS.Inlay.Receipt

/-! # transport the Ward symbols. Only sum last at each link. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Inlay.Net.Receipt
open Set Function Filter Gauge NormedSpace MeasureTheory LocalH Push.Loops LinearMap
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal Matrix
open Nexus Loft Loft.Chart Chart.Grove Bric Coil
variable {V W I J R : Type*}{G:Gauge} {Ω:Net V I}{H:Net W J}(u:Receipt G Ω H)
variable [Fintype V][Fintype W][Fintype I][Fintype J]
lemma passA (i:Flit G V): u.track (A ℝ i)= ∑ j:Flit G W,u.φ i j • A ℝ j:=by unfold A; rw [u.vary]; simp only [Fintype.sum_sum_type,Place.a,skein,zero_smul,Finset.sum_const_zero,add_zero]
lemma passK (i:Flit G V): u.track (K ℝ i)= ∑ j:Flit G W,u.φ i j • K ℝ j:=by unfold K; rw [u.vary]; simp only [Fintype.sum_sum_type,Place.k,skein,zero_smul,Finset.sum_const_zero,add_zero,zero_add]
lemma passC (i:Flit G I): u.track (C ℝ i)= ∑ j:Flit G J,u.ε i j • C ℝ j:=by unfold C; rw [u.vary]; simp only [Fintype.sum_sum_type,Place.c,skein,zero_smul,Finset.sum_const_zero,add_zero,zero_add]
lemma passL (i:Flit G I): u.track (L ℝ i)=∑ j:Flit G J,u.rate i.1 • u.ε i j • L ℝ j:=by unfold L; rw [u.vary]; simp only [Fintype.sum_sum_type,Place.l,skein,zero_smul,Finset.sum_const_zero,zero_add,smul_smul]
-- want exact formula even before scaling. Frame uses Leg kernel for later physical orientation via Wind.
omit [Fintype J] in
private lemma windChat (x:Flit G V)(y:Flit G J):
    (∑ i:Flit G W,u.φ x i • H.chat y i)=∑ i:Flit G I,u.ε i y • u.track (Ω.chat i x):=by
  let A:=pathof G W J
  let Y:=slabQ y
  let F: Grove (ink G W):= ⟨stip x ∘ u.inkmap ∘ H.fly Y, (stip x ∘ₗ u.inkmap).toContinuousLinearMap.contDiff.contDiffAt.comp (f:=H.fly Y) _ (H.wax_rate (A:=0) (fun _=> (quill G).self_of_nhds) Y)⟩
  let pill (i:Flit G I):=Brook.dive (Ω.spotG i x) u.inkmap.toContinuousLinearMap
  have hs : F.val=∑ i:Flit G W, (u.φ x i • H.spotG y i).val:=by
    ext1 P; rw [Finset.sum_apply]; change stip x (u.inkmap (H.fly Y P))=_; rw [← slab_total (H.fly Y P),map_sum,map_sum]; simp_rw [map_smul]; refine Finset.sum_congr rfl (fun i _=>?_); exact mul_comm (stip i (H.fly Y P)) (u.φ x i)
  -- provide common marked input coordinates. all natural premises no h assumed beyond patch.
  have hv : ∀ᶠ q:G.Color in 𝓝 0, Quill (G.adjoint u.color q):= by have ht:=(G.adjoint u.color).toContinuousLinearMap.continuous.tendsto (0:G.Color); rw [map_zero] at ht; exact ht.eventually (quill G)
  have he: F.val=ᶠ[𝓝 0] ∑ i:Flit G I,(u.ε i y • pill i).val:=by
    let L:=u.inkmap.toContinuousLinearMap; have ht:=L.continuous.tendsto (0:ink G W); rw [map_zero] at ht
    filter_upwards [tide (G:=G) (V:=W), ht.eventually (tide (G:=G)), ((continuous_apply (u.parcel x.1)).tendsto (0:ink G W)).eventually hv] with z hu h hd
    rw [Finset.sum_apply]; change stip x (u.inkmap (H.fly Y z))=_; rw [stip_at,← u.natural z Y x.1 (hu _) hd (h _), ← stip_at x]; change stip x (Ω.current (u.inkmap z) (u.ghost Y))=_; rw [← slab_total (u.ghost Y)]; simp_rw [map_sum,map_smul]; rfl
  refine Eq.trans (b:=A.shine F) ?_ ?_ -- fix
  · have hf:= A.flash F _ _ (Filter.EventuallyEq.of_eq hs); simp_rw [Brook.gleam_smul] at hf; exact hf.symm
  have hf:= A.flash F _ _ he; simp_rw [Brook.gleam_smul] at hf; simp_rw [chat,u.action]; exact hf
lemma forwarding (x:Flit G V): u.track (beam Ω.chat x) = ∑ i:Flit G W,u.φ x i • beam H.chat i:=by
  unfold beam; rw [map_sum]; simp_rw [u.times,u.passC,Finset.sum_mul, Finset.smul_sum]; rw [Finset.sum_comm]; rw [Finset.sum_comm (s:=(Finset.univ:Finset (Flit G W)))]; refine Finset.sum_congr rfl fun y _=>?_ ; simp_rw [smul_mul_assoc, ← mul_smul_comm, ← Finset.mul_sum]; rw [windChat]
-- rod transport similar. bracket skeleton alone.
omit [Fintype V] [Fintype W] in
lemma rolling (x:Flit G I)(y z : Flit G J): (∑ i:Flit G J,u.ε x i*(grit G J).price y z i)=∑ i:Flit G I,∑ j:Flit G I,u.ε i y*u.ε j z*(grit G I).price i j x :=by
  -- identify ad bracket intertwiner. commute through true material, no tensor assertions
  let X:=adI (slabQ y) (slabQ z)
  have hh : (∑ i:Flit G J,u.ε x i*(grit G J).price y z i)= stip x (u.ghost X):= by rw [← slab_total X,map_sum,map_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,map_smul, grit_price]; exact mul_comm ..
  rw [hh,u.ghostAd]; -- ghostAd doesn't find X
  let a: ink G I→ₗ[ℝ] G.Color:= proj x.1
  let B:= ((G.ad.comp a).compl₂ a).compr₂ (coefQ x.2)
  change B (u.ghost (slabQ y)) (u.ghost (slabQ z))=_; nth_rw 1 [← slab_total (u.ghost (slabQ y))]; rw [← slab_total (u.ghost (slabQ z))]; simp_rw [LinearMap.map_sum₂, LinearMap.map_smul₂]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_sum]; simp_rw [Finset.smul_sum,map_smul]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [grit_price,smul_smul]; rfl
lemma riding (x:Flit G I): u.track (rod (grit G I) x) = ∑ i:Flit G J,u.ε x i • rod (grit G J) i:=by
  have hn (f:Flit G I→Flit G I→Flit G J→Flit G J→Heave G W J ℝ): (∑ i:Flit G I,∑ j:Flit G I,∑ a:Flit G J,∑ b:Flit G J,f i j a b)=∑ a:Flit G J,∑ b:Flit G J,∑ i:Flit G I,∑ j:Flit G I,f i j a b:= by
    simp_rw [Finset.sum_comm (f:=fun j a=>∑ b:Flit G J,f _ j a b)]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [Finset.sum_comm (f:=fun j b=> f _ j i b)]; rw [Finset.sum_comm]
  unfold rod
  rw [map_smul, map_sum]; simp_rw [map_sum]; simp_rw [map_smul,u.times,u.passC]; simp_rw [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]; rw [hn]; -- explicit inspect
  let Q (i j:Flit G J): Heave G W J ℝ:= C ℝ i*C ℝ j
  rw [Finset.sum_comm (f:=fun v : Flit G J=>fun a:Flit G J=>∑ b:Flit G J, u.ε x v • (-halve ℝ • ((grit G J).price a b v • (C (E:=Flit G W) ℝ a*C ℝ b))))]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [Finset.sum_comm (s:=(Finset.univ:Finset (Flit G J))) (t:=(Finset.univ:Finset (Flit G J)))] -- arg? 
  refine Finset.sum_congr rfl fun b _=>?_ ; simp_rw [smul_mul_assoc,mul_smul_comm, smul_smul]; simp_rw [← Finset.sum_smul]; refine congr_arg (fun x:ℝ=> x • Q a b) ?_
  have he i j : -halve ℝ * ((grit G I).price i j x*(u.ε i a * u.ε j b))= -halve ℝ * (u.ε i a*u.ε j b * (grit G I).price i j x):=by ring
  simp_rw [he, ← Finset.mul_sum,← u.rolling]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> by ring
end YM.MSBar.Inlay.Net.Receipt
