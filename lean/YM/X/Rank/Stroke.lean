import YM.X.Rank.Pairwise
/-!
# Sampling real flavor-colors with light probes at every finite list of primary sites.

No Gram rank hypothesis on the diagnostic. The one-leg tests have exactly
homogeneous powers at any fixed derivative order. Their coefficients determine
flavor; also they can be separated from finitely many other evaluation points
without Laplace uniqueness on any *interacting* correlator.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Rank
open Function Set Filter Maxwell Wick Maxwell.Free Next.Rank.Normal MvPolynomial Rad
open scoped Topology BigOperators Classical
variable {G : Gauge} {S : Finset E4} {a b m d v u : E4}(c : G.ColorIndex) {P: Canvas G}

private lemma shade_cost (j:Stroke)(d:E4)(hd:d≠0)(p: Flavor 0)(n:ℕ)(hn : j.2.1 ≤ n) (x : E4) :
    Tendsto (fun t:ℝ=> (t⁻¹)^(4+n)*pay c (x-t⁻¹ • d,p) j) atTop (𝓝 (if j.1=x ∧ j.2.1=n then fare c (ax j.2.1 j.2.2) p d else 0)):= by
   let y (t:ℝ):=j.1-(x-t⁻¹ • d); have ht : Tendsto (fun t:ℝ=>t⁻¹) atTop (𝓝 0):= tendsto_inv_atTop_zero; let f:= fare c (ax j.2.1 j.2.2) p
   by_cases hc : j.1=x
   · have he t : y t=(t:ℝ)⁻¹ • d:= by unfold y; rw [hc]; abel
     have hL : (fun t:ℝ=>(t⁻¹)^(4+n)*pay c (x-t⁻¹ • d,p) j)=ᶠ[atTop] fun t:ℝ=>(t⁻¹)^(n-j.2.1)*f d:= by
       filter_upwards [eventually_gt_atTop (0:ℝ)] with t hp
       let r:ℝ:= t⁻¹; have hr:0<r:=inv_pos.mpr hp
       have hD:y t≠0:= (he t).trans_ne (smul_ne_zero hr.ne' hd)
       change _*(if j.1=x-r • d then _ else f (y t))=_; rw [if_neg (show j.1≠x-r • d from sub_ne_zero.mp hD), he]
       rw [show f (t⁻¹ • d)= (r⁻¹)^(4+j.2.1)* f d from (kernel_pole ..).degree r hr d hd]
       change r^(4+n)* (r⁻¹^(4+j.2.1)*f d)=r^_*f d
       rw [show 4+n=n-j.2.1+(4+j.2.1) by omega,pow_add]; field_simp; rw [div_pow,one_pow]; field_simp
     by_cases he' : j.2.1=n
     · rw [if_pos ⟨hc,he'⟩]; apply Tendsto.congr' hL.symm; simp only [he',Nat.sub_self,pow_zero,one_mul]; exact tendsto_const_nhds
     rw [if_neg (fun h=>he' h.2)]; apply Tendsto.congr' hL.symm
     simpa only [zero_pow (by omega : n-j.2.1≠0),zero_mul] using! (ht.pow (n-j.2.1)).mul_const (f d)
   have hv:j.1-x ≠0:=sub_ne_zero.mpr hc; have hy:Tendsto y atTop (𝓝 (j.1-x)) := by simpa only [zero_smul, sub_zero] using! (tendsto_const_nhds (x:=j.1)).sub ((tendsto_const_nhds (x:=x)).sub (ht.smul_const d))
   have hf : ContinuousAt f (j.1-x):=(kernel_smooth _ _ hv).continuousAt 
   have hh:= (ht.pow (4+n)).mul (hf.tendsto.comp hy)
   rw [zero_pow (by omega), zero_mul] at hh; rw [if_neg (fun h=>hc h.1)]
   apply hh.congr'; filter_upwards [hy.eventually (eventually_ne_nhds hv)] with t h; exact congr_arg (t⁻¹^ _ * ·) (if_neg (show j.1≠x-t⁻¹ • d from sub_ne_zero.mp h)).symm

lemma paid_layer (s: Finset Stroke)(p:Stroke→ℝ)(S:Finset E4) (hp:∀ w:Scout,w.1∉ S → ∑ i∈s,p i*pay c w i=0)(x:E4)(n:ℕ) (hn:∀ i∈s,(i:Stroke).2.1≤n):
    let u(k:Ax n) := ((x,⟨n,k⟩) : Stroke); let V := Finset.univ.filter (fun k => u k ∈ s)
    ∑ k∈ V,p (u k) • (ax n k)=0 := by
  intro u V; apply payment c; intro z hz q; let H:=(assay c hz n 0).flip q
  change H (∑ k∈ V, _) = 0
  rw [map_sum]; simp_rw [map_smul]
  let A(i:Stroke):= if i.1=x∧i.2.1=n then fare c (ax i.2.1 i.2.2) q z else 0
  have hS : ∑ i∈s,p i*A i=0:= by
    have ht:= tendsto_finsetSum s fun i hi=> (shade_cost c i z hz q n (hn i hi) x).const_mul (p i)
    apply tendsto_nhds_unique ht
    let f (t:ℝ):= x-t⁻¹ • z; have hi:Injective f:= fun u v he=> inv_injective (smul_left_injective ℝ hz (sub_right_inj.mp he))
    have hI := (hi.tendsto_cofinite.mono_left atTop_le_cofinite).eventually (p:=fun x=>x∈ (S:Set E4)ᶜ) S.finite_toSet.compl_mem_cofinite
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hI] with t hI; simp_rw [fun i=>mul_left_comm (p i) (t⁻¹^(4+n)), ← Finset.mul_sum, hp (x-t⁻¹ • z,q) hI,mul_zero]
  rw [← hS]
  let T(i:Stroke): Prop:=i.1=x ∧ i.2.1=n
  let s':= s.filter T
  have hd : s'= V.image u := by
    ext j; rcases j with ⟨a,b,y⟩; constructor
    · rintro h; obtain ⟨h,h'⟩:=Finset.mem_filter.mp h; change a=x∧b=n at h'; obtain ⟨rfl,rfl⟩:=h'; exact Finset.mem_image.mpr ⟨y,(by simp [* ,V,u]),rfl⟩ -- dependent subst?
    intro h; obtain ⟨w,h,he⟩:= Finset.mem_image.mp h; rw [← he]
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h).2,⟨rfl,rfl⟩⟩
  symm; calc
    _=∑ i∈s',p i*A i:= Eq.symm (Finset.sum_subset (Finset.filter_subset _ _) (fun i hi h=>by unfold A; rw [if_neg (show ¬ T i from fun hz=>h (Finset.mem_filter.mpr ⟨hi,hz⟩)),mul_zero]))
    _ = _:= by
      rw [hd,Finset.sum_image]; refine Finset.sum_congr rfl ?_; intro j hj; simp only [A,u,and_self,↓reduceIte]; rfl
      intro i _ j _ H; exact Sigma.mk.inj_iff.mp (Prod.mk.inj H|>.2) |>.2 |> eq_of_heq

lemma controls (s: Finset Stroke)(p:Stroke→ℝ)(S:Finset E4) (hp:∀ w:Scout,w.1∉ S → ∑ i∈s,p i*pay c w i=0) (v:Stroke)(hv:v∈s) : p v=0 := by -- edit syntax
  let t:=s.filter fun i=>p i≠0; by_contra! h; have ht:v ∈ t := Finset.mem_filter.mpr ⟨by assumption,h⟩
  obtain ⟨⟨x,n,i⟩,hx,hN⟩:= Finset.exists_max_image t (fun u=> u.2.1) ⟨v,ht⟩
  have hy:= paid_layer c t p S (fun w hw=>by rw [← hp w hw]; exact Finset.sum_subset (Finset.filter_subset _ _) fun i hi h=>by rw [show p i=0 from ?_,zero_mul]; exact Classical.byContradiction fun hr=>h (Finset.mem_filter.mpr ⟨hi,hr⟩)) x n hN
  apply (Finset.mem_filter.mp hx).2
  let X(k:Ax n):Stroke:=(x,⟨n,k⟩); let V:=Finset.univ.filter fun i=> X i∈ t
  change ∑ k∈V, p (X k) • (ax n k)=0 at hy; apply_fun ((ax n).coord i) at hy; have hV: i∈V:= Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩
  rw [map_zero,map_sum,Finset.sum_eq_single_of_mem i hV] at hy
  · simpa using hy
  intro j hj H; simp [H,Ne.symm H]
end YM.PositionX.Rank
