import YM.XSpace.Liken
/-! # When warmed lower degrees aren't seen by the triangular diagnostic. Used on compact shapes. -/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Relief
open Function Set Filter Lattice Trace Chart2 Maxwell Maxwell.Free Photo Cirrus Foundation Chiral Graph3 Stall Playpen Future Mu JetGauge Pages Next.Rank.Normal MvPolynomial Finsupp Asymptotics
open scoped Topology BigOperators InnerProductSpace Classical
variable {G:Gauge}(W:Initialize G)(g:G.Simple)(c:Shade.Cut) {ι:Type}{L: Filter ι}{a:ι→ℝ}{x y z:ι→Cover}{u v:E4}
variable (s:Relief.Stage L a)(hu:distance L a (fun i=> x i-z i) u) (hv:distance L a (fun i=> y i-z i) v)(hUV:u ≠ v)
lemma peek_m (P:Stamp G)(x:Cover): peek G (Trace.volume x P)=peek G P:=by unfold peek Mu.scalar; rw [ting,map_zero]
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 700000 in
lemma transport (p:Stamp G)(x:Cover)(a:Line G): Ξ (displace x a) (Trace.volume x p)=Trace.volume x (Ξ a p):=by
  have he (p:Stamp G)(a:Line G): Ξ a p=tie G (harp a) p-harp a*p:=by apply eq_sub_of_add_eq; rw [add_comm]; simpa only [mul_one,one_tie] using! (cross_rule 1 p a).symm
  rw [he,he,map_sub,map_mul,rings, ← Mu.bring,rings]
lemma trails (x:Cover)(r p:Line G)(P:Stamp G): slower (displace x r) (displace x p) (Trace.volume x P) = slower r p P:=by
  simp_rw [slows,transport,peek_m,col,meter_serves]
lemma jpeg (x y z:Cover)(p:Stamp G): bottom W g (z+x) (z+y) (Trace.volume z p)=bottom W g x y p:=by
  unfold bottom; simp only [LinearMap.sum_apply,LinearMap.smul_apply]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> congr_arg ((4:ℂ)⁻¹ • ·) (by simp_rw [u_line,cable,← displacement z x,← displacement z y,trails])

-- normalize back into receipt quantity
abbrev uTicket (b:Name G): Fee G := ⟨1,wickLine g (W.surveys 4) false b,carriesL g (W.surveys _) false b⟩ -- needs args
abbrev cameU (a:ℝ)(v:Cover)(b:Name G):= a⁻¹^2 • u_line g W v b
lemma carriesMark (a:ι→ℝ)(v:ι→Cover)(b:Name G)(i): cameU W g (a i) (v i) b= Calling v a (uTicket W g b) i := rfl
lemma ξ_scale (v:ℝ)(a:Line G)(x:Stamp G): Ξ (v • a) x=(v:ℂ) • Ξ a x:=by
  change slit (numbers (bake _)) _= _; rw [map_smul, show numbers (v • bake a)=(v:ℂ) • numbers (bake a) from funext fun i=>by simp [numbers]]; exact slit_smul .. -- order
lemma ν_scale (a:Line G)(b:Line G)(v:ℝ): col (v • a) (v • b) = (v:ℂ)^2 * col a b:= by unfold col handshake; simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
lemma soft (p q:Line G)(v:ℝ): slower (v • p) (v • q)=(v:ℂ)^4 • slower p q:=by apply LinearMap.ext; intro x; rw [LinearMap.smul_apply,smul_eq_mul, slows,ν_scale, ξ_scale,ξ_scale,map_smul,map_smul, slows]; simp only [map_smul,smul_eq_mul]; ring

-- conditional uniformly charged turn at use-point relative geometry
variable {P:ι→ Stamp G}
def SimplePay (P:ι→ Stamp G) (z x y:ι→Cover)(L:Filter ι)(a:ι→ℝ): Prop:= Likely L (fun i=> peek G (P i)) ∧ ∀ i j :Name G, Likely L fun l => peek G (Ξ (cameU W g (a l) (x l-z l) i) (Ξ (cameU W g (a l) (y l-z l) j) (P l)))
include hUV s hu hv in
theorem lowest (h:SimplePay W g P z x y L a): Tendsto (fun i=> (a i:ℂ)⁻¹^8 *bottom W g (x i) (y i) (Trace.volume (z i) (P i))) L (𝓝 0):=by
  have he : distance L a (fun i=> x i-z i-(y i-z i)) (u-v):= fence L u v hu hv; let A i:= x i-z i; let B i:= y i-z i; let C i:ℂ:=(a i:ℂ)⁻¹; let F j i := cameU W g (a i) (A i) j; let H j i:= cameU W g (a i) (B i) j; let f (t u : Name G)(i):= (4:ℂ)⁻¹ * slower (F t i) (H u i) (P i); let M:=W.surveys 4
  have ht(t p):Tendsto (fun i=> col (F t i) (H p i)) L (𝓝 0):=by
    unfold F H cameU; simp_rw [ν_scale]; let v i:= handshake (u_line g W (A i) t) (u_line g W (B i) p)
    have hp:funds L a 5 v:= duty g M s he (sub_ne_zero.mpr hUV) M false t p (by decide) (by decide); have ht:= (Complex.continuous_ofReal.tendsto 0).comp (pays0 s 4 hp); rw [Complex.ofReal_zero] at ht; apply ht.congr; intro i; change (↑((a i)⁻¹^4*v i):ℂ)= (↑((a i)⁻¹^2):ℂ)^2* ↑(v i); push_cast; ring
  have hh (b e):Tendsto (f b e) L (𝓝 0):=by
    obtain ⟨D,hD⟩:= h.1; obtain ⟨B,hB⟩:= h.2 b e; have he : Tendsto (fun i=> peek G (Ξ (F b i) (Ξ (H e i) (P i)))) L (𝓝 B):=hB
    unfold f; simp_rw [slows]; have hi:=(((ht b e).const_mul 4|>.mul he).add (((ht b e).pow 2|>.const_mul 2)|>.mul hD))|>.const_mul ((4:ℂ)⁻¹); simpa using hi
  have hi:= tendsto_finsetSum (f:=fun i l=>∑ u,f i u l) Finset.univ fun i _=>tendsto_finsetSum Finset.univ (fun k _=> hh i k); simp only [Finset.sum_const_zero] at hi; apply hi.congr; intro i; rw [← show bottom W g (z i + A i) (z i+B i) =bottom W g (x i) (y i) from (by unfold A B; rw [add_comm (z i),sub_add_cancel,add_comm (z i),sub_add_cancel]
    ), jpeg]; unfold bottom; simp_rw [LinearMap.sum_apply, LinearMap.smul_apply,Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; unfold f F H cameU; rw [soft,LinearMap.smul_apply]; simp only [smul_eq_mul]; push_cast; ring
end YM.XSpace.Relief
