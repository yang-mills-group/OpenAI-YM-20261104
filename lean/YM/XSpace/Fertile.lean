import YM.XSpace.Furniture
/-!
# Oriented reannouncement & presence of the first RG-adjustment counterterm

Field frame (prior to removal) may grow polynomially in spacing inverse. Invariant
and strictly unit; works for compacts with clearance priced by detailed Cut.
No insertion of an optional β-scale derivative, still using raw formal parameter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Structure1
open Filter Set Function Asymptotics Lattice Chart2 Mu Furlough Normalize Foundation JetGauge Outline Shade Future Hoops Stall Playpen Further.FreeCovariance.KP
open scoped Topology BigOperators Classical
variable {ι: Type} {G:Gauge} (W:Initialize G)(c:Shade.Cut) {n j:ℕ} (d:ℕ)
-- bind field
variable {a:ι→ℝ} {L:Filter ι}[L.IsCountablyGenerated] (S:Tendsto a L (𝓝 0))(he:∀ᶠ i in L,0<a i)
def harvest (a:ℝ): Change G d :=⟨_, compass _ (ready_in W c a d)⟩
variable (x:ι→Fin n→Cover) (w : Fin n→ E4) (t:Tags G d n) (H:Poses L a (fun j i=>x i j) w Finset.univ)(hc: Cleared c w Finset.univ)
include he S H hc in
lemma established : Likely L (fun i=> adequate W (ready W c (a i) d) (a i) (x i) t):=by
  simp_rw [calls (adequate _ _ _ _) t]; apply Likely.sum; intro b _; let o(j : Fin n):= Normalize.part d (b j) (t j)
  exact (compensation W o Finset.univ c S he H hc).congr (he.mono fun i hi=> (confidence W c (d:=d) (x i) (a i) hi o (fun j=> Nat.lt_add_one_iff.mp (b j).isLt)).symm)
private lemma ratioUp (t:ℝ)(s:Signed)(p:Cover): actual t (s.act p)= s.ortho.motion (actual t p):=by
  unfold actual; rw [map_smul]; congr 1; ext1 j; change _= Ortho.move s.ortho _ _; rw [Signed.ortho_move]; obtain ⟨j,rfl⟩:=s.perm.surjective j; unfold rcast; simp only [WithLp.ofLp_toLp,Signed.act_at]; split_ifs <;> push_cast <;> rfl
include he S H hc in
theorem sprout : Likely L fun i=> adequate W (harvest W c d (a i)).val (a i) (x i) t:=by
  change Likely L fun i=> adequate W (forge (ready W c (a i) d)) (a i) (x i) t; simp_rw [forges]; apply Likely.mul (Likely.const L _) (Likely.sum _ _ _); intro s _; simp_rw [spun]; let y := s.ortho.motion ∘ w; let z (i:ι) (k:Fin n) := s.act (x i k); have hh : Poses L a (fun j i=>z i j) y Finset.univ:=by
    refine ⟨?_,fun j hj k hk h=> H.ends hj hk (Ortho.move_injective _ h)⟩ -- arg order?
    intro j hj; simp_rw [z,ratioUp]; exact s.ortho.motion.continuous.continuousAt.tendsto.comp (H.payment j hj)
  have ht:Cleared c y Finset.univ:= by intro i hi j hj hx; unfold y; simp only [Function.comp_apply, ← map_sub]; rw [LinearIsometryEquiv.norm_map]; exact hc i hi j hj hx
  simp_rw [sun]; exact Likely.mul (Likely.const L _) (Likely.add (established W c d S he z y _ hh ht) ((established W c d S he z y _ hh ht).cont continuous_star))

variable {t x w}
-- coupon making this a known position frame BEFORE trimming. Strong enough for every period notice.
abbrev Fees (T:ι→FieldEnd G d) := ∀ p:Sec G d, By ℂ L (fun i=> (a i:ℂ)^(d+1) • T i p) 0
include S he
set_option maxHeartbeats 900000 in
lemma start_cost : Fees (a:=a) (L:=L) d (fun i=> ready W c (a i) d):=by
  let u(k:Fin (d+1)):= fun (X:Sec G k.val)=> up (Nat.lt_add_one_iff.mp k.isLt) X
  intro p f; simp_rw [ready,LinearMap.sum_apply,LinearMap.comp_apply,Finset.smul_sum,map_sum,map_zero]; rw [← Finset.sum_const_zero (s:=(Finset.univ:Finset (jobs d))) (M:=ℂ)]
  refine tendsto_finsetSum Finset.univ fun k _=>?_ ; let p':=Normalize.part d k p; let F:Sec G k.val→ₗ[ℂ] ℂ:= f ∘ₗ (up (Nat.lt_add_one_iff.mp k.isLt)); let g (i:ι):=repair W c k (a i) p'
  change Tendsto (fun i=> f ((a i:ℂ)^(d+1) • u k (classFee W c (a i) _ p'))) L (𝓝 0)
  let Z i(re:jobs k.val):=(a i:ℂ)^(d-k.val)*(a i:ℂ)^re.val; let o(j:jobs k.val): Module.Dual ℂ (Sec G k.val):= F ∘ₗ en (Nat.lt_add_one_iff.mp j.isLt) ∘ₗ Normalize.part _ _; let ψ(j:jobs k.val)(i):= Z i j * o j ((a i:ℂ) • g i)
  have ht(j):Tendsto (ψ j) L (𝓝 0):=by
    have hA:Tendsto (fun i=>(a i:ℂ)) L (𝓝 0):=by simpa only [comp_def, Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto (0:ℝ)).comp S
    have hh:Tendsto (fun i=>o j ((a i:ℂ) • g i)) L (𝓝 (o j 0)):=greeting W c S he p' (o j); rw [map_zero] at hh
    have hh:= ((hA.pow (d-k.val)).mul (hA.pow j.val)).mul hh; rw [mul_zero] at hh; exact hh
  have hx:=tendsto_finsetSum (f:=ψ) Finset.univ (fun i _=> ht i); simp only [Finset.sum_const_zero] at hx; apply hx.congr'; filter_upwards [he] with i hi
  have hz:(a i:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hi.ne'; change ∑ j,ψ j i=_; simp only [classFee,u,LinearMap.comp_apply,LinearMap.smul_apply,gates,LinearMap.sum_apply,map_sum, Finset.smul_sum,map_smul]; refine Finset.sum_congr rfl fun y _=>?_ ; change Z i y * o y ((a i:ℂ) • g i)= _ • (_ • ((a i:ℂ)^y.val • (o y (g i)))); rw [map_smul]; simp only [smul_eq_mul, Z]; obtain ⟨r,hr⟩:= Nat.exists_eq_add_of_le (Nat.lt_add_one_iff.mp k.isLt); -- order
  let b:ℂ:=a i; rw [base,show (a i:ℂ)^(d+1)= (a i:ℂ)^k.val*(a i:ℂ)^(d-k.val)*(a i:ℂ) from by rw [← pow_add,show k.val+(d-k.val)=d from by omega,pow_add,pow_one]]; rw [inv_pow]; field_simp

omit S he [L.IsCountablyGenerated] in
private lemma stay {T:ι→FieldEnd G d}(h:Fees (a:=a) (L:=L) d T): Fees (a:=a) (L:=L) d (fun i=> mid (T i)):=by
  intro p g; let A(i:ι):ℂ:= (a i:ℂ)^(d+1)
  let f : Module.Dual ℂ (Sec G d) :=
    { toFun:=fun p=> star (g (reel d p))
      map_add' x y:=by simp only [map_add,star_add]
      map_smul' c x:=by rw [(reel d).map_smulₛₗ,map_smul,RingHom.id_apply,star_smul,show star ((starRingEnd ℂ) c)=_ from star_star c] }
  have he:= (h p g).add ((h (reel d p) f).star); rw [map_zero,map_zero,star_zero,add_zero] at he; have hp:=he.const_mul ((2:ℂ)⁻¹); rw [mul_zero] at hp; rw [map_zero]; apply hp.congr; intro i; change _ * (g (A i • _) + star (star (g (reel d (A i • _)))))=_
  rw [star_star,(reel d).map_smulₛₗ]; simp only [mid,LinearMap.smul_apply,LinearMap.add_apply,rsa,A,map_pow, Complex.conj_ofReal,map_add,map_smul,smul_eq_mul,mul_add]; ring

set_option maxRecDepth 4600 in
theorem cost : Fees (a:=a) (L:=L) d (fun i=> (harvest W c d (a i)).val):=by
  intro p g; let T i:= ready W c (a i) d; change Tendsto (fun i=> g ((a i:ℂ)^(d+1) • forge (T i) p)) L _
  let f (s:Signed) i:= g ( (a i:ℂ)^(d+1) • spiral s d (mid (T i)) p); have ht(s):Tendsto (f s) L (𝓝 0):=by
    have he:= stay d (T:=T) (start_cost W c d S he) (τ s d p) (g ∘ₗ τ s⁻¹ d); rw [map_zero] at he; apply he.congr; intro i; rw [LinearMap.comp_apply, map_smul (τ s⁻¹ d)]; rfl
  have he:= (tendsto_finsetSum Finset.univ fun x _=>ht x).const_mul ((R Signed)⁻¹); simp only [Finset.sum_const_zero,mul_zero] at he; rw [map_zero]; apply he.congr; intro i; rw [axes,LinearMap.smul_apply,smul_comm,LinearMap.sum_apply, Finset.smul_sum,map_smul,map_sum]; rfl
end YM.XSpace.Structure1
