import YM.XSpace.InnerDy
/-!
# Components of bracket automorphism group. Near the identity is color conjugation.

Via nearest multipliers in the compact Ad cosets; avoids any additional manifold
on Ad or its orbit. Compact even for possibly disconnected faithful subgroups.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Maxwell.Free ProbeLine LinearMap InnerProductSpace OJoint Matrix
open scoped Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius Matrix Classical
variable {G : Gauge}

abbrev Knight (G:Gauge):= ↥(OJoint G.ColorIndex) -- import? O in Orbital not Inner
abbrev Area (G:Gauge):= Matrix G.ColorIndex G.ColorIndex ℝ

lemma spin_faith {s t : Knight G} (h : ∀ p, Spin s p=Spin t p): s=t:= by
  apply Subtype.ext; exact Matrix.toEuclideanLin.injective (LinearMap.ext h)

def adjM (G:Gauge) (u:G.El) := Matrix.of fun i j=> G.adjoint u (EuclideanSpace.basisFun _ ℝ j) i
lemma adj_ok (G:Gauge) (u:G.El): (adjM G u).transpose*adjM G u=1:= by
  let V := (EuclideanSpace.basisFun G.ColorIndex ℝ)
  ext i j; rw [Matrix.one_apply]; change (∑ k,G.adjoint u (V i) k*G.adjoint u (V j) k)= _
  rw [show (∑ k,G.adjoint u (V i) k*G.adjoint u (V j) k)=inner ℝ (G.adjoint u (V j)) (G.adjoint u (V i)) from rfl, identity_adj]; by_cases h:i=j
  · subst j; simp [V]
  rw [if_neg h]; exact V.orthonormal.2 (Ne.symm h)

def intoClan (G:Gauge)(u:G.El): Knight G:=⟨adjM G u, (Matrix.mem_orthogonalGroup_iff' _ _).mpr (adj_ok ..)⟩
lemma enters (g:G.El)(x:G.Color): Spin (intoClan G g) x=G.adjoint g x:= by
  have hv: Spin (intoClan G g)=G.adjoint g:= by apply (EuclideanSpace.basisFun G.ColorIndex ℝ).toBasis.ext; intro i; ext j; rw [spin_act]; simp [intoClan,adjM,PiLp.single_apply,mul_ite]
  rw [hv]
lemma enters_one (G:Gauge): intoClan G 1=1:= spin_faith fun x=> by rw [enters,G.adjoint_one,spin_one]
lemma entry_mul (g h:G.El): intoClan G (g*h)=intoClan G g*intoClan G h:= spin_faith fun x=> by rw [enters,spin_mul,enters,enters,G.adjoint_mul]
lemma entry_inv (g:G.El): intoClan G g⁻¹=(intoClan G g)⁻¹ := by apply eq_inv_of_mul_eq_one_right; rw [← entry_mul]; simp [enters_one] -- inspect

lemma entry_cont (G:Gauge): Continuous (intoClan G):= Continuous.subtype_mk (continuous_pi fun i=> continuous_pi fun j=> (EuclideanSpace.proj (𝕜:=ℝ) i).continuous.comp (adj_cont (EuclideanSpace.basisFun _ ℝ j))) _

def Homed (s:Knight G): Prop:= ∀ x y, Spin s (G.ad x y) = G.ad (Spin s x) (Spin s y)
lemma always (g:G.El): Homed (intoClan G g):= by intro x y; simp only [enters,adjoint_ad]
lemma Homed.glob {s t: Knight G}(h:Homed s)(ht:Homed t): Homed (s*t):= by intro x y; simp only [spin_mul]; rw [ht x y,h]
lemma Homed.rev {s:Knight G}(h:Homed s): Homed s⁻¹:= by
  intro x y; have he(v:G.Color): Spin s (Spin s⁻¹ v)=v:= by rw [← spin_mul, mul_inv_cancel, spin_one]
  apply show Injective (Spin s) from fun x y h=> by rw [← spin_one x,← spin_one y,← inv_mul_cancel s, spin_mul,spin_mul,h]
  rw [he,h,he,he]

lemma clan_tangent (N : Area G) (z: G.Color)(h: G.ad z=Matrix.toEuclideanLin N):
    HasDerivAt (fun t:ℝ=> (intoClan G (G.lieExp (t • z))).val) N 0 := by
  apply hasDerivAt_pi.mpr; intro i; apply hasDerivAt_pi.mpr; intro j
  let v:= EuclideanSpace.basisFun G.ColorIndex ℝ j
  have he : G.ad z v i=N i j:= by rw [h]; change (∑ j,N i j*v j)= _; simp [v, mul_ite, PiLp.single_apply]
  rw [← he]; exact ((EuclideanSpace.proj (𝕜:=ℝ) i).hasFDerivAt.comp_hasDerivAt 0 (adj_has z v)) -- inspect

private lemma tangent0 {N:Area G} (Q:ℕ→Area G)(q:ℕ→ℝ)(a:ℕ→Knight G)(he:Tendsto q atTop (𝓝 0))(hD:Tendsto Q atTop (𝓝 N))(hx:∀ i, q i≠0)
    (hb:∀ i,Homed (a i)) (ha:∀ i x, Spin (a i) x=x+q i • Matrix.toEuclideanLin (Q i) x)(x y:G.Color):
    let K:= Matrix.toEuclideanLin N; K (G.ad x y)= G.ad (K x) y+ G.ad x (K y):= by
    intro K
    let r i:= Matrix.toEuclideanLin (Q i)
    have ht (z:G.Color): Tendsto (fun i=> r i z) atTop (𝓝 (K z)):= (((LinearMap.applyₗ z : Module.End ℝ G.Color →ₗ[ℝ] G.Color).comp Matrix.toEuclideanLin.toLinearMap).continuous_of_finiteDimensional.tendsto N).comp hD -- inspect
    let B:= toContinuousLinearMap (toContinuousLinearMap.toLinearMap ∘ₗ G.ad)
    have hs {a b:G.Color}(f g : ℕ→G.Color)(hf:Tendsto f atTop (𝓝 a))(hg:Tendsto g atTop (𝓝 b)): Tendsto (fun i=> G.ad (f i) (g i)) atTop (𝓝 (G.ad a b)):= by
      let F : G.Color×G.Color→ G.Color:= fun p=> G.ad p.1 p.2
      have ht:Continuous F:= by
        unfold F Gauge.ad; simp only [LinearMap.coe_mk, AddHom.coe_mk]; exact G.projectColor.continuous_of_finiteDimensional.comp ((Continuous.sub ((G.colorMat.continuous_of_finiteDimensional.comp continuous_fst).mul (G.colorMat.continuous_of_finiteDimensional.comp continuous_snd)) ((G.colorMat.continuous_of_finiteDimensional.comp continuous_snd).mul (G.colorMat.continuous_of_finiteDimensional.comp continuous_fst))))
      change Tendsto (F ∘ fun i=> (f i,g i)) atTop (𝓝 (F (a,b)))
      exact (ht.tendsto (a,b)).comp (hf.prodMk_nhds hg)
    have hP : Tendsto (fun i=> G.ad (r i x) y + G.ad x (r i y)+q i • G.ad (r i x) (r i y)) atTop (𝓝 (G.ad (K x) y+ G.ad x (K y)+ (0:ℝ) • G.ad (K x) (K y))):= ((hs _ _ (ht x) (tendsto_const_nhds (x:=y))).add (hs _ _ (tendsto_const_nhds (x:=x)) (ht y))).add (he.smul (hs _ _ (ht x) (ht y)))
    rw [zero_smul,add_zero] at hP
    apply tendsto_nhds_unique_of_eventuallyEq (ht _) hP
    apply Eventually.of_forall; intro i
    have hp:= hb i x y; dsimp only at hp ⊢; simp_rw [ha, _root_.map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply] at hp
    apply smul_right_injective G.Color (hx i);
    change q i • _= q i • _; simp_rw [smul_add]; unfold r; simp only [smul_add] at hp; apply add_left_cancel (a:=G.ad x y); rw [hp]; abel

section path
variable (H:G.Simple)
include H
set_option maxHeartbeats 500000 in
lemma around : ∀ᶠ s: Knight G in 𝓝 1, Homed s→ s∈Set.range (intoClan G):= by
  by_contra h
  let V:= {v:Knight G | Homed v∧ v∉Set.range (intoClan G)}
  obtain ⟨p,hp,P⟩:= mem_closure_iff_seq_limit.mp (mem_closure_iff_frequently.mpr (show ∃ᶠ s:Knight G in 𝓝 1,s∈V from ((not_eventually.mp h).mono fun i hx=> _root_.not_imp.mp hx)))
  -- minimize distance to identity.
  choose g h₁ h₂ using fun i=> isCompact_univ.exists_isMinOn (@Set.univ_nonempty G.El _)
    (f:=fun u=> ‖(p i * intoClan G u).val - (1:Area G)‖) (by apply Continuous.continuousOn; exact (((continuous_subtype_val.comp (continuous_const.mul (entry_cont G))).sub continuous_const).norm)) -- syntax
  let a(i):=p i * intoClan G (g i); let t(i):= ‖(a i).val - (1:Area G)‖
  have hb i :Homed (a i):= Homed.glob (hp i|>.1) (always (g i))
  have hh i : t i ≠0:= fun H=> (show ¬p i∈Set.range (intoClan G) from (hp i).2) ⟨(g i)⁻¹,by rw [entry_inv]; symm; exact eq_inv_of_mul_eq_one_left (Subtype.ext (sub_eq_zero.mp (norm_eq_zero.mp H)))⟩
  have hM i (g':G.El):t i ≤ ‖(a i*intoClan G g').val-(1:Area G)‖:= by unfold a; rw [mul_assoc,← entry_mul]; exact h₂ i (mem_univ _)
  have Ht:Tendsto t atTop (𝓝[≠] 0):= by
    refine tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero (fun _=> norm_nonneg _) (g:=fun i=> ‖(p i).val - (1:Area G)‖) (fun i=>?_) ?_, Eventually.of_forall hh⟩
    · simpa only [t,a,enters_one,mul_one] using (show t i ≤ ‖(p i * intoClan G (1:G.El)).val - (1:Area G)‖ from h₂ i (mem_univ (1:G.El)))
    simpa only [Function.comp_apply, show (1:Knight G).val=(1:Area G) from rfl,sub_self,norm_zero] using (((continuous_subtype_val.tendsto (1:Knight G)).comp P).sub (tendsto_const_nhds (x:=(1:Area G)))).norm
  let L(i):= (t i)⁻¹ • ((a i).val - (1:Area G))
  have hL i : ‖L i‖=1:= by unfold L; rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]; exact inv_mul_cancel₀ (hh i)
  obtain ⟨N,hN,w,hw,hD⟩:= (isCompact_sphere (0:Area G) 1).tendsto_subseq (x:=L) (fun i=> by simp [hL])
  let q(i):=t (w i); let Q := L ∘ w
  have Hq := Ht.comp hw.tendsto_atTop; have he : Tendsto q atTop (𝓝 0):= Hq.mono_right nhdsWithin_le_nhds
  have HX i : (a i).val=1+t i • L i:= by unfold L; rw [smul_smul,mul_inv_cancel₀ (hh i),one_smul,add_comm,sub_add_cancel]
  let K:= Matrix.toEuclideanLin N
  have ha i (x:G.Color):Spin (a (w i)) x=x+q i • Matrix.toEuclideanLin (Q i) x:= by
    unfold Spin; rw [HX,_root_.map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]; exact congr_arg (· + _) (spin_one x)
  have hn(x y:G.Color): K (G.ad x y)= G.ad (K x) y+ G.ad x (K y):= by
    exact tangent0 Q q (fun i=> a (w i)) he hD (fun i=> hh (w i)) (fun i=>hb (w i)) ha x y
  obtain ⟨z,hz⟩:=inside H K hn
  let b(i):= intoClan G (G.lieExp (q i • z)); let f(t:ℝ):= (intoClan G (G.lieExp (t • z))).val
  have hx:f 0=1:= by simp [f, enters_one]
  have hB : Tendsto (fun i=> (q i)⁻¹ • ((b i).val-1)) atTop (𝓝 N):= by
    have hp:= (hasDerivAt_iff_tendsto_slope.mp (show HasDerivAt f N 0 from clan_tangent _ z hz.symm)).comp Hq
    simp only [slope_def_module, Function.comp_def,hx,sub_zero] at hp; exact hp
  have ht : Tendsto b atTop (𝓝 1):= by
    have h : Continuous fun t:ℝ=>intoClan G (G.lieExp (t • z)):= (entry_cont G).comp (by fun_prop)
    have hm:= (h.tendsto 0).comp he; simp only [zero_smul,Gauge.mat_lieExp_zero, enters_one] at hm; exact hm
  let F(i):=a (w i)*(b i)⁻¹
  have hf : Tendsto (fun i=> (q i)⁻¹ • ((F i).val-(1:Area G))) atTop (𝓝 0):= by
    have hv (i): (q i)⁻¹ • ((F i).val -(1:Area G)) = ((Q i)-(q i)⁻¹ • ((b i).val-1))*((b i)⁻¹).val:= by
      change (q i)⁻¹ • _=((q i)⁻¹ • _- (q i)⁻¹ • _)*_; rw [← smul_sub,show (a (w i)).val - (1:Area G)-((b i).val-1)=(a (w i)).val-(b i).val by abel,smul_mul_assoc, sub_mul,show (b i).val*((b i)⁻¹).val=1 from Subtype.ext_iff.mp (mul_inv_cancel (b i))]; rfl
    have hz:= (hD.sub hB).mul ((continuous_subtype_val.tendsto _).comp (ht.inv)) -- inv operation
    simp_rw [hv]; simp only [sub_self,Matrix.zero_mul] at hz; exact hz
  have hz := hf.norm
  rw [norm_zero] at hz
  obtain ⟨i,hi⟩:= (hz.eventually (gt_mem_nhds (show (0:ℝ)<1 from zero_lt_one))).exists
  let g':= G.lieExp (q i • z)
  have ht := hM (w i) (g'⁻¹); rw [entry_inv] at ht; change q i ≤ ‖(F i).val - (1:Area G)‖ at ht
  change ‖(q i)⁻¹ • ((F i).val - (1:Area G))‖< 1 at hi
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hi
  exact hi.not_ge ((show 1 = (q i)⁻¹*q i from (inv_mul_cancel₀ (hh (w i))).symm).trans_le (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (norm_nonneg _))))
end path
end YM.XSpace.Stab
