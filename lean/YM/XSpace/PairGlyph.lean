import YM.XSpace.Fibers
import YM.XSpace.Clan
/-! # Six-point (weight six) label knows the bracket

Although the same color actor has only been inferred orthogonal,
its action on an alternating invariant tensor with three undifferentiated
legs can already be tested in this horizon. Use a real fixed element,
independent of the samples. Label-space orbit then discrete.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Stab
open Function Set Filter MeasureTheory Next.Rank Normal Maxwell Maxwell.Free ProbeLine MvPolynomial OJoint InnerProductSpace
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace ContDiff Classical Polynomial
variable {G:Gauge}

def paintCh (s:Knight G)(A:TaylorTower G):TaylorTower G:= fun i=> faceMap _ (LinearMap.toContinuousLinearMap (Spin s)) (A i)

lemma stationed (s:Knight G)(A:TaylorTower G) {n:ℕ}(p:Flavor n): Maxwell.Free.available ((paintCh s A) n) p=Spin s (Maxwell.Free.available (A n) p):= by
  let F:= A n
  ext1 i
  have ht: faceMap n (cp (G:=G) i) (faceMap n (LinearMap.toContinuousLinearMap (Spin s)) F)=∑ j:G.ColorIndex, s.val i j • faceMap n (cp (G:=G) j) F := by
    apply Subtype.ext; funext a b; ext1 x
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,Finset.sum_apply,Pi.smul_apply,sum_apply,_root_.smul_apply,face_eval]; exact spin_act s (F.val a b x) i
  change p _=_
  rw [show faceMap n (cp (G:=G) i) (paintCh s A n)=_ from ht,map_sum,spin_act]; exact Finset.sum_congr rfl fun j _=>map_smul p _ _

lemma sends (A:TaylorTower G)(s: Knight G)(n:ℕ): chord (paintCh s A) n=swept s (chord A n):= by
  apply PiLp.ext; intro i
  exact congr_arg (fun x:G.Color=> x i.2) (stationed s A (pieces i.1.1 i.1.2))
lemma pledge (n:ℕ)(p:HFields G n)(A:TaylorTower G)(s:Knight G): Maxwell.probe (paintCh s A) p.val= watches (changing s (records G n p)) (chord A n):= by
  rw [← opensR,appears_read,sends,changing_value]
lemma accepts {n:ℕ}(p:HFields G n)(s:G.El): changing (intoClan G s) (records G n p)=records G n p:= by
  apply grid_full; intro y; obtain ⟨A,rfl⟩:= chord_full y
  rw [← pledge,← appears_read,opensR]; rw [show paintCh (intoClan G s) A=Maxwell.Free.shade s A from ?_, ← pigment_action, (sector.mp p.property).2 s]
  funext i; apply Subtype.ext; funext v w; ext1 z
  exact enters s _

-- rank-three color trilinear

def CH (G:Gauge)(x y z:G.Color):= inner ℝ (G.ad x y) z
lemma previous (x y z:G.Color): CH G x z y= -CH G x y z:= by unfold CH; rw [Gauge.ad_skew, real_inner_comm z _]
def Phi (G:Gauge) : Triple G := G.ad.compr₂ (innerₗ G.Color)
lemma rig : ∀ x y z, Phi G x y z=CH G x y z:= fun _ _ _=>rfl

local notation "U" => Maxwell.Free.available

-- grade-0 flavor layout; only 01,02,03 for f-components
abbrev δ_color (G:Gauge)(i:G.ColorIndex):= unitColor G i

def flags (G:Gauge)(a b c:Flavor 0): WickPol G:=∑ i:G.ColorIndex,∑ j:G.ColorIndex,∑ k:G.ColorIndex,
    C (↑(CH G (δ_color G i) (δ_color G j) (δ_color G k)):ℂ)*bit a i*bit b j*bit c k

lemma tricolor (a b c:Flavor 0)(A:TaylorTower G) : probe A (flags G a b c)= (↑(CH G (U (A 0) a) (U (A 0) b) (U (A 0) c)):ℂ):= by
  let P:=Phi G; let X:=A 0
  have he (p:Flavor 0): U X p=∑ i:G.ColorIndex, flavor 0 i p X • unitColor G i := (color_sum (U X p)).symm
  unfold flags; change _= (↑(P _ _ _):ℂ); rw [he a, he b, he c];
  simp_rw [map_sum, LinearMap.sum_apply, map_mul, Complex.ofReal_sum]
  have hc(c:ℂ): probe A (C c)=c:= by simp [probe]
  simp only [map_smul,LinearMap.smul_apply,bit,symbol_test,hc,smul_eq_mul,Complex.ofReal_mul];
  conv_lhs=>
    rw [Finset.sum_comm]; rhs; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=> ?_; refine Finset.sum_congr rfl fun j _=> ?_; refine Finset.sum_congr rfl fun k _=> ?_
  unfold X; rw [show ∀ i j k,P i j k=CH G i j k from rig]; unfold δ_color; ring

lemma admits {d:ℕ}(hd:6≤d)(a b c:Flavor 0): flags G a b c∈shellSector G d:= by
  refine sector.mpr ⟨?_,fun u=> ?_⟩
  · unfold flags
    refine Submodule.sum_mem _ fun i _=>Submodule.sum_mem _ fun j _=> Submodule.sum_mem _ fun k _=>?_ ; rw [lowerCap,MvPolynomial.mem_restrictSupport_iff]
    intro p h
    have hp(w:Flavor 0)(i:G.ColorIndex): IsWeightedHomogeneous scaleW (bit w i) 2:= symbol_hom (flavor _ i w) (fun i=>i+2)
    have he := ((((hp a i).C_mul _).mul (hp b j)).mul (hp c k)) (mem_support_iff.mp h)
    exact le_trans (show _ ≤ 6 from he.le) hd
  apply Maxwell.equalPol; intro A; rw [pigment_action,tricolor,tricolor];
  simp only [Maxwell.Free.shade, shows_hue,CH,← adjoint_ad, identity_adj]

lemma landmarks (x y z : G.Color): ∃ P:Shell G 0,U P (cell 0 1)=x ∧ U P (cell 0 2)=y ∧ U P (cell 0 3)=z := by
  let v:=blade 0 1 x+blade 0 2 y+blade 0 3 z
  have ht i j t a c (x:G.Color): flavor (G:=G) 0 c (cell i j) (blade t a x)=wedge 1 i j t a*x c:= congr_arg (fun x:G.Color=> x c) (blade_eval ..)
  refine ⟨v,?_⟩; refine ⟨PiLp.ext fun i=>?_, PiLp.ext fun i=>?_, PiLp.ext fun i=>?_⟩ <;> (simp only [Maxwell.Free.available,v, WithLp.ofLp_toLp,map_add, ht, wedge,Matrix.one_apply] <;> simp +decide)
lemma spin_via (T: Knight G)(z:G.Color): Spin T (Spin T⁻¹ z)=z:= by rw [← spin_mul,mul_inv_cancel,spin_one]
lemma sign_select (H:G.Simple)(T:Knight G)(c:ℝ)(h:∀ x y z,CH G (Spin T x) (Spin T y) (Spin T z)=c*CH G x y z): c=1∨c= -1:= by
  have hf x y: G.ad (Spin T x) (Spin T y)=c • Spin T (G.ad x y):= by
    apply ext_inner_right ℝ; intro z; rw [← spin_via T z,real_inner_smul_left, OJoint.spin_inner]; exact h x y _
  obtain ⟨x,y,hp⟩:= H.nonabelian; have hx:x≠0:=by rintro rfl; simpa using hp
  let Q:= G.ad x; let P:=Spin T; let S:= Spin T⁻¹
  let t:=G.ad (Spin T x)
  have hP : S*P=1:= by ext1 v; change Spin T⁻¹ (Spin T v)= _; rw [← spin_mul,inv_mul_cancel,spin_one]; rfl
  have hU : P*S=1:= LinearMap.ext fun v=>spin_via T v
  have hu:P*Q* S= P*Q* S:=rfl
  have ht : t=c • (P*Q*S):= by
    apply LinearMap.ext; intro v; rw [LinearMap.smul_apply]; change G.ad (Spin T x) v=c • Spin T (Q _); nth_rw 1 [← spin_via T v]; rw [hf]
  have hQ:t*t=c^2 • (P*(Q*Q)*S):= by
    rw [ht,smul_mul_assoc, mul_smul_comm,smul_smul,sq]; congr 1; calc
     _= P*(Q*(S*P)*Q)*S:= by simp only [mul_assoc]
     _= _:= by rw [hP];simp
  have hg:= Gauge.trace_adjoint H (Spin T x) (Spin T x); rw [spin_inner] at hg; change -LinearMap.trace _ _ (t*t)=_ at hg
  rw [hQ,map_smul, LinearMap.trace_mul_comm ℝ,← mul_assoc,hP,one_mul,smul_eq_mul, ← mul_neg] at hg -- inspect
  rw [show -LinearMap.trace _ _ (Q*Q)=_ from Gauge.trace_adjoint H x x] at hg
  let b:=G.casimir*inner ℝ x x
  have hb : b≠0:= mul_ne_zero (Gauge.casimir_pos H).ne' (by rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
  exact sq_eq_one_iff.mp (mul_right_cancel₀ hb (hg.trans (one_mul _).symm))

def conn (s:Knight G)(t:ℝ):Prop:= ∀ x y z,CH G (Spin s x) (Spin s y) (Spin s z)=t*CH G x y z
lemma reach {d:ℕ}(H:G.Simple)(hd:6≤d)(T:HFields G d→HFields G d) (s:Knight G)(h:∀ p,records G d (T p)=changing s (records G d p)) : conn s 1 ∨ conn s (-1):= by
  let x:=cell 0 1; let y:=cell 0 2; let z:=cell 0 3
  let p: HFields G d:=⟨flags G x y z, admits hd x y z⟩
  have he (J:TaylorTower G):probe J (T p).val= CH G (Spin s (U (J 0) x)) (Spin s (U (J 0) y)) (Spin s (U (J 0) z)):= by
    rw [← opensR,appears_read, h, ← pledge]; change probe _ (flags G x y z)=_; rw [tricolor,stationed,stationed,stationed]
  let F:=Spin s; let L: Triple G:= ( ( ( Phi G).compl₁₂ F F ).compr₂ (LinearMap.lcomp _ _ F) ) -- inspect L lcomp wants F after end rather than before
  have hh a b c:L a b c=CH G (F a) (F b) (F c):= rfl
  obtain ⟨c,hc⟩:= alternate H L (by intro i j k; rw [hh,hh]; unfold CH; rw [skew_ad (F i),inner_neg_left]) (fun i j k=> previous _ _ _) (by
    intro u a b c
    obtain ⟨X,h₁,h₂,h₃⟩:= landmarks a b c; let J : TaylorTower G:= fun i=> if t:i=0 then t ▸ X else 0
    have hg:J 0=X:=by simp [J]
    have ht:(T p).val∈shellSector G d:=(T p).property
    have hp := (((sector.mp ht).2 u))
    have hz := congr_arg (probe J) hp; rw [pigment_action,he,he] at hz
    simp only [Maxwell.Free.shade, shows_hue,hg,x,y,z,h₁,h₂,h₃] at hz
    exact Complex.ofReal_inj.mp hz)
  have hp:conn s c := hc
  exact (sign_select H s c hp).elim (fun hx=> Or.inl (hx ▸ hp)) (fun hx=> Or.inr (hx ▸ hp))

lemma conn_closes (G:Gauge)(v:ℝ): IsCompact {s:Knight G| conn s v}:= by
  have h (x y z:G.Color):Continuous (fun s:Knight G=> CH G (Spin s x) (Spin s y) (Spin s z)):= by
    have q (x:G.Color):Continuous fun s:Knight G=> Spin s x:= by
      exact (((LinearMap.applyₗ x: Module.End ℝ G.Color→ₗ[ℝ] G.Color).comp Matrix.toEuclideanLin.toLinearMap).continuous_of_finiteDimensional.comp continuous_subtype_val)
    have p x y : Continuous fun s:Knight G=> G.ad (Spin s x) (Spin s y):= by
      unfold Gauge.ad; simp only [LinearMap.coe_mk, AddHom.coe_mk]; refine G.projectColor.continuous_of_finiteDimensional.comp (Continuous.sub (Continuous.mul (G.colorMat.continuous_of_finiteDimensional.comp (q x)) (G.colorMat.continuous_of_finiteDimensional.comp (q y))) ((G.colorMat.continuous_of_finiteDimensional.comp (q y)).mul (G.colorMat.continuous_of_finiteDimensional.comp (q x))))
    exact (p x y).inner (q z)
  apply IsClosed.isCompact; unfold conn; simp_rw [Set.setOf_forall]; exact isClosed_iInter (fun x=> isClosed_iInter (fun y=> isClosed_iInter (fun z=> isClosed_eq (h x y z) continuous_const)))
lemma conn_away {s p:Knight G}{v:ℝ} (hs:conn s v)(hp:conn p v): Homed (p*s⁻¹) := by
  intro x y; let t:=p*s⁻¹
  have ht (x y z) : CH G (Spin t x) (Spin t y) (Spin t z)= CH G x y z := by
    let a(w:G.Color):= Spin s⁻¹ w
    have he := (hp (a x) (a y) (a z)).trans (hs (a x) (a y) (a z)).symm; unfold a at he; rw [spin_via,spin_via,spin_via] at he; unfold t; rw [spin_mul,spin_mul,spin_mul,he]
  apply ext_inner_right ℝ; intro z
  rw [← spin_via t z,spin_inner]; exact (ht ..).symm
lemma conn_orbit (H:G.Simple) (t:ℝ){n:ℕ}(p:HFields G n): Set.Finite ((fun v : Knight G=> changing v (records G n p)) '' {v:Knight G| conn v t}):= by
  let K:= {v:Knight G|conn v t}
  let F (x:Knight G) := changing x (records G n p)
  have hp (x:↥K): ∀ᶠ y : Knight G in 𝓝 x.val, y∈K → F y=F x := by
    have ht : Tendsto (fun y:Knight G=> y*x.val⁻¹) (𝓝 x.val) (𝓝 1):= by simpa using (continuous_mul_const x.val⁻¹).tendsto x.val
    filter_upwards [ht.eventually (around H)] with y hy
    intro h
    obtain ⟨B,hB⟩:= hy (conn_away x.property h)
    have hh : y = intoClan G B*x.val:= by rw [hB]; group
    apply grid_full; intro Q; unfold F; rw [hh,changing_value,changing_value,rotor_mul,← changing_value,accepts p B]
  choose E hu hv ht using fun x:↥K=> eventually_nhds_iff.mp (hp x)
  obtain ⟨P,hP⟩:= (conn_closes G t).elim_finite_subcover E hv (by intro x hx; exact Set.mem_iUnion.mpr ⟨(⟨x,hx⟩:↥K),ht ⟨x,hx⟩⟩)
  refine ((Finset.finite_toSet P).image (fun x:↥K=> F x)).subset ?_
  rintro _ ⟨x,hx,rfl⟩; obtain ⟨y,hy⟩:= Set.mem_iUnion.mp (hP hx); obtain ⟨hS,hX⟩:= Set.mem_iUnion.mp hy; exact ⟨y,hS,(hu y x hX hx).symm⟩

lemma lowty (H:G.Simple){k:ℕ} (hk:k≤5)(p:HFields G k)(v:Knight G): changing v (records G k p)=records G k p:= by
  apply grid_full; intro x; obtain ⟨A,ha⟩:=chord_full x; rw [←ha, ← pledge, ← appears_read,opensR]
  let P:= paintCh v A
  let V:= LinearMap.ker ((probe P).toLinearMap-(probe A).toLinearMap)
  suffices p.val∈ V from sub_eq_zero.mp this
  have hg (i j:ℕ):Teams G i j ≤ V:= by
    unfold Teams; apply Submodule.span_le.mpr; rintro x ⟨y,z,rfl⟩
    change probe P (team G y z)-probe A (team G y z)=0; rw [basicTeam,basicTeam]; unfold P; rw [stationed,stationed, spin_inner,sub_self]
  apply show shellSector G 5≤ V from ?_
  · exact Maxwell.Free.chain hk p.property
  rw [five_support H,low_support H]; refine sup_le (sup_le (Submodule.span_le.mpr ?_) (hg _ _)) (hg _ _)
  rintro x h; obtain rfl : x=(1:WickPol G):= h; change probe _ _ - probe _ _=0; rw [map_one,map_one,sub_self]

-- hence possible outputs belong to finite sets (locally constant ambiguity)
theorem stabilizing {d:ℕ}(H:G.Simple)(h:4≤d)(c:G.ColorIndex)(p:HFields G d): ∃ R:Set (Chamber G d), R.Finite∧∀ (T:HFields G d→ HFields G d), Deliver h T→ records G d (T p)∈R:= by
  let F:= fun v : Knight G=>changing v (records G d p)
  by_cases hd:6≤d
  · refine ⟨(F '' _)∪(F '' _), (conn_orbit H 1 p).union (conn_orbit H (-1) p),fun T Hg=>?_⟩
    obtain ⟨A,hA⟩:= Hg.actor c
    rw [hA]; rcases reach H hd T A hA with he|he
    · left; exact ⟨A,he,rfl⟩
    right; exact ⟨A,he,rfl⟩
  refine ⟨{records G d p}, Set.finite_singleton _, fun T H'=>?_⟩
  obtain ⟨A,hA⟩:= H'.actor c
  rw [hA, lowty H (by omega)]; exact Set.mem_singleton _
end YM.XSpace.Stab
