import YM.Push.LOOP_COEFFICIENT.Tangent
import YM.LocalH.Chart

/-!
# Lie gauge vector fields in the exponential chart

Works for possibly disconnected group. Need chart near identity for Taylor
calculus, not imposing convergence assumptions on that chart. Accelerations
used in checking commutators. We will certify Divergence separately. Color from
existing gauge. Landau shift & signed-coordinate equivariance wanted on entire
Stencil, thus prove joint identities near identity, not just linear terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSBar.Nexus
open Set Function Filter Gauge NormedSpace MeasureTheory Precision Lattice LocalH Push.Loops
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius InnerProductSpace ENNReal
variable {G : Gauge}

abbrev faces (G : Gauge) := G.Color× G.Color
abbrev R (u : G.Color):= G.mat (G.lieExp u)
def str (p : faces G) : G.Mat →ₗ[ℝ] G.Mat where
    toFun X:= X* G.colorMat p.2 - G.colorMat p.1 * X
    map_add' _ _:=by rw [add_mul,mul_add]; abel
    map_smul' _ _:=by rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]; rfl

def arch (x : G.Color) : faces G →ₗ[ℝ] G.Color where
   toFun p:= fderiv ℝ G.plog (R x) (str p (R x))
   map_add' v w:=by rw [show str (v+w) (R x)=str v (R x)+str w (R x) from ?_,map_add]; unfold str; simp only [Prod.snd_add, Prod.fst_add, LinearMap.coe_mk, AddHom.coe_mk,map_add,mul_add,add_mul]; abel
   map_smul' r v:=by rw [show str (r • v) (R x)=r • str v (R x) from ?_,map_smul]; rfl -- see
                     change R x * G.colorMat (r • v.2)-G.colorMat (r • v.1)* R x=r • str v (R x); rw [map_smul,map_smul, mul_smul_comm,smul_mul_assoc,← smul_sub]; rfl
lemma archs (x : G.Color)(p:faces G): arch x p=fderiv ℝ G.plog (R x) (str p (R x)):=rfl

-- actual patch
abbrev Quill {G:Gauge} (x:G.Color):Prop:= ∃ U s, Geom G U s ∧ x∈s
lemma quill (G:Gauge):∀ᶠ x:G.Color in 𝓝 0, Quill x:=by
  obtain ⟨r,hr,h⟩:=geom_patch G; filter_upwards [Metric.ball_mem_nhds (0:G.Color) hr] with x hx; exact ⟨_,_,h r le_rfl,hx⟩
lemma Quill.permit {x : G.Color}(h:Quill x): G.plog (R x)=x:= by obtain ⟨U,s,h,H⟩:=h; exact h.2.2.1 H
lemma Quill.admit {x : G.Color}(h:Quill x) : ContDiffAt ℝ ω G.plog (R x):=by obtain ⟨U,s,h,H⟩:=h; exact h.2.2.2.2.2.2 _ (h.2.2.2.2.2.1 H)
lemma Quill.again {x : G.Color}(h:Quill x): ∀ᶠ y : G.Color in 𝓝 x,Quill y:= by
  obtain ⟨U,s,h,H⟩:=h; filter_upwards [h.2.1.mem_nhds H] with v hv; exact ⟨U,s,h,hv⟩
lemma Quill.smooth {x : G.Color}(h:Quill x) (p : faces G): ContDiffAt ℝ ω (fun y=> arch y p) x:= by
  simp_rw [archs]; exact ((h.admit.fderiv_right (m:=ω) (by simp)).comp (f:=R) x G.exp_jet.contDiffAt).clm_apply
    ((str p).toContinuousLinearMap.contDiff.contDiffAt.comp (f:=R) x G.exp_jet.contDiffAt)
lemma push_smooth (p:faces G): ContDiffAt ℝ ω (fun x:G.Color=> arch x p) 0:= Quill.smooth ((quill G).self_of_nhds) p
lemma Quill.release {x : G.Color}(h:Quill x)(y:G.Color): fderiv ℝ G.plog (R x) (fderiv ℝ R x y)= y:= by
  have he : (G.plog ∘ R)=ᶠ[𝓝 x] id:= h.again.mono fun _=> Quill.permit
  have hx:=DFunLike.congr_fun ((fderiv_comp (𝕜:=ℝ) (g:=G.plog) (f:=R) x (h.admit.differentiableAt (by simp)) (G.exp_jet.differentiable (by simp) _)).symm.trans he.fderiv_eq) y
  rw [fderiv_id] at hx; exact hx

-- variation path. convention exponent scaled before canonical changes.
def warp (t:ℝ)(p:faces G)(x:G.El): G.El:= G.lieExp (t • -p.1)* x * G.lieExp (t • p.2)
@[simp] lemma warp_zero (p:faces G)(x:G.El): warp 0 p x=x:=by simp [warp]
lemma roll (x:G.Color):HasDerivAt (fun t:ℝ=> R (t • x)) (G.colorMat x) 0:= by
  have hx : HasDerivAt (fun t:ℝ=> t • x) x (0:ℝ):= by simpa using! ((hasDerivAt_id' (0:ℝ)).smul_const x)
  have he:= G.expDiff_zero; rw [← show (0:ℝ) • x=(0:G.Color) from zero_smul ..] at he; exact he.comp_hasDerivAt 0 hx
lemma roll_path (x:G.El)(p:faces G): HasDerivAt (fun t=> G.mat (warp t p x)) (str p (G.mat x)) 0:= by
  simp_rw [warp,G.mat_mul]; convert! (((roll (-p.1)).mul_const (G.mat x)).mul (roll p.2)) using 1; simp only [map_neg,R,zero_smul, G.mat_lieExp_zero,G.mat_one, one_mul, mul_one,neg_mul]; unfold str; dsimp; abel -- fix unfolding
lemma delta_p (p : faces G){x : G.Color}(h:Quill x): HasDerivAt (fun t : ℝ=> snap G (warp t p (G.lieExp x))) (arch x p) 0:= by
  rw [archs]; have ht:= (h.admit.differentiableAt (by simp)).hasFDerivAt; rw [R,← warp_zero p (G.lieExp x)] at ht
  exact (show HasDerivAt _ _ _ from (ht.comp_hasDerivAt 0 (roll_path (G.lieExp x) p))).congr_deriv (by rw [warp_zero]; rfl) -- see
lemma Quill.bless {x : G.Color}(h:Quill x)(p : faces G): fderiv ℝ R x (arch x p)= str p (R x):= by
  let u:=G.lieExp x; let v t:= warp t p u
  have he:= (G.exp_jet.differentiable (by simp) x).hasFDerivAt; have hv : snap G (v 0)=x:=by rw [show v 0=u from warp_zero ..]; exact h.permit
  suffices (fun t=> G.mat (v t))=ᶠ[𝓝 0] R ∘ (snap G ∘ v) by
    have hh: HasFDerivAt R (fderiv ℝ R x) (snap G (v 0)):= by rw [hv]; exact he
    have ht := (hh.comp_hasDerivAt 0 (show HasDerivAt (snap G∘v) (arch x p) 0 from delta_p p h)).congr_of_eventuallyEq this -- ∘ token use unicode hazards
    exact ht.unique (roll_path u p)
  obtain ⟨U,s,h,H⟩:=h
  have ht : Continuous v:= by unfold v warp; fun_prop
  filter_upwards [ht.continuousAt (x:=0) (h.1.mem_nhds (show v 0∈U by rw [show v 0=u from warp_zero p u]; exact h.2.2.2.2.2.1 H))] with t hh; exact congr_arg G.mat (h.2.2.2.1 hh).symm
lemma arch_zero (p : faces G): arch (0:G.Color) p=p.2-p.1:=by
  have he:= Quill.bless ((quill G).self_of_nhds) p; rw [show fderiv ℝ R (0:G.Color)= G.colorMat.toContinuousLinearMap from G.expDiff_zero.fderiv] at he; apply G.colorMat_injective; rw [show G.colorMat (arch _ p)=_ from he,map_sub]; change _* G.colorMat p.2- G.colorMat p.1*_= _; simp [R]

lemma arch_com {x:G.Color} (h:Quill x)(p q:faces G):
    fderiv ℝ (fun x=> arch x q) x (arch x p)- fderiv ℝ (fun x=> arch x p) x (arch x q) = arch x (G.ad p.1 q.1, G.ad p.2 q.2):=by
  let W : faces G := (G.ad p.1 q.1, G.ad p.2 q.2)
  have he: (str q (str p (R x))-str p (str q (R x)))=str W (R x):=by simp only [str,W,LinearMap.coe_mk, AddHom.coe_mk,G.colorMat_ad]; noncomm_ring
  have hh p q : (fderiv ℝ (fderiv ℝ R) x (arch x p)) (arch x q) + fderiv ℝ R x (fderiv ℝ (fun x=> arch x q) x (arch x p)) = str q (str p (R x)):= by
    have ht : (fun y:G.Color=> fderiv ℝ R y (arch y q))=ᶠ[𝓝 x] fun y=> str q (R y):= h.again.mono fun _ H=> H.bless q
    have hr:= ((G.exp_jet.contDiffAt.fderiv_right (m:=ω) (by simp)).differentiableAt (x:=x) (by simp)).hasFDerivAt
    have hu:= (G.exp_jet.differentiable (by simp) x).hasFDerivAt
    have hv:=((str q).toContinuousLinearMap.hasFDerivAt.comp x hu).congr_of_eventuallyEq ht
    have hy:= hr.clm_apply ((h.smooth q).differentiableAt (by simp)).hasFDerivAt
    have he:= DFunLike.congr_fun (hy.unique hv) (arch x p)
    change fderiv ℝ R x (fderiv ℝ (fun x=> arch x q) x _)+fderiv ℝ (fderiv ℝ R) x (arch x p) (arch x q)=(str q) (fderiv ℝ R x _) at he
    rw [h.bless p, add_comm] at he; exact he
  calc
    _ = fderiv ℝ G.plog (R x) (fderiv ℝ R x _) := (h.release _).symm
    _ = _ := ?_
  rw [map_sub (fderiv ℝ R x)]; rw [archs x (G.ad p.1 q.1,_),← he]; rw [← hh p q, ← hh q p, show (fderiv ℝ (fderiv ℝ R) x (arch x p)) (arch x q)=fderiv ℝ (fderiv ℝ R) x (arch x q) (arch x p) from G.exp_jet.contDiffAt.isSymmSndFDerivAt (by simp) (arch x p) (arch x q)]; apply DFunLike.congr_arg; abel
end YM.MSBar.Nexus
