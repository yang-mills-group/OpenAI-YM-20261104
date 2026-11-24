import YM.RG01.Sounder.Knot
import YM.Integration.WilsonPhysicalHistoryRetainedSpringSite
import YM.Integration.WilsonRootedHeldAffineCenter

/-! At a genuine held rough field, every signed physical orientation of a filed
    rooted curvature packet has bounded derivatives in the full angular shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldPacketGerm
open Function Lattice Wilson RG Tree Pressure Precision Gauge
open Push Push.Uniform Push.AbsoluteSums AnalyticNext.QuarticMatch.Estimate
open ConnectedActivityE6 Coat Control Blaze
open RG01.Sounder RG01.Sounder.book Logfee
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G:Gauge}{c f:Side}{S:StepData c f}{T:Tube G S}{F:Forest S.ratio}
variable {k:ℕ}{σ A:ℝ}

def bondMap (X:Coat T F)(e:Bond f):Directions G f →L[ℝ] G.Color:=
  if e∈F.trunks then 0 else if X.Hot e then
    ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Bond f=>G.Color) e else 0

private theorem bound (X:Coat T F)(e:Bond f):‖bondMap X e‖≤1:=by
  unfold bondMap
  split_ifs <;> try simp
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a=> by
    rw [one_mul]; exact norm_le_pi_norm a e

/-- No compact link is discarded: tree links, genuinely frozen links, and
    exponential increments over the nonconstant replica retain their original values. -/
theorem link (X:Coat T F)(u:Directions G f)(e:Bond f):
    X.input u e=G.lieExp (bondMap X e u)*X.input 0 e:=by
  by_cases tree:e∈F.trunks
  · have read (a:Directions G f):X.input a e=1:=F.on_tree (X.view a) ⟨e,tree⟩
    simp [read,bondMap,tree]
  · have read (a:Directions G f):X.input a e=X.view a ⟨e,tree⟩:=F.off_tree _ ⟨e,tree⟩
    by_cases hot:X.Hot e
    · simp [read,Coat.view,bondMap,RG.increment,tree,hot]
    · simp [read,Coat.view,bondMap,tree,hot]

def linkBill (G:Gauge)(j:ℕ):ℝ:=2^j*eUniversal G j*‖(1:G.Mat)‖

theorem links (X:Coat T F)(j:ℕ)(u:Directions G f)(e:Bond f):
    Allows j (fun a:Directions G f=>G.mat (X.input a e)) u (linkBill G j):=by
  let L:=bondMap X e
  have M:‖L‖≤1:=bound X e
  have exp:Allows j (fun a:Directions G f=>G.mat (G.lieExp (L a))) u (eUniversal G j):=by
    refine ⟨(G.exp_jet.comp L.contDiff).contDiffAt,fun w hw=>?_⟩
    have hc:= (unitPrice G j).used
    refine (endless L u j w hw).trans (mul_le_mul_of_nonneg_left ?_ (ample_pos G).le)
    apply (pow_le_pow_left₀ (mul_nonneg (by linarith) (norm_nonneg L)) _ w).trans
      (pow_le_pow_right₀ (by linarith) hw)
    exact (mul_le_mul_of_nonneg_left M (by linarith)).trans (by linarith)
  have fixed:Allows j (fun _:Directions G f=>G.mat (X.input 0 e)) u ‖(1:G.Mat)‖:=
    allows_const u (unit_pay (X.input 0 e)).le
  have fields:(fun a:Directions G f=>G.mat (X.input a e))=
      fun a=>G.mat (G.lieExp (L a)*X.input 0 e):=funext fun a=>congrArg G.mat (link X a e)
  rw [fields]
  exact exp.times fixed

def filed {k:ℕ}(atoms:Stack G k){g:ℕ}(draw:Commission atoms σ A g)(hs:0<σ):book G (k+2):=
  ⟨atoms,σ,A,hs,draw.toll,draw.hue⟩

def tariff (G:Gauge)(k j:ℕ)(σ:ℝ):ℝ:=
  composeCost j ((1+(2:ℝ)^j/Work.F02.radius σ)^j) (linkBill G j)*|Work.F02.slotConst G|^k

/-- This is a single true reported site, retaining its entire countable path
    bank and every original signed orientation. Its price has no torus cardinal. -/
theorem directions (X:Coat T F)(a:PrismA G)(draw:Commission a.cells σ A a.grade)(hs:0<σ)
    (s:Signed)(x:Site f)(j:ℕ)(u:Directions G f):
    Brush j (A*tariff G (a.rise+2) j σ) 1
      (fun v:Directions G f=>∑' n,(a.cells n).unmasked (pull s 0 (X.input v)) x) u:=
  (filed a.cells draw hs).slab_notes X.input (links X j) s x u

private theorem norm_diff {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h:E→ℝ)(C:ℝ)(q:∀x,Brush 1 C 1 h x)(u v:E):|h u-h v|≤C*‖u-v‖:=by
  have regular (x:E) (_hx:x∈(Set.univ:Set E)):DifferentiableAt ℝ h x:=
    (q x).smooth.differentiableAt (by norm_num)
  have slopes (x:E) (_hx:x∈(Set.univ:Set E)):‖fderiv ℝ h x‖≤C:=by
    simpa only [normJ,norm_iteratedFDeriv_one,one_pow,mul_one] using (q x).order 1 le_rfl
  change ‖h u-h v‖≤C*‖u-v‖
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (s:=Set.univ) (f:=h) (C:=C) (𝕜:=ℝ)
    regular slopes (convex_univ) (Set.mem_univ v) (Set.mem_univ u)

theorem compared (X:Coat T F)(a:PrismA G)(draw:Commission a.cells σ A a.grade)(hs:0<σ)
    (x:Site f)(u v:Directions G f):
    |OriginalMarkedRunAction.sitePacket a.cells x (X.input u)-
      OriginalMarkedRunAction.sitePacket a.cells x (X.input v)|≤A*tariff G (a.rise+2) 1 σ*‖u-v‖:=by
  let single (s:Signed)(b:Directions G f):ℝ:=∑' n,(a.cells n).unmasked (pull s 0 (X.input b)) x
  have one (s:Signed):|single s u-single s v|≤A*tariff G (a.rise+2) 1 σ*‖u-v‖:=by
    have q (b:Directions G f):Brush 1 (A*tariff G (a.rise+2) 1 σ) 1 (single s) b:=directions X a draw hs s x 1 b
    exact norm_diff (single s) _ q u v
  have all:=OriginalMarkedRunAction.mean_bound (fun s=>single s u-single s v) _ one
  simpa only [OriginalMarkedRunAction.sitePacket,Patch.average,Finset.sum_sub_distrib,mul_sub,single] using all

end YM.Integration.WilsonRootedHeldPacketGerm
