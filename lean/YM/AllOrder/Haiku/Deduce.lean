import YM.AllOrder.Haiku.Origin
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

variable {A B:ℕ→ Bills (Coarse G)}
abbrev Constant {ι:Type*}(f:ι→ℝ):Prop:=∀ x y,f x=f y
def Station (k:ℕ)(n:Side)(A:ℕ→ Bills (Coarse G)) := ∀ i<k, Constant (A i n)
-- may tag ANY transform with Pointwise Equality, only cares regular site
abbrev Smooth (k:ℕ)(n:Side)(A:ℕ→Bills (Coarse G)):= ∀ r≤k,Plausible (A r n)
variable (h:Etiquette A n k)
include h in
lemma Etiquette.less (H:Etiquette B n k)(hA:Smooth k n A)(hB:Smooth k n B): Etiquette (A-B) n k:= by
 have hv(x:ℝ→ F[n])(hx:ContDiffAt ℝ ω x 0): weigh x (fun i=>(A-B) i n) k=weigh x (fun i=>A i n) k-weigh x (fun i=>B i n) k:= weigh_sub hx (fun i hi=> (hA i hi).smooth.contDiffAt) le_rfl (fun i hi=> (hB i hi).smooth.contDiffAt)
 refine ⟨fun x y v w hx hy hV hu=>((hv x hx).trans ((congr_arg₂ (fun a b:ℝ=>a-b) (h.stain x y v w hx hy hV hu) (H.stain x y v w hx hy hV hu)).trans (hv _ hy).symm)),fun x s hx=>?_⟩; exact ((hv x hx).trans ((congr_arg₂ (fun a b:ℝ=>a-b) (h.sign x s hx) (H.sign x s hx)).trans (hv _ ((orderTurn s).contDiff.contDiffAt.comp _ hx)).symm))
-- common signed to all n, gives tangent formulas
include h in
lemma Etiquette.paints (u:G.El) : ∀ x:Link G n, A k n (Stationary.stain u x)= A k n x:= by
 intro x; let P:ℝ→Link G n:= fun _=>x; let Y(ζ:ℝ):=Stationary.stain u x; rw [← show weigh P (fun i=>A i n) k=A k n x from congr_fun (weigh_const ..) k,←show weigh Y (fun i=>A i n) k= A k n (Y 0) from congr_fun (weigh_const ..) k]; symm; apply h.stain P Y (fun _ _=>u) u contDiffAt_const contDiffAt_const tendsto_const_nhds; apply Eventually.of_forall; intro i; change input _ _ (i•Stationary.stain _ x)= _; rw [← map_smul]; exact (stain_cons u (i • x)).symm
include h in
lemma Etiquette.rotates (s:Signed) (x:Link G n): A k n (Stationary.orderTurn s x)=A k n x:= (show weigh (fun _=>Stationary.orderTurn s x) (fun i=>A i n) k=_ from congr_fun (weigh_const ..) k).symm.trans ((Etiquette.sign h (fun _=>x) s contDiffAt_const).symm.trans (congr_fun (weigh_const ..) k))
lemma Station.posts (Hs:Station k n A)(x:ℝ→ Link G n): weigh x (fun i=>A i n) k=A k n (x 0):= by
 unfold weigh; rw [sum_eq_single k, Nat.sub_self,someJ_zero];
 · rfl
 · intro j hj hh; have hz j' (h:j'<k):Constant (A j' n):=Hs j' h; rw [show A j n ∘ x= (fun _=> A j n 0) from funext fun t=> hz _ (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hh) _ _]; exact ((Act.static (n:=k-j) _).writes _ le_rfl).trans (if_neg (by have h:= Finset.mem_range.mp hj; omega))
 simp

include h in
lemma Etiquette.steady (Hs:Station k n A)(x:Swatch G n): A k n (x.2-gradientA G n x.1)=A k n x.2:= by
 let F' (p:ℝ):= p • x; let f:= moveField ∘ F'; let g:= Laplace.SigmaP.shift f; have he:F' 0=0:= by simp [F']
 have ht:f 0=0:= by simp only [f,he,Function.comp_apply,moveField_zero]
 have hf:ContDiffAt ℝ ω F' 0:= by unfold F'; fun_prop
 have hG: Tendsto F' (𝓝 0) (𝓝 0):=he ▸ hf.continuousAt
 have hg:ContDiffAt ℝ ω g 0:= shifty ((he.symm ▸ (moveField_analytic (G:=G) (m:=n)).contDiffAt).comp _ hf)
 have hv : echo g=f:=funext fun i=> (Laplace.SigmaP.shift_start ht i).symm; let V:ℝ→Link G n:=fun _=>x.2; let B:=A k n; let u(t:ℝ):= switchSite ((F' t).1); have hu:Tendsto u (𝓝 0) (𝓝 (fun _=>1)) := ((show Tendsto _ (𝓝 0) (𝓝 1) from switch_zero (G:=G) (m:=n) ▸ (switch_cont (G:=G) (m:=n)).continuousAt.tendsto.comp ((show Tendsto (fun t=> (F' t).1) (𝓝 0) (𝓝 0) from continuous_fst.continuousAt.tendsto.comp hG))))
 have h0:g 0=x.2-gradientA G n x.1:= by
     have hs : HasDerivAt f (fderiv ℝ moveField 0 x) 0 := Push.side _ moveField_analytic.differentiableAt x
     unfold g Laplace.SigmaP.shift; rw [dslope_same, hs.deriv,moveField_rate]
 rw [←h0, ← Station.posts Hs g, ←show weigh V (fun i=>A i n) k= A k n x.2 from Station.posts Hs V]; symm; apply h.stain V g u 1 contDiffAt_const hg hu; unfold Haiku.life; rw [hv]; exact (hG.eventually moveField_germ)
end YM.AllOrder.Haiku
