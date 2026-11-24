import YM.AllOrder.Haiku.Deduce
/-! Real locus Gram WITH MANY anchor parameter letters held fixed.
Building on Haiku.{Origin,Deduce}. Definition & tools generalize Stain component to API over ANY n/book (no required sign spatial invariance). -/
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
structure Vernal (G:Gauge)(n:Side)(A:Book (rule (Coarse G) n))(k:ℕ) :Prop where
 leaf (v w:ℝ→Stationary.Link G n) (u:ℝ→(Site n→G.El))(x:G.El): ContDiffAt ℝ ω v 0→ContDiffAt ℝ ω w 0 → Tendsto u (𝓝 0) (𝓝 (fun _=>x)) → life (G:=G) w=ᶠ[𝓝 0] (fun t=> gauge (u t) (life v t)) → weigh v A k= weigh w A k
-- no assumption analytic beyond what was already paid. t exposed formal g powers.
variable {A B:Book (Stationary.Link G n)} (h:Vernal G n A k)
include h
lemma Vernal.minus (H:Vernal G n B k) (hA:∀ i≤k,Plausible (A i))(hB:∀ i≤k,Plausible (B i)): Vernal G n (A-B) k:=by
 have he(x:ℝ→ Stationary.Link G n)(hx:ContDiffAt ℝ ω x 0): weigh x (A-B) k=weigh x A k-weigh x B k:= weigh_sub hx (fun i hi=> (hA i hi).smooth.contDiffAt) (le_refl k) (fun i hi=> (hB i hi).smooth.contDiffAt)
 exact ⟨fun u v w x hu hv hρ hg=>by rw [he u hu, he v hv,h.leaf u v w x hu hv hρ hg,H.leaf u v w x hu hv hρ hg]⟩
lemma Vernal.paints (u:G.El) : ∀ x:Link G n, A k (Stationary.stain u x)= A k x:= by
 intro x; let P:ℝ→Link G n:= fun _=>x; let Y(ζ:ℝ):=Stationary.stain u x; rw [← show weigh P A k=A k x from congr_fun (weigh_const ..) k,←show weigh Y A k= A k (Y 0) from congr_fun (weigh_const ..) k]; symm; apply h.leaf P Y (fun _ _=>u) u contDiffAt_const contDiffAt_const tendsto_const_nhds; apply Eventually.of_forall; intro i; change input _ _ (i•Stationary.stain _ x)= _; rw [← map_smul]; exact (stain_cons u (i • x)).symm
omit h in
lemma Vernal.billK (Hs:∀ i<k, Constant (A i))(x:ℝ→ Link G n): weigh x A k=A k (x 0):= by
 unfold weigh; rw [sum_eq_single k, Nat.sub_self,someJ_zero];
 · rfl
 · intro j hj hh; have hz j' (h:j'<k):Constant (A j'):=Hs j' h; rw [show A j ∘ x= (fun _=> A j 0) from funext fun t=> hz _ (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hh) _ _]; exact ((Act.static (n:=k-j) _).writes _ le_rfl).trans (if_neg (by have h:= Finset.mem_range.mp hj; omega))
 simp
lemma Vernal.steady (Hs:∀ i<k, Constant (A i))(x:Swatch G n): A k (x.2-gradientA G n x.1)=A k x.2:= by
 let F' (p:ℝ):= p • x; let f:= moveField ∘ F'; let g:= Laplace.SigmaP.shift f; have he:F' 0=0:= by simp [F']
 have ht:f 0=0:= by simp only [f,he,Function.comp_apply,moveField_zero]
 have hf:ContDiffAt ℝ ω F' 0:= by unfold F'; fun_prop
 have hG: Tendsto F' (𝓝 0) (𝓝 0):=he ▸ hf.continuousAt
 have hg:ContDiffAt ℝ ω g 0:= shifty ((he.symm ▸ (moveField_analytic (G:=G) (m:=n)).contDiffAt).comp _ hf)
 have hv : echo g=f:=funext fun i=> (Laplace.SigmaP.shift_start ht i).symm; let V:ℝ→Link G n:=fun _=>x.2; let B:=A k; let u(t:ℝ):= switchSite ((F' t).1); have hu:Tendsto u (𝓝 0) (𝓝 (fun _=>1)) := ((show Tendsto _ (𝓝 0) (𝓝 1) from switch_zero (G:=G) (m:=n) ▸ (switch_cont (G:=G) (m:=n)).continuousAt.tendsto.comp ((show Tendsto (fun t=> (F' t).1) (𝓝 0) (𝓝 0) from continuous_fst.continuousAt.tendsto.comp hG))))
 have h0:g 0=x.2-gradientA G n x.1:= by
     have hs : HasDerivAt f (fderiv ℝ moveField 0 x) 0 := Push.side _ moveField_analytic.differentiableAt x
     unfold g Laplace.SigmaP.shift; rw [dslope_same, hs.deriv,moveField_rate]
 rw [←h0, ← Vernal.billK Hs g, ←show weigh V A k= A k x.2 from Vernal.billK Hs V]; symm; apply h.leaf V g u 1 contDiffAt_const hg hu; unfold Haiku.life; rw [hv]; exact (hG.eventually moveField_germ)
-- Earn plan.E
end YM.AllOrder.Haiku
