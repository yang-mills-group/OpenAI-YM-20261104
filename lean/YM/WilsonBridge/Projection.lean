import YM.WilsonBridge.Hessian
import YM.PertExtension.OrbCovariance

/-!
# The *same tree* supplies a based-gauge minor and projection

Without assuming rank facts about a graph, use the actual tree and the no
flat directions lemma already proved in `OrbExpansion`. Use this projection
with the Haar and cotree covariances of `PertExtension.Orb`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based.Position
open PertExtension Orb MS Native Bare Koszul Lattice Filter Function Finset
open Cylinder Cylinder.Taylor FreeBV
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}
local notation "Γ" => (based (0:E G n))

lemma no_gauge (F:E G n) (i:Ghost G n): hessian G n F (generator i 0)=0 := by
    have he:= (expGerm G n|>.fderiv_right (m:=ω) (by simp)).differentiableAt (by simp)
    have hv:= (ongoing i).differentiableAt (by simp)
    have hx : (fun x:E G n=> fderiv ℝ (exponent G n) x (generator i x))=ᶠ[𝓝 0] (fun _=>0):= expInvariant i
    have hh:= (he.hasFDerivAt.clm_apply hv.hasFDerivAt).congr_of_eventuallyEq hx.symm
    have hz:= DFunLike.congr_fun (hh.unique (hasFDerivAt_const _ _)) F
    rw [stationary] at hz; simpa [hessian] using hz
lemma pure_gauge (F:E G n)(u:U G n): hessian G n F (Γ u)=0:= by
    rw [← Native.frame u]; simp_rw [map_sum,map_smul,show ∀ i:Ghost G n,hessian G n F (Γ (priv i))=0 from no_gauge F]; simp
lemma lifted_grad (u:U G n)(e:Edge (Site n))(he:Even n.val) :
    let t:=siteField n G.Color u; edgeField n G.Color (Γ u) e= t (e.1+step e.2)- t e.1:= by
  intro t; have ht (v: OEdge n) : edgeField n G.Color (Γ u) v.val=t (v.val.1+step v.val.2)- t v.val.1:= by rw [edge_rep]; exact Maurer.volt_zero _
  rcases eR_spec e with hz|hz
  · exact ht (⟨e,hz⟩:OEdge n)
  have hh: eR (reflect e)=reflect e:= (eR_reflect _).trans hz
  have h:= ht ⟨reflect e,hh⟩; change edgeField n G.Color (Γ u) (reflect e)= t (-e.1-step e.2+step e.2)-t (-e.1-step e.2) at h; rw [ edge_even he, sub_add_cancel, show -e.1-step e.2= -(e.1+step e.2) from (by abel), show ∀ x,t (-x)=t x from site_even u, show ∀ x,t (-x)=t x from site_even u ] at h; exact neg_injective ((h.trans (neg_sub ..).symm))

open scoped Classical in
def minor (G:Gauge)(n:Side): U G n →ₗ[ℝ] (Trees n→G.Color):= LinearMap.pi fun i=> (LinearMap.proj i.val).comp (based (0:E G n)) -- `classical` pollutes? i DecEq used only type Pi
variable (G)
set_option maxHeartbeats 500000 in
lemma tree_minor (he:Even n.val): Bijective (minor G n) := by
    classical
    refine ⟨?_,?_⟩
    · apply LinearMap.ker_eq_bot.mp
      apply le_bot_iff.mp; intro u hu
      change minor G n u=0 at hu; change u=0
      let t:=siteField n G.Color u; let F:= edgeField n G.Color (Γ u)
      have hg (x:Site n) (i:Axis): F (x,i) = t (x+step i)-t x:= lifted_grad u _ he
      have hT (x:Site n)(d:Step): Orb.cash F d x=t (x+d.vec)-t x := by cases d with | mk i b=> cases b <;> simp [Orb.cash,Step.vec,Step.used, hg]; rw [sub_eq_add_neg]
      have ht (x:Site n) : t x=0 := by
        induction hx : depth x using Nat.strong_induction_on generalizing x with
        | _ k ih =>
          by_cases hy:x=0; rw [hy]; exact site_root u
          have hl : depth (x+(Orb.move x).vec) < k := (move_falls hy).trans_eq hx
          have h':=hT x (Orb.move x); rw [ ih _ hl _ rfl ] at h'
          have hf : F ((Orb.move x).used x)=0:= by
            let v : Trees n:= ⟨picked x,x,hy,rfl⟩; have he': Γ u (index ((Orb.move x).used x))=0:= congr_fun hu v
            unfold F; rw [edge_spec,he']; simp
          unfold Orb.cash at h'; rw [hf] at h'; simpa using h'.symm
      funext i; rw [← site_rep u i]; exact ht _
    intro b
    let F : Trees n → Multiplicative G.Color:= fun i=> Multiplicative.ofAdd (b i)
    let t : Site n → G.Color:= fun x=> Multiplicative.toAdd (Orb.frame F x)
    let u : U G n:= fun x=> t x.val
    have hs : siteField n G.Color u=t:= by
        funext x; rw [site_spec]; split
        next hx=>
            rw [vertex_eq_iff.mp hx]; unfold t; rw [Orb.frame,dif_pos vertex_zero]; rfl
        next => exact congr_arg Multiplicative.toAdd (Orb.frame_rep F x).symm
    refine ⟨u,funext fun i=>?_⟩
    change Γ u i.val=b i; change Maurer.volts _ _=_; rw [Pi.zero_apply,Maurer.volt_zero]
    change siteField n G.Color u (i.val.val.1+step i.val.val.2)-siteField n G.Color u i.val.val.1=_; rw [hs]
    have hz:= tree_zero he F 1 i; unfold aligned Lattice.gauge links at hz; rw [lift_at,splitLink,dif_pos i.property] at hz; change Multiplicative.ofAdd (t i.val.val.1)* Multiplicative.ofAdd (b i) * (Multiplicative.ofAdd (t _ ))⁻¹=1 at hz; apply_fun Multiplicative.toAdd at hz; change t i.val.val.1+b i+ -t (i.val.val.1+step i.val.val.2)=0 at hz; apply sub_eq_iff_eq_add.mpr; rw [add_comm (b i)]; exact (eq_neg_of_add_eq_zero_left hz|>.trans (neg_neg _)).symm

open scoped Classical
variable {G}
-- these two projections are actual coordinate restrictions; the Fixing projection
-- from `N` is not this coordinate restriction alone.
def restrictTree (G:Gauge)(n:Side) : E G n →ₗ[ℝ] (Trees n→G.Color):= LinearMap.pi fun i=> LinearMap.proj i.val
def co (G:Gauge)(n:Side) : E G n →ₗ[ℝ] (Cotree n→G.Color):= LinearMap.pi fun i=> LinearMap.proj i.val
def insertCo (G:Gauge)(n:Side) : Dir G n →ₗ[ℝ] E G n where
  toFun := genJet
  map_add' x y := by funext i; unfold genJet; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c x:= by funext i; unfold genJet; simp only [Pi.smul_apply]; split_ifs <;> simp
lemma co_at (x:Dir G n)(i:Cotree n) : insertCo G n x i.val=x i:= by change genJet _ _=_; rw [genJet,dif_pos i.property]
lemma co_off (x:Dir G n)(i:Trees n) : insertCo G n x i.val=0:= by change genJet _ _=_; rw [genJet,dif_neg (not_not_intro i.property)]

def Y (G:Gauge)(h:Even n.val): E G n →ₗ[ℝ] U G n:= (LinearEquiv.ofBijective (minor G n) (tree_minor G h)).symm.toLinearMap ∘ₗ restrictTree G n
lemma projects_y (he:Even n.val)(F:E G n) : minor G n (Y G he F)=restrictTree G n F:= (LinearEquiv.ofBijective _ (tree_minor G he)).apply_symm_apply (restrictTree G n F)
lemma solves_y (he:Even n.val)(u:U G n) : Y G he (Γ u)=u:= (LinearEquiv.ofBijective _ (tree_minor G he)).symm_apply_apply u
lemma erase_branch (he:Even n.val)(F:E G n) : F- Γ (Y G he F) = insertCo G n (co G n (F-Γ (Y G he F))) := by
  funext i; by_cases h:Branch i; swap; · exact (co_at (co G n (F-Γ (Y G he F))) (⟨i,h⟩: Cotree n)).symm
  rw [Pi.sub_apply, co_off _ (⟨i,h⟩:Trees n)]; exact sub_eq_zero.mpr ( congr_fun (projects_y he F) (⟨i,h⟩:Trees n) ).symm
lemma basis_pr {Q:Type} [DecidableEq Q][Fintype Q] (i j:Eyes G Q) : projector i (priv j)= if i=j then 1 else 0:= by
  rw [projector_k]; rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩; by_cases h:i=j <;> by_cases h':a=b <;> simp [priv,Native.baseC,h,h',EuclideanSpace.basisFun_apply]
lemma off_y (he:Even n.val)(i:Gluon G n)(h:¬ Branch i.1): Y G he (priv i)=0:= by
    have ht: restrictTree G n (priv i)=0:= funext fun j=> by
        change priv i j.val=0; apply Pi.single_eq_of_ne (show j.val≠i.1 from fun hz=> h (hz ▸ j.property)) -- maybe name
    change (LinearEquiv.ofBijective (minor G n) (tree_minor G he)).symm (restrictTree G n _)=0; rw [ht,map_zero]
end YM.WilsonBridge.Based.Position
