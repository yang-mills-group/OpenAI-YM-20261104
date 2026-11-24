import YM.WilsonBridge.Exponent
import YM.PertExtension.OrbTree
import YM.PertExtension.OrbExpansion
import YM.MS.Wilson.Gauge

/-!
# The actual orbit position alphabet and based BRST vector field

Use positive links, one per `PertExtension.Orb.OEdge` on the even torus (arbitrary
edge representative as there); include at a site just the ghost of *based*
equivariant gauge transformations. Root at the inversion-fixed origin. No half weights
on this independent edge chart (the action is *already* half the ambient action).
The ∆/Haar check includes the field-dependent log chart Jacobian here with no
field-independent mass proxy.
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBridge.Based
open PertExtension Orb
open MS Native Bare Koszul Lattice Filter Function Finset
open Cylinder Cylinder.Taylor
open scoped Topology ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}
/-- Non-root inversion orbit representatives. -/
abbrev BasedSite (n : Side) := {x : Site n // vertex x=x ∧ x≠0}
-- keep concrete decidable instances available for color coords
noncomputable instance (n:Side) : Fintype (BasedSite n) := by classical unfold BasedSite; infer_instance

namespace Position
variable (G n)
abbrev E := OEdge n → G.Color
abbrev U := BasedSite n → G.Color
abbrev Gluon := Eyes G (OEdge n)
abbrev Ghost := Eyes G (BasedSite n)
abbrev Letter := Based.Letters (Gluon G n) (Ghost G n)
abbrev Parity := Based.parity (Gluon G n) (Ghost G n)
abbrev Bracket := Based.bracket (Gluon G n) (Ghost G n)
variable {G n}

section
-- avoid inverse shade with mixed determinant by giving exact position lifts on logs
variable {R:Type} [AddCommGroup R] [Module ℝ R]
-- use representative directions. linear fields on all orbit edges (not tree slice)
def edgeField (n:Side) (R:Type) [AddCommGroup R] [Module ℝ R] : (OEdge n → R) →ₗ[ℝ] Links (Per n) R where
  toFun F e := if eR e=e then F (index e) else -(F (index e))
  map_add' f g := by funext i; simp only [Pi.add_apply]; split <;> simp [add_comm]
  map_smul' c f:= by funext i; simp only [Pi.smul_apply]; split <;> simp

lemma edge_spec (f : OEdge n → R) (e:Edge (Site n)) :
    edgeField n R f e = if eR e=e then f (index e) else -(f (index e)):= rfl
@[simp] lemma edge_rep (f : OEdge n → R) (e:OEdge n) : edgeField n R f e.val=f e:= by
  rw [edge_spec,if_pos e.property,show index e.val=e from Subtype.ext e.property]
lemma edge_even (hn : Even n.val) (f : OEdge n → R) (e) :
    edgeField n R f (reflect e)= -edgeField n R f e:= by
  simp_rw [edge_spec,eR_reflect,show index (reflect e)=index e from Subtype.ext (eR_reflect _)]
  rcases eR_spec e with h|h
  · simp [h,Ne.symm (no_fixed_edge hn e)]
  simp [h,no_fixed_edge hn e]
lemma edge_tree (A : Cotree n → R) : edgeField n R (genJet A)=variation A:= by
  classical
  funext e
  rw [edge_spec]
  unfold variation; dsimp only [LinearMap.coe_mk,AddHom.coe_mk]

def siteField (n:Side) (R:Type) [AddCommGroup R] [Module ℝ R] : (BasedSite n→R) →ₗ[ℝ] (Site n→R) where
  toFun U x:= if h: vertex x=0 then 0 else U ⟨vertex x,vertex_vertex _,h⟩
  map_add' f g:= by funext i; simp only [Pi.add_apply]; split <;> simp
  map_smul' c f:= by funext i; simp only [Pi.smul_apply]; split <;> simp
lemma site_spec (f : BasedSite n → R)(x : Site n): siteField n R f x= if h: vertex x=0 then 0 else f ⟨vertex x,vertex_vertex _,h⟩:= rfl
@[simp] lemma site_root (f : BasedSite n → R): siteField n R f 0=0:= by rw [site_spec,dif_pos vertex_zero]
lemma site_even (f : BasedSite n → R)(x : Site n): siteField n R f (-x)=siteField n R f x := by
  rw [site_spec, site_spec]; split_ifs with h h'
  · rfl
  · exact False.elim (h' (vertex_neg x ▸ h))
  · exact False.elim (h (by rwa [vertex_neg]))
  exact congr_arg f (Subtype.ext (vertex_neg _))
@[simp] lemma site_rep (f : BasedSite n → R)(x:BasedSite n): siteField n R f x.val=f x:= by
  rw [site_spec,dif_neg (fun h=>x.2.2 (vertex_eq_iff.mp h)),show (⟨vertex x.val, _⟩:BasedSite n)=x from Subtype.ext x.2.1] -- `_` structure
end

-- actual compact Lie algebra. Ordinary finite proof.
local notation "Tτ" => colorTerm G (BasedSite n)
abbrev endAt (e:OEdge n) := Chart.endRail (Chart.drive n) e.val
abbrev endpoints (G:Gauge)(n:Side)(e:OEdge n) : U G n →ₗ[ℝ] Maurer.Ends G:= (Chart.route (Chart.drive n) e.val).comp (siteField n G.Color)

def based (F:E G n): U G n →ₗ[ℝ] E G n:= LinearMap.pi fun i=> (Maurer.voltage (F i)).comp (endpoints G n i)
def generator (i:Ghost G n)(F:E G n): E G n:= based F (priv i)
lemma gen_at (i:Ghost G n)(F:E G n)(e) : generator i F e=Maurer.volts (endpoints G n e (priv i)) (F e):=rfl
lemma ongoing (i:Ghost G n): germ (generator i):= contDiffAt_pi.mpr (fun j => by
    change ContDiffAt ℝ ω (fun x:E G n=>Maurer.volts (endpoints G n j (priv i)) (x j)) _
    exact (Maurer.home _).comp (f:= fun x:E G n=> x j) (0:E G n) (contDiff_apply ..|>.contDiffAt))
lemma push_gen {i:Ghost G n}{F H:E G n}(h : DifferentiableAt ℝ (generator i) F)(e:OEdge n)(he:DifferentiableAt ℝ (Maurer.volts (endpoints G n e (priv i))) (F e)): fderiv ℝ (generator i) F H e=fderiv ℝ (Maurer.volts (endpoints G n e (priv i))) (F e) (H e) := by
    let X:E G n→L[ℝ] G.Color:= ContinuousLinearMap.proj e; let V:=Maurer.volts (endpoints G n e (priv i))
    have hX : X ∘ generator i= V ∘ X :=rfl
    have ht:= fderiv_comp F X.differentiableAt h; rw [hX,fderiv_comp F (show DifferentiableAt ℝ V (X F) from he) X.differentiableAt,X.fderiv,X.fderiv] at ht
    exact DFunLike.congr_fun ht.symm H
lemma braid_site (x y:U G n) (i:Site n): siteField n G.Color (Native.braid x y) i = G.ad (siteField n G.Color x i) (siteField n G.Color y i):= by
  simp_rw [site_spec]; split; · simp
  rfl
lemma turns (F H:U G n)(e:OEdge n) : Maurer.braid (endpoints G n e F) (endpoints G n e H)=endpoints G n e (Native.braid F H):= Prod.ext (braid_site F H e.val.1).symm (braid_site F H (endAt e)).symm
lemma winds : Focus.Vibes Tτ generator := by
    refine ⟨cartan ..,ongoing,fun i j=>?_⟩
    obtain ⟨r,hr,W⟩:= LocalH.geom_patch G
    filter_upwards [eventually_all.mpr (fun e:OEdge n=> (show ∀ᶠ F:E G n in 𝓝 0,F e∈ Metric.ball 0 r from
      (continuous_apply e|>.tendsto (0:E G n)).eventually (Metric.ball_mem_nhds _ hr))), (ongoing i).eventually (by simp), (ongoing j).eventually (by simp)] with F h hI hJ
    rw [show ∑ k,colorTerm G (BasedSite n) i j k • generator k F=based F (Native.braid (priv i) (priv j)) from (by rw [← crowd,map_sum]; simp only [map_smul,generator])]
    funext e; simp only [Pi.sub_apply, push_gen (hI.differentiableAt (by simp)) e ((Maurer.analytic_volts _ (W r (le_refl r)) (h e)).differentiableAt (by simp)), push_gen (hJ.differentiableAt (by simp)) e ((Maurer.analytic_volts _ (W r (le_refl r)) (h e)).differentiableAt (by simp)), gen_at, Maurer.storm _ _ (W r (le_refl r)) (h e), turns ]; rfl

variable (G n)
abbrev focus : Bare.Focus (Bracket G n) (Gluon G n) (Ghost G n) := ⟨Equiv.refl _,fun _=>rfl,fun _=>rfl ⟩

def glow : Focus.Glow (focus G n) (E G n) where
    e0 z:= match z with
      | Sum.inl (Sum.inl i)=>priv i
      | _=> 0
    seed := projector
    restore F := Native.frame F
    ever x hx:= by rcases x with (i|i)|(i|i) <;> first| exact ⟨_,rfl⟩| exact False.elim (hx rfl)
variable {G n}

def logHaar (F:E G n) : ℝ:=∑ i:OEdge n,Maurer.lac (F i)
lemma haarSmooth : germ (logHaar (G:=G) (n:=n)):= ContDiffAt.sum (fun i _=> (Maurer.hlog G).comp (f:=fun x:E G n=>x i) (0:E G n) (contDiff_apply ..|>.contDiffAt))
lemma haar_fderiv {F A:E G n}(h:∀ i:OEdge n,DifferentiableAt ℝ (Maurer.lac (G:=G)) (F i)): fderiv ℝ (logHaar (G:=G) (n:=n)) F A=∑ i: OEdge n, fderiv ℝ Maurer.lac (F i) (A i):= by
    let T i : E G n→L[ℝ] G.Color:= ContinuousLinearMap.proj i
    have hh i:= (h i).hasFDerivAt.comp (f:=⇑(T i)) F (T i).hasFDerivAt; rw [show fderiv ℝ logHaar F=_ from (HasFDerivAt.fun_sum fun i _=> hh i).fderiv]; simp; rfl
lemma index_div (k:Ghost G n) : ∀ᶠ F:E G n in 𝓝 0, Focus.index_div (glow G n) (generator k) F=∑ i:OEdge n,Maurer.divs (Maurer.volts (endpoints G n i (priv k))) (F i):=by
    filter_upwards [(ongoing k).eventually (by simp),eventually_all.mpr (fun x:OEdge n=> (continuous_apply x|>.tendsto (0:E G n)).eventually ((Maurer.home (endpoints G n x (priv k))).eventually (by simp)))] with F h he
    unfold Focus.index_div; rw [Finset.sum_apply,Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _=>?_)
    rw [Maurer.by_row]; apply Finset.sum_congr rfl; intro j _; have hv : DifferentiableAt ℝ (generator k) F:= h.differentiableAt (by simp)
    change fderiv ℝ (projector (i,j)∘ generator k) F (priv (i,j))=fderiv ℝ (Maurer.volts _) (F i) (baseC j) j
    rw [fderiv_comp F (projector (i,j)).differentiableAt hv,(projector (i,j)).fderiv,ContinuousLinearMap.comp_apply,projector_k]
    rw [push_gen hv i ((he i).differentiableAt (by simp))]; simp [priv]
lemma volume_charge : Focus.Bills (glow G n) generator logHaar:= by
    intro k; filter_upwards [index_div k,eventually_all.mpr (fun x:OEdge n=> (continuous_apply x|>.tendsto (0:E G n)).eventually ((Maurer.wind_div (endpoints G n x (priv k))).and ((Maurer.hlog G).eventually (by simp))))] with F hA h
    change Focus.index_div _ _ F+ fderiv ℝ logHaar F (generator k F)=0
    rw [hA, haar_fderiv (fun i=> (h i).2.differentiableAt (by simp)),← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun i _=> (h i).1

end Position
end YM.WilsonBridge.Based
