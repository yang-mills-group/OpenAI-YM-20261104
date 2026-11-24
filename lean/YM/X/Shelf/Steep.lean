import YM.X.Shelf.Pebble
import YM.X.Braid.Stitch
/-!
# Static tape for milk lift. finite support route.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Shelf
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}
local notation "mV"=>poly V
variable {Q:(ℕ→ℂ) → Prop} {P P': (ℕ→ℂ) → Prop}
variable {p:ℕ→poly V}{c:ℕ→ℂ}
lemma badge_plus {f: ℕ→poly V}(h:f∈Badge (poly V) P ⊤)(v:mV): (fun i=>v*f i)∈ Badge mV P ⊤:= moved (LinearMap.mulLeft ℂ v) (fun p _=> Submodule.mem_top) h
lemma smote (hP:∀ {c f :ℕ→ℂ},P' c→P f→ Q (c*f))(h:p∈Badge (poly V) P ⊤)(he:P' c) : (fun i=>c i • p i)∈Badge (poly V) Q ⊤:= by
    induction h using Submodule.span_induction with
    | mem x h=> obtain ⟨a,v,h,hx,rfl⟩:=h; simp_rw [smul_smul]; exact badged (c*a) (hP he h) Submodule.mem_top
    | zero=> simp only [Pi.zero_apply,smul_zero]; exact Submodule.zero_mem _
    | add f g a b x y=> simp only [Pi.add_apply,smul_add]; exact Submodule.add_mem _ x y
    | smul a z hp hx=>simp_rw [Pi.smul_apply,smul_comm (c _) a];exact Submodule.smul_mem _ a hx
-- for τ(t) of Released scalars and static vectors.
lemma due (m:ℕ→ V→ℂ)(p:poly V)(h:∀ v,P (fun i=>m i v)): (fun i=> slit (m i) p)∈Badge mV P ⊤:= by
    induction p using MvPolynomial.induction_on with
    | C x=> simp only [slit_C]; exact Submodule.zero_mem _
    | add a b ih ih'=> simp_rw [map_add];exact Submodule.add_mem _ ih ih'
    | mul_X p i IH=> rw [mul_comm p]; simp_rw [slit_prod,C_mul']; exact Submodule.add_mem _ (badge_plus IH _) (badged _ (h i) Submodule.mem_top)
lemma dues (hP:∀ {c f:ℕ→ℂ}, P c→P' f→ Q (c*f))(v:ℕ→V→ℂ)(he:∀ i:V,P' (fun t=>v t i))(h:p∈Badge (poly V) P ⊤) : (fun i=> slit (v i) (p i))∈Badge (poly V) Q ⊤:= by
    induction h using Submodule.span_induction with
    | mem i h=> obtain ⟨a,z,h,he',rfl⟩:=h; simp_rw [Derivation.map_smul]; exact smote hP (due v z he) h -- name
    | zero => simp_rw [Pi.zero_apply,map_zero];exact Submodule.zero_mem _
    | add a b _ _ x y=> simp_rw [Pi.add_apply,map_add];exact Submodule.add_mem _ x y
    | smul t a _ h=>simp only [Pi.smul_apply,Derivation.map_smul];exact Submodule.smul_mem _ t h
lemma always (Q:ℕ→Symmetric V)(h:∀ i j, Released (fun t=>(Q t).cov i j))(p:mV): (fun i=>milk (Q i) p)∈Steady mV:= by
    induction p using MvPolynomial.induction_on with
    | C x=> simp_rw [Normal.fine]; apply stead
    | add a b h₀ ih=> simp_rw [map_add];exact Submodule.add_mem _ h₀ ih
    | mul_X p i IH=> rw [mul_comm p]; simp_rw [feeds]; exact Submodule.add_mem _ (badge_plus IH _) (dues (fun b h₁=> breaths b h₁) _ (h i) IH)
lemma slit_shutter (x y:V→ℂ)(p:poly V): slit (x-y) p= slit x p-slit y p:= by rw [sub_eq_add_neg,slit_linear,← neg_one_smul ℂ y, slit_smul];simp [sub_eq_add_neg]
include hq
lemma milk_slow (A:Symmetric V)(Q:ℕ→Symmetric V)(h:∀ i j, Vanished q (fun t=>(Q t).cov i j-A.cov i j))(p:mV): (fun i=> milk (Q i) p - milk A p)∈ Badge mV (Vanished q) ⊤:= by
    have hk(i j): Released (fun t=>(Q t).cov i j) := by rw [show (fun t=>(Q t).cov i j)=(fun t=>(Q t).cov i j-A.cov i j)+(fun t=> A.cov i j) from by ext1 t; simp]; exact (late hq (h i j)).add (constell _)
    let B:= Badge mV (Vanished q) ⊤
    induction p using MvPolynomial.induction_on with
    | C x=> simp only [fine,sub_self];exact Submodule.zero_mem _
    | add a b x y=>simp_rw [map_add,add_sub_add_comm];exact Submodule.add_mem _ x y
    | mul_X p i IH=>
       rw [mul_comm p]; let r(t):= (milk (Q t) p); let s':=milk A p; let n(t):=(Q t).cov i; let b:=A.cov i; simp_rw [feeds,add_sub_add_comm,←mul_sub]
       have he t: slit (n t) (r t) - slit b s'=slit (n t) (r t-s')+ slit (n t-b) s':= by rw [slit_shutter,map_sub]; abel
       have hp : (fun t=>slit (n t) (r t)-slit b s') ∈ B:= by simp_rw [he]; exact B.add_mem (dues (fun h hu=> Vanished.left h (charged hu)) n (hk i) IH) (due (P:=Vanished q) _ s' (h i))
       exact B.add_mem (badge_plus IH _) hp
end YM.PositionX.Shelf
