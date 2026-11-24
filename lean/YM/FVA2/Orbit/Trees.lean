import YM.FVA2.Orbit.Vertical
import YM.PertExtension.OrbHessian
/-!
# Ordinary tree prescription in the orbit coordinates

No FP/Haar-Jacobian from the dropped links once `tree` in our convention. `Permitted` uses the
algebraic spanning-tree criterion, in the graph of link orbits with `0` the root: the signed
incidence map on real colors on this subset, with the root removed, is bijective (see `incidence` below, this uses the actual linear differential test). This even lets the independence results
handle a trivial gauge with zero Lie algebra (in which a non-tree could also be admitted; no
perturbative dependence). In `TreeChoice.lean` we also show the established quotient tree `Orb.Branch` is
a permitted choice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Orbit
namespace Grove
open Function Set Filter Finset Topology MS.Bare Lattice PertExtension PertExtension.Orb LocalH
open scoped ContDiff Topology Matrix.Norms.Frobenius Classical BigOperators
variable {G:Gauge} {n:Side}
local notation "T" => Site n
local notation "L" => Edge T
local notation "R" => Root G n
local notation "V" => Rep G n
local notation "I" => OEdge n
local notation "e" => G.lieExp
abbrev Line (n:Side) := OEdge n → Prop
abbrev Complement {n:Side} (G:Gauge) (S:Line n):= {x//¬ S x}→G.Color
abbrev Direct {n:Side}(G:Gauge)(S:Line n):= {x//S x}→G.Color
variable (S : Line n)
def take : Rep G n →ₗ[ℝ] Direct G S:= LinearMap.pi fun i=> LinearMap.proj i.val
def leave : Rep G n →ₗ[ℝ] Complement G S:= LinearMap.pi fun i=> LinearMap.proj i.val

def rise : Complement G S →ₗ[ℝ] Rep G n:= LinearMap.pi fun i=> if h:¬ S i then LinearMap.proj ⟨i,h⟩ else 0
lemma rise_nil (x : Complement G S): take S (rise S x)=0:= by funext i; simp [take,rise,i.property]
lemma rise_up (x : Complement G S): leave S (rise S x)=x:= by funext i; simp [leave,rise,i.property]
lemma joint {p q:V} (h:take S p=take S q)(k:leave S p=leave S q): p=q:= by funext i; by_cases hi:S i; exact congr_fun h (⟨i,hi⟩); exact congr_fun k ⟨i,hi⟩
/-- Algebraic spanning-tree criterion on the actual rooted incidence. -/
def Permitted (G:Gauge) (S: Line n) := Bijective (take S ∘ₗ vertical (0:Rep G n))
-- literal negative gradient root-frozen
lemma incidence : Permitted G S ↔ Bijective (fun z: Root G n=> fun i:{x: OEdge n // S x}=> let w:=i.val.val; atSite w.1 z- atSite (w.1+step w.2) z) := by
    let L':=fun z: Root G n=> take S (touches G n (Pert.Orb.gZ (gaugeAngles G n z))); have he : (⇑(take S ∘ₗ vertical (0:V)))=Neg.neg ∘ L':= by funext z; change take S (vertical _ _) = _; rw [vertical_flat,map_neg]; rfl
    unfold Permitted; rw [he]; exact Equiv.neg (Direct G S)|>.comp_bijective L' -- lemma name

def shrub (G:Gauge) (S:Line n) (h:Permitted G S):Screen G n (Complement G S) where
 σ:= rise S
 origin:= (rise S).map_zero
 germ:= (rise (G:=G) S).toContinuousLinearMap.contDiff.contDiffAt
 valid:=by
   let σ: Complement G S →L[ℝ]Rep G n:= (rise S).toContinuousLinearMap
   have h' x y: fderiv ℝ (orbiting (⇑(rise (G:=G) S))) 0 (x,y)= vertical (0:Rep G n) x + σ y:= by
      have he:= (axes_later (⇑σ) σ.contDiff.contDiffAt σ.map_zero).self_of_nhds x y; rw [map_zero,σ.fderiv] at he; exact he
   have hv y : leave S (σ y)=y:= rise_up S y; have hx y:take S (σ y)=0:= rise_nil S y; constructor
   · rintro ⟨x,y⟩ ⟨z,w⟩ k
     rw [h',h'] at k; have H:= congr_arg (take (G:=G) S) k; simp only [map_add,hx,add_zero] at H; obtain rfl := h.1 H; exact congr_arg (Prod.mk x) ( (hv y).symm.trans ( (congr_arg (leave S) (add_left_cancel k)).trans (hv w)))
   intro x; obtain ⟨z,hz⟩:= h.2 (take S x); change take S (vertical (0:Rep G n) z) = _ at hz
   let t:= vertical (0:Rep G n) z; refine ⟨(z, leave S x-leave S t),?_⟩
   rw [h']; apply joint S
   · rw [map_add,hx,add_zero]; exact hz
   rw [map_add,hv]; change leave S t + _ = _; abel
lemma shrub_down (h:Permitted G S): (shrub G S h).σ=rise S:=rfl
lemma shrub_cost (h:Permitted G S) : ∀ᶠ p:Complement G S in 𝓝 0,(shrub G S h).weight p= hair p:= by
    let s:= shrub G S h; let f (p:Complement G S):=s.σ p; let L':= s.hurdle; let D:=fderiv ℝ s.tilt; let Y':= ContinuousLinearMap.id ℝ (Complement G S); let k:= (rise (G:=G) S).toContinuousLinearMap; have hD : ∀ᶠ p:Complement G S in 𝓝 0,∀ x y,D (0,p) (x,y)= vertical (f p) x+k y := by
        filter_upwards [axes_later (⇑k) k.contDiff.contDiffAt k.map_zero] with p hp; simp_rw [k.fderiv] at hp; exact hp
    have hk (x y) : L' (x,y)= vertical 0 x + k y:= by
        rw [←show f 0=0 from s.origin]; exact hD.self_of_nhds x y -- rw direction
    filter_upwards [hD] with p hp
    have he z : take S (vertical (f p) z)=take S (vertical 0 z):= by
       have hA:= rise_nil S p; funext i; change Maurer.voltage _ _= Maurer.voltage _ _
       rw [show f p i.val=0 from congr_fun hA i];rfl
    have hz (x : Complement G S): take S (k x)=0:= rise_nil S x
    have hP := D (0,p); let M:= L'.symm.toContinuousLinearMap ∘L D (0,p)
    have hM (y) : M (0,y)=(0,y):= L'.injective ( (L'.apply_symm_apply (D (0,p) (0,y))).trans (by rw [hp,hk,map_zero,map_zero]))
    let A:= ContinuousLinearEquiv.prodComm ℝ (Complement G S) (Root G n)
    let H:= A.symm.toContinuousLinearMap ∘L M ∘L A.toContinuousLinearMap
    have hu : H.det=M.det:= LinearMap.det_conj M.toLinearMap A.symm.toLinearEquiv
    have hh (x:R) : (M (x,0)).1=x:= by
       let T':= M (x,0); have W:take S (vertical (0:Rep G n) T'.1 + k T'.2)=take S (vertical 0 x):= by
          rw [← hk, show L' (T'.1,T'.2)=D (0,p) (x,0) from L'.apply_symm_apply (D (0,p) (x,0)), hp,map_zero,add_zero,he];
       rw [map_add,hz,add_zero] at W; exact h.1 W
    have hb:= upper H Y' (ContinuousLinearMap.id ℝ R) (fun x=> by change (M (0,x)).swap=(x,0); rw [hM]; rfl) hh; rw [hu,show Y'.det=1 from map_one LinearMap.det, show (ContinuousLinearMap.id ℝ R).det=1 from map_one LinearMap.det,one_mul] at hb
    change hair (f p) * meter L' (D (0,p))= hair p; rw [adjust, show (L'.symm.toContinuousLinearMap ∘L D (0,p)).det=1 from hb,mul_one]; unfold hair; rw [← Fintype.prod_subtype_mul_prod_subtype S]
    have he (i:{x // S x}) : spin G (f p i.val)=1:= by rw [show f p i.val=0 from congr_fun (rise_nil S p) i, spin_zero]
    simp_rw [he]; rw [Finset.prod_const_one,one_mul]; exact Finset.prod_congr rfl fun i _=> congr_arg (spin G) (congr_fun (rise_up S p) i)
end Grove
end YM.FVA2.Orbit
