import YM.MSbar.Symbol.Shear
import YM.MSbar.Scale.Cell
/-!
Analytic region & uniformly finite Laurent order. Need unbounded-plane transforms only for
analytic uniqueness at the integer dimensions, while vertices in Laurent recursion are holomorphic
(with possible finite pole order) on the proper profit regions only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Counter
open Dim Symbol Domain Diagram Scale Super Loops Function Set Filter
open scoped Classical Topology BigOperators ContDiff

class Profit (U:Set ℂ): Prop where
    proper : U ≠ univ
    around : 0∈ U
    pub : IsOpen U
-- Eq modulo punctured agreement
def rim (U:Set ℂ) := U \ {0}
@[simp] lemma rim_mem (U:Set ℂ) (z:ℂ): z∈rim U ↔ z ∈ U ∧ z ≠ 0:= .rfl
variable {C:Type} {m j:ℕ} {U:Set ℂ} {W:Edition C}{d:Bit} {f g: Vertex C}{F G:Functionals C}
namespace Charting
lemma shear (z:ℂ) [p:Profit U] (hz:z∈U): Chart (𝓟 U) (fun f:ℂ→ℂ => dslope f 0 z) (fun f=> DifferentiableOn ℂ f U) := by
   have h0: U ∈ 𝓝 0:= p.pub.mem_nhds p.around
   have hk (f g : ℂ→ℂ)(h:f=ᶠ[𝓟 U] g): dslope f 0 z= dslope g 0 z:=by
      have ht : EqOn f g U:= fun x hx => eventually_principal.mp h x hx
      by_cases he:z=0
      · rw [he,dslope_same,dslope_same]; exact (ht.eventuallyEq_of_mem h0).deriv_eq
      simp only [dslope_of_ne _ he,slope_def_module,ht p.around,ht hz]
   refine ⟨fun {_} _ h=>?_, fun {_ _} _ _ h=> hk _ _ h,?_,?_⟩ -- strict implicit?
   · rw [hk _ _ h]; rcases eq_or_ne z 0 with rfl|he; simp only [dslope_same,deriv_zero,Pi.zero_apply]; simp [dslope_of_ne _ he,slope_def_module]
   · intro a b c ha hb hc H; rw [hk _ _ H]; rcases eq_or_ne z 0 with rfl|he
     · rw [dslope_same,dslope_same,dslope_same,deriv_add (ha.differentiableAt h0) (hb.differentiableAt h0)]
     simp [dslope_of_ne _ he,slope_def_module]; ring
   intro a b c ha hb H; rw [hk _ _ H]; rcases eq_or_ne z 0 with rfl|he
   · rw [dslope_same,dslope_same]; exact deriv_const_mul c (hb.differentiableAt h0)
   simp [dslope_of_ne _ he,slope_def_module]; ring
end Charting

def chop (F:Functionals C) : Functionals C:= fun z m x=> dslope (fun t=> F t m x) 0 z
lemma stripping (F:Functionals C) (z:ℂ): z • chop F z= F z-F 0 := funext fun m=> funext fun x=>by simpa only [sub_zero,smul_eq_mul] using! sub_smul_dslope (fun z=>F z m x) 0 z
-- Complete mass-angular grade
abbrev Bright (U:Set ℂ) (W:Edition C)(d:Bit) (F:Functionals C) := Full U 0 W d F
-- multiply by function of regulator parameter
def times {X:Type*}[SMul ℂ X](f:ℂ→ℂ)(g:ℂ→X): ℂ→X:= fun z=> f z • g z
namespace Bright
variable [p:Profit U] (h: Bright U W d F)
omit [Profit U] in
lemma sum {ι:Type*}(s:Finset ι){F:ι→Functionals C}(hf:∀ i∈s,Bright U W d (F i)): Bright U W d (∑ i∈s,F i):= Full.sum _ hf
include h
lemma hol (i:Words C m): DifferentiableOn ℂ (fun z=>F z m i) U:= fun z hz=> ((h.total.wager p.pub i).cost.cr z 0 hz).differentiableWithinAt
lemma chops : Bright U W d (chop F):= by
    refine using_cell (fun z hz=> Cell.reform (A:=fun _ f=> dslope f 0 z) (fun _=>Charting.shear z hz) (eventually_principal.mpr (fun y hy=> full_cell h hy)) (fun n u=> Bright.hol h u)) ?_
    introv H; exact ⟨Symbol.AH.peeling ((h.licensed.ev _ _ H).cost) p.pub p.around,fun H=> (p.proper H).elim⟩
lemma temp {c:ℂ→ℂ} (hc:DifferentiableOn ℂ c U): Bright U W d (times c F):= by
    refine using_cell (fun z hz=> live_cell (Live.scale (c z) (h.freeze hz))) ?_; intro E i1 i2 i3 m x hx
    exact ⟨(Symbol.AH.holomorphic (X:=E) p.pub hc).mul ((h.licensed.ev _ _ hx).cost),fun H=> (p.proper H).elim⟩
lemma keep (hf:EqOn F G (rim U))(hg:Bright U W d G): EqOn F G U:= by
   intro x hx; by_cases H:x=0
   swap; exact hf ⟨hx,H⟩
   subst x; funext m v; apply tendsto_nhds_unique (l:=𝓝[≠] (0:ℂ)) ((hol h v 0 p.around |>.differentiableAt (p.pub.mem_nhds p.around)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
   refine ((hol hg v 0 p.around|>.differentiableAt (p.pub.mem_nhds p.around)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
   filter_upwards [eventually_nhdsWithin_of_eventually_nhds (show ∀ᶠ x in 𝓝 (0:ℂ),x∈ U from p.pub.mem_nhds p.around),self_mem_nhdsWithin] with x hx hC; exact congr_fun (congr_fun (hf ⟨hx,hC⟩) m) v|>.symm
end Bright
end YM.MSbar.Counter
