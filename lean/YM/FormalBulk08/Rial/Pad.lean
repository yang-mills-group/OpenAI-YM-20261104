import YM.FormalBulk08.Pose.Alto

/-! Rooted top supplies. Stencil coordinate uses basis index in *that same*
F/every later consumer, proof for any appropriate SectionData on F. Real
columns (shared basis fixed by bar), untruncated polynomial stencil log.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Rial
open Filter Set Function Lattice Laurent Wilson Exterior Stationary
open Orb Jets Lava Lotus Mesa Gorge Shore City Kemp Rift Wine Pose PowerSeries Reef
open Planned.PrimaryIntegral295 Place Carrier Film Labels Source Source.Drops Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {S:Finset Cover} {d:ℕ}{F: Frame G d} {I:Type*} {j u l r :ℕ} {η A : ℝ}
abbrev SpotC (S:Finset Cover)(G:Gauge) := Spot S × hue G

def chamber (S:Finset Cover)(G:Gauge): SpotC S G → edgeL G := fun i=>((Place.first i.1).val,Exterior.coord (Place.beam i.1),i.2)
lemma chamber_safe (S:Finset Cover)(G:Gauge): Injective (chamber S G):= by
   rintro ⟨i,j⟩ ⟨k,l⟩ h
   have hi:(first i).val=(first k).val:=congr_arg (fun z:edgeL G=>z.1) h; have hk : axisEquiv (Place.beam i)=axisEquiv (Place.beam k):=congr_arg (fun z:edgeL G=>z.2.1) h; have hh : j=l:=congr_arg (fun z:edgeL G=>z.2.2) h
   exact Prod.ext (show i=k from Subtype.ext (Prod.ext (Subtype.ext hi) (axisEquiv.injective hk))) hh

def sofas (G:Gauge)(S:Finset Cover) : Jets.Rays (SpotC S G)≃L[ℝ]Dev S G:= LinearEquiv.toContinuousLinearEquiv {
    toFun x i:= City.moon G (fun j=> x (i,j))
    invFun f i:= (City.moon G).symm (f i.1) i.2
    map_add':= fun _ _=>rfl
    map_smul':=fun _ _=>rfl
    left_inv:=fun _=>rfl
    right_inv:=fun _=>rfl }
variable (T:SectionData F)(i:F.Index)

def lights (p:F.Index): Jets.Rays (SpotC T.stencil G)→ℝ:=fun x=>(Place.column T p (sofas _ _ x)).re
lemma lights_diff : ContDiff ℝ ω (lights T i):= Complex.reCLM.contDiff.comp ((column_smooth T i).comp (sofas G T.stencil).contDiff)
lemma unsetting (n:Side)(x: Jets.Rays (wire G n)): T.places (copy F i) 0 (input G n x)= Place.column T i (sofas G T.stencil (x ∘ Lotus.drip n ∘ chamber T.stencil G)):= by
   unfold SectionData.places Place.column slant; rw [Function.comp_apply]; apply T.cylinder_local; rintro ⟨a,b⟩ ha hb
   let p: Spot _:=⟨(⟨a,ha⟩,b),hb⟩; rw [show pore _ (a,b)=_ from (pore_site _ p),Lattice.expandAt,add_zero,input, Work.F03.represent_link]; rfl
lemma trueLamp (n:Side)(x: Jets.Rays (wire G n)): (T.places (copy F i) 0 (input G n x)).re= lights T i (x ∘ Lotus.drip n ∘ chamber T.stencil G):= by rw [unsetting];rfl
lemma litLower (h:Bid.pop T)(n : ℕ)(hn:n<(F.grades i).2): iteratedFDeriv ℝ n (lights T i) 0=0:= by
    let L:= Complex.reCLM
    let g:=sofas G T.stencil
    let P:= Place.column T i; have hp : ContDiff ℝ ω P:=column_smooth T i
    have he : lights T i= (L ∘ P) ∘ g.toContinuousLinearMap:=rfl
    rw [he, jets_linear g.toContinuousLinearMap ((L.contDiff.comp hp).contDiffAt.of_le le_top)]
    ext x; rw [L.iteratedFDeriv_comp_left hp.contDiffAt le_top,show iteratedFDeriv ℝ n P 0=0 from radials_vanish T h i n hn]; simp
lemma litLower_coeff (h:Bid.pop T)(n : ℕ)(hn:n<(F.grades i).2): PowerSeries.coeff n (paste (lights T i))=0:= by apply orbit_ext; intro x; rw [trace_paste,PertExtension.Series.Radial.jet, litLower T i h n hn]; simp [traceP]

def stencilP := Jets.paste (lights T i)
def dabs := afterX (stencilP T i) (F.grades i).2
lemma dab_origin (h:Bid.pop T):PowerSeries.X ^ (F.grades i).2 * dabs T i = paste (lights T i):= after_rope (paste (lights T i)) _ (litLower_coeff T i h)
lemma pinpaths (e r : ℕ)(h:r≠ (F.grades i).2+e):rancho (dabs T i) e r=0:= by rw [rancho,dabs,after_one,marble_eq_zero_iff,stencilP,MvPolynomial.homogeneousComponent_of_mem (paste_grade ..),if_neg h]

-- Rebase the finite support into the covering kernel at a single root.
def hymn (v: Tile (SpotC S G) r) : Tile (edgeL G) r := fun w=> ∑ i, if chamber S G ∘ i=w then v i else 0
lemma hymn_power (p:Tile (SpotC S G) r)(i): hymn p (chamber S G ∘ i)=p i:= by
    rw [hymn,Finset.sum_eq_single i,if_pos rfl]; intro j _ h; exact if_neg (fun h'=> h (funext fun l=> chamber_safe S G (congr_fun h' l))); simp
lemma hymn_floor (p:Tile (SpotC S G) r)(i:chain (edgeL G) r)(h:∀ v:chain (SpotC S G) r,chamber S G ∘ v≠i): hymn p i=0:= Finset.sum_eq_zero fun v _=> if_neg (h v)
lemma hymn_bill (A:Tile (SpotC S G) r)(η : ℝ)(x:edgeL G):∃ C,Knoxville (fame _) η x (hymn A) C:= by
    let V i (w: chain (edgeL G) r):= if chamber S G ∘ i=w then A i else 0
    have h: hymn A=∑ i,V i:=funext fun w=> by rw [Finset.sum_apply];rfl
    have he i : Knoxville (fame _) η x (V i) (Real.exp (η*herb (fame _) x (chamber S G ∘ i))*‖A i‖):= by
       refine ⟨by positivity,?_⟩;rw [tsum_eq_single (chamber S G ∘ i)]; swap;· intro b hb; unfold V; rw [if_neg (Ne.symm hb), enorm_zero,mul_zero]
       unfold V;rw [if_pos rfl, ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_norm];rfl
    rw [h]; exact ⟨_,knox_sum Finset.univ (fun i _=> he i)⟩
lemma hymn_agate (v:Tile (SpotC S G) r)(h:Agate v): Agate (hymn v):= by
    intro w s; unfold hymn; refine (Fintype.sum_equiv (Equiv.arrowCongr s.symm (Equiv.refl (SpotC S G))) _ _ fun i=>?_).symm; change (if chamber S G ∘ i=w then _ else _)=(if chamber S G ∘ (i∘s)=w ∘ s then _ else _)
    by_cases he:chamber S G ∘ i=w
    · rw [if_pos he,if_pos]; exact (h i s).symm
      change (chamber S G ∘ i) ∘ s=w ∘ s; rw [he]
    rw [if_neg he,if_neg]; exact fun h=> he (funext fun k=>by have hv:=congr_fun h (s.symm k); simp only [Function.comp_apply,s.apply_symm_apply] at hv ⊢; exact hv)
end YM.FormalBulk08.Rial
