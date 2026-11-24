import YM.X.Sage.Trail
/-!
# λ beam extensions for 2pt-UU guide. no need continuum singular estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Sage
open Lattice Wilson Next.Rank Normal LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Function Reed Ocean Hinge Haze Fielding Print Tri Plate Gravity Chir Fund Imprint
open Stems hiding X
open MeasureTheory Bare MvPolynomial Set Pulse Pert Pert.Position Pert.RawLabels Labels Maxwell.Free
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {m d k:ℕ} {V I:Type*} {q:ℕ+} {r R:ℝ}
local notation "τ"=>(atTop:Filter ℕ)
local notation "E"=>Pert.Position.E F d
local notation "ε"=> epsilon q k
local notation "o"=> side q k
variable (S:Bare.Shop F)(v:Fin m → Pert.Position.E F d)(hq:1<q.val)(t: Test m) (a:Beam q)
lemma part_cost (X: Fin m →Fielding.Walk) : postZ S v X q a k= Hinge.shock (flow G o) (∏ i:Fin m, dress (X i k) (held S ε⁻¹ d 0 (physicalLabel F d (v i)))):= by
    unfold postZ; rw [coins_view,hours,chapter_val,one_mul]; simp_rw [sales,LinearMap.comp_apply]; rw [Fund.loc («o»:=a k),map_prod (hairAt (a k))]; simp_rw [Fund.tint]; rfl
abbrev meow (S:Bare.Shop F)(q:ℕ+)(d:ℕ)(v:Pert.Position.E F d): Foam G:= stance S q d (physicalLabel F d v)
local notation "T"=> meow S q d
lemma meows (x:Fielding.Walk)(v:Pert.Position.E F d): milk (flow G o) (dress (x k) (held S ε⁻¹ d 0 (physicalLabel F d v)))=dress (x k) (T v k) := milked ..
lemma two_E (v:Fin 2→E)(X:Fin 2→Fielding.Walk)(Z:Fielding.Walk) : postZ S v X q a k= gather q Z (X 0) (X 1) 1 (T (v 0)) (T (v 1)) k:= by
    unfold Tot.gather; rw [part_cost, Fin.prod_univ_two]; nth_rw 1 [← one_mul (dress _ _ * _)]; rw [triple_fate,meows,meows]; simp only [Pi.one_apply,map_one,Next.Rank.Normal.pure]
lemma one_E (v:Fin 1→ E)(X:Fin 1→Fielding.Walk)(Z Y:Fielding.Walk): postZ S v X q a k=gather q Z (X 0) Y 1 (T (v 0)) 1 k:= by
   unfold Tot.gather; rw [part_cost,Fin.prod_univ_one]; nth_rw 1 [← mul_one (dress _ _)]; nth_rw 1 [← one_mul ((dress _ _)*1)]; rw [triple_fate,meows]; simp only [Pi.one_apply,map_one,pure]
variable (H:4≤d)
local notation "D"=> dean F H
local notation "P"=> μDeck q G
lemma popu : meow S q d D=stance S q d (UW G H):= by unfold meow; rw [dean_c]
local notation "Θ"=> Reed.Horizontal G
include hq
lemma pantry : T D-P∈ Ash q Θ:= popu S H▸ feelU hq S H -- orientation
omit hq
lemma extra (x y:E4):∃ z:E4,z≠x∧z≠y:= by obtain ⟨a,ha⟩:= Infinite.exists_notMem_finset ({x,y}:Finset E4); use a; simpa using ha
lemma kinder (X Y:Fielding.Walk)(x y:E4)(hx:plot q X x)(hy:plot q Y y)(hp:x≠y)(hq:1<q.val):∃r:ℝ,r>0 ∧∃ Z, Geom q r Z X Y:= by
    obtain ⟨z,hx',hy'⟩:= extra x y; let Z:= fun k:ℕ=>Haze.index (epsilon q k) z; have hz:plot q Z z:= entrant hq z; obtain ⟨r,u,h1,h2,h3⟩:= ((show ∀ᶠ r:ℝ in 𝓝[>] 0,(0:ℝ)<r from self_mem_nhdsWithin).and ((geo_live hq hx' hz hx).and ((geo_live hq hp hx hy).and (geo_live hq hy'.symm hy hz)))).exists
    exact ⟨r,u,Z,h1,h2,h3⟩
include hq
local notation "L"=> Plate.Apt
set_option maxHeartbeats 420000 in
lemma double_u : Guide S q (m:=2) (fun _=> D):= by
   intro x hx X hX a; obtain ⟨r,hr,Z,h⟩:= kinder (X 0) (X 1) (x 0) (x 1) (hX _) (hX _) ((show Injective x.ofLp from hx).ne (by decide)) hq
   have hb: postZ S (fun _=> D) X q a=gather q Z (X 0) (X 1) 1 (T D) (T D):= funext fun i=> two_E (k:=i) S a (fun _=> D) X Z; rw [hb]; obtain ⟨χ⟩:= Floor.make (R:=r/2) (by linarith)
   exact CostF.sterile ((replace_fields (p:=1) q Z (X 0) (X 1) h hr hq Plate.Apt.base (pantry S hq H) (pantry S hq H) (single_ready degreeU) (stan_h S hq _)).trans (CostF.zero (arrest _ _ _ χ h (by linarith) hq Plate.Apt.base (fun _=>Plate.duty.one))))
-- one-point µDeck projection
omit hq
lemma mono_μ (X Y Z:Fielding.Walk) : gather q X Y Z 1 P 1=0:= by ext1 i; unfold Tot.gather; simp only [Pi.one_apply, map_one,snapμ]; rw [tri_S]; simp_rw [tri_sum,tri_cross,Derivation.map_one_eq_zero]; simp
lemma one_ready : (1:Foam G)∈Ready q Θ:= by rw [← Tot.empty («T»:=Θ) (q:=q)]; exact page_all []
include hq
set_option maxHeartbeats 420000 in
lemma single_u : Guide S q (m:=1) (fun _=>D):= by
    intro x hx X hX a; obtain ⟨y,hy,_⟩:= extra (x 0) (x 0); let Y:=fun i:ℕ=> Haze.index (epsilon q i) y; have he:plot q Y y:=entrant hq ..; obtain ⟨r,hr,Z,h⟩:=kinder (X 0) Y (x 0) y (hX _) he (Ne.symm hy) hq
    have hz: postZ S (m:=1) (fun _=>D) X q a=gather q Z (X 0) Y 1 (T D) 1:= funext fun k=> one_E (k:=k) S a (fun _=>D) X Z Y; rw [hz]; apply CostF.sterile; rw [← mono_μ (G:=G) (q:=q) Z (X 0) Y]; exact replace_fields (p:=1) q _ _ _ h hr hq Plate.Apt.base (pantry S hq H) (show (1:Foam G)-1∈ Ash q Θ from by rw [sub_self]; exact Submodule.zero_mem _) (single_ready degreeU) one_ready
end YM.PositionX.Sage
