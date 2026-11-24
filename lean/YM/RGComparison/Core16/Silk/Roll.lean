import YM.RGComparison.Core16.Silk.Loom
import YM.Next.FOUNDATIONS.Primary
/-!
# Rail moments from §Fk. (On actual conditional step.)
Test unconditional real boundary covariance at the TRUE height schedule. Comparison here on
full **conditional** at given Planet g, all admissible outputs and any rotations.
No WeakCoupling analytic assertion needed. Coefficients by `Fk`.read; exact version
of the hierarchy of PT conditional moments BEFORE address pricing, support
transport and mask operations. Eventually supply `ℒ` along seam and other profit budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial
open Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D I : Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D]

abbrev chart (G : Gauge) := Next.Foundations.chart G

variable {X:Shelf G A D} (P:Planet X S ι k T)
-- tag-aware lift from `G.curvature` frame to template. Color indices for wiring fixed
-- orientation of Kin chart. Canonical ambient geometry period f (fine).
def sway (w:Rail G ι) : Cost:= fun g=> P.expect g (sing w g)

def swatch (w:Rail G ι) : Stuff G ι (Fin w.length):= fun i=>.inl (w[i]).1

def weft (w:Rail G ι)(u:Fin w.length→G.Color): ℝ:=∏ j,u j (w[j]).2

def warp (w:Rail G ι)(_:ℝ)(x:Sky G ι):= ∏ j:Fin w.length, curve x w[j]

def price (w:Rail G ι):Roll:= PowerSeries.mk (Fk.read P (chart G) (swatch w) (weft w) w.length)

variable (w:Rail G ι)

omit [Fintype ι] in
lemma swatch_word (u:Sky G ι)(j:Fin w.length)(g:ℝ)(hg:0<g) : (g • book (swatch w) g u) j= G.curvature (u (w[j]).1):= smul_inv_smul₀ hg.ne' _
omit [Fintype ι] in
lemma warp_cont (g:ℝ): Continuous (warp w g):= continuous_finsetProd _ fun j hj=> by unfold curve; fun_prop
omit [Fintype A] [Fintype D] in
lemma tags : Visible X (weft w) (warp w) (swatch w) (w.length) (2^w.length) := by
   refine ⟨fun g _=>havenreal (warp_cont w g),fun g _ x=>?_,bundle w,bundle_cap _,fun i=>mem_univ_resp i,fun g _ hg x _=>?_⟩ -- auxiliary
   · unfold warp; rw [abs_prod]; refine (prod_le_prod (g:=fun _=>2) (fun _ _=> abs_nonneg _) (fun i _=> show |curve x w[i]| ≤ 2 from (mono_cone _ _).trans ((G.curvature_norm ..).trans (G.chord_le_two ..)))).trans ?_; simp only [Finset.prod_const,card_univ,Fintype.card_fin]; exact le_rfl
   · unfold warp weft; simp_rw [swatch_word (ι:=ι) w x _ g hg]; rfl
where
  mem_univ_resp (i:Fin w.length) : (w[i]).1∈bundle w := List.mem_toFinset.mpr (List.mem_map_of_mem (f:=Prod.fst) (List.getElem_mem ..))

omit [Fintype ι] in
lemma homogeneous (u:Fin w.length→ G.Color)(r:ℝ): weft w (r • u)= r^w.length*weft w u:= by unfold weft; simp [Finset.prod_mul_distrib]
omit [Fintype ι] in
lemma knitted : ContDiff ℝ ω (weft w):= contDiff_prod (t:=univ) (f:=fun i : Fin w.length => fun v:Fin w.length→G.Color=> v i (w[i]).2) fun i hi=>
      (EuclideanSpace.proj (w[i]).2:G.Color→L[ℝ] ℝ).contDiff.comp (f:=fun v :Fin w.length→G.Color=>v i) (contDiff_apply ℝ _ _)
omit [Fintype ι] in
lemma stiches : Zeros w.length (weft w):= by
   refine fun j hj=> Tested.jets_vanish ((knitted w).contDiffAt.of_le le_top) (fun v=> ?_) hj
   unfold Tested.Bill; simp_rw [homogeneous]; refine ⟨|weft w v|, abs_nonneg _, Tested.eventually_pos.mono (fun i hi=> ?_)⟩
   rw [norm_mul,Real.norm_of_nonneg (pow_nonneg hi.le _)]; exact le_of_eq (mul_comm ..)

omit [Fintype ι] in
lemma sing_roll (g:ℝ)(x:Sky G ι) : sing w g x=g⁻¹^w.length*warp w g x:= by
    induction w with
    | nil=> simp [sing,warp]
    | cons i w h=>
       rw [sing_cons,h]; unfold warp; simp only [List.length_cons]; rw [Fin.prod_univ_succ]
       change tally g i x * (g⁻¹ ^ w.length * ∏ j:Fin w.length, curve x w[j]) = g⁻¹^(w.length+1)*(curve x i * ∏ j:Fin w.length, curve x w[j])
       unfold tally; rw [div_eq_mul_inv,pow_succ']; ring

variable {P}(H:P.Steady)
include H
lemma supplies : train (sway P w) (price P w):= by
   apply train.sand; unfold sway; have hf (g:ℝ): sing w g=g⁻¹^w.length • warp w g:= funext (sing_roll w g); simp_rw [hf,Planet.expect_mul]
   exact Fk.exterior H (Next.Foundations.chart_ok G) (tags w) (stiches w) (knitted w|>.contDiffAt)


lemma zero_part : price P [] = 1:= by
    apply (supplies [] H).unique
    rw [←map_one (PowerSeries.C (R:=ℝ))]; apply (train.cash 1).travel; filter_upwards [Fk.tollLess (willing H.prices)] with g hg
    exact (burden H hg 1).symm
omit H

-- coefficient budgets read after log pricebook. Uniform in arbitrary admitted shape,
-- period, Gate STEP after aperture. Negative powers for pointer curvature already credited.
lemma uniform (B:Lumen.Stage)(Y:Good X)(r d:ℕ): ∃ (U:Lumen.Stage)(v:ℝ), U.Above B ∧ Visit U X ∧ 0≤v ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(S:Side)(P:Planet X S ι k T), P.Steady→ ∀ w:Rail G ι, w.length ≤ d→ Fk.Allots U (term (price P w)) r v (sway P w):=by
    obtain ⟨T,t,ht,h,h',he⟩:= assemble Y (r+2) d B
    obtain ⟨V,hV,hK⟩:= Fk.date_purchase T
    exact ⟨V,2*t,above_trans h hV,newer h' hV,by positivity,fun _ _ _ _ _ _ S P H u hu=> (supplies u H).money hV hK (he _ _ _ _ _ _ S P H u hu)⟩

lemma issued (Y:Good X)(r d:ℕ): ∃ v:ℝ, 0≤v ∧ ∀ (ι k T:Type)(_:Fintype ι)(_:Fintype k)(_:Fintype T)(S:Side)(P:Planet X S ι k T), P.Steady→ ∀ w:Rail G ι,w.length≤d→∀ i≤r,|nth i (price P w)|≤v:=by
    obtain ⟨_,v,_,_,hv,h⟩:=uniform ⟨1,0,le_rfl⟩ Y r d; exact ⟨v,hv,fun _ _ _ _ _ _ S P H u hu=> (h _ _ _ _ _ _ S P H u hu).front⟩

end YM.RGComparison.Core16.Silk
