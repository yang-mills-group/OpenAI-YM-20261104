import YM.MS.Wind.Lapid
/-!
# Volterra desk preservation on polynomial scales

For LPT small-t and large t ✓. Choice linear operation on all Flow kernels
 but none of theorem statements will mention evaluation on a non-smooth input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind
open Function Filter Set Finset Plane Koszul Flux MeasureTheory
open Landau Native Lattice Tone Momentum Heat Real Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{F H:Flow G}{P Q:Pack G}{b:Bool}{u v r:ℤ}{t:ℝ}
lemma tune_interval (h:TouchF F)(r:ℝ) (l: List (Lane4 G)): IntervalIntegrable (fun s:ℝ=>F s l) volume 0 r:= ((h.at_const (id:ℝ→ℝ) l contDiff_id).continuous).intervalIntegrable ..
def coast (F:Flow G): Flow G:= fun i l=> ∫ s in 0..i, F s l
lemma coast_l : ∃ U : Flow G→ₗ[ℂ] Flow G,∀ F,TouchF F→ U F=coast F:= by
   let X:Submodule ℂ (Flow G):={
       carrier:=setOf TouchF
       zero_mem':=TouchF.zeros
       add_mem' {_ _} H H':= TouchF.add H H'
       smul_mem' c _ H:= TouchF.scale c H }
   let L : X →ₗ[ℂ] Flow G := {
       toFun F:= coast F.val
       map_add' F H:= by ext i l; exact intervalIntegral.integral_add (tune_interval F.property i l) (tune_interval H.property i l)
       map_smul' c F:= by ext; exact intervalIntegral.integral_const_mul .. }
   obtain ⟨T,H⟩:= Submodule.exists_isCompl X; refine ⟨L.comp (X.projectionOnto T H),fun F h=>?_⟩; let u:X :=⟨F,h⟩; change L (X.projectionOnto T H u.val)=_; rw [Submodule.projectionOnto_apply_left]; rfl

def tonic (G:Gauge) : Flow G →ₗ[ℂ] Flow G:= (coast_l).choose
lemma tonic_at (h:TouchF F): tonic G F=coast F:= coast_l.choose_spec F h
-- stationary symmetry. Use interval subtype rolled integrability. Includes negative r with signed subtraction.

lemma bone_C (h:Bon b u F): Bon b u (coast F) where
   joint:= deskLift h.joint
   sym t := by intro l i j r; unfold coast; simp_rw [h.sym _ l i j r, intervalIntegral.integral_const_mul]
   perk t := by intro l r i p q; unfold coast; simp_rw [h.perk _ l r i p q,intervalIntegral.integral_const_mul]
   real t:= by intro l; unfold coast; simp_rw [h.real _ l]; rw [intervalIntegral,intervalIntegral,star_sub]; congr! 1 <;> exact integral_conj
   pulse t:= by intro l hl; unfold coast; simp_rw [h.pulse _ l hl]; simp
   t_color t f:= by
       let μ1 : Measure ℝ:= volume.restrict (Set.Ioc 0 t); let μ2: Measure ℝ:= volume.restrict (Set.Ioc t 0)
       have he : coast F t=(fun l=> ∫ s,F s l ∂μ1)-(fun l=>∫ s,F s l ∂μ2):=rfl
       rw [he,map_sub]; congr 1; · ext; rw [rep_integral]; simp_rw [h.t_color _ f]; intro i; exact (tune_interval h.joint t i).1
       ext; rw [rep_integral]; simp_rw [h.t_color _ f]; intro i; exact (tune_interval h.joint t i).2
   stand t u':= by intro s w hw; simp_rw [coast,← intervalIntegral.integral_const_mul]; simp_rw [h.stand _ u' s w hw]
lemma desk_max (he:Rank F r): Rank (coast F) r:= by intro t l hl; unfold coast; simp_rw [he _ l hl]; simp
lemma tonicPack (h:Fees b u P): Fees b u (fun x=> tonic G (P x)) where
   stay x:= by rw [tonic_at (h.stay x|>.joint)]; exact bone_C (h.stay x)
   pay:= by obtain ⟨v,hv⟩:=h.pay; exact ⟨v,fun x=> by rw [tonic_at (h.stay x|>.joint)]; exact desk_max (hv x)⟩
   currency:= h.currency.linear ((tonic G).restrictScalars ℝ)
end YM.MS.Wind
