import YM.RegulatorIR.Binding.Lands
import YM.RegulatorIR.Binding.Scenes

/-! Pack the same representation and its readout at all finite scales.
No differentiation of mask costs. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.Field Geometry.End Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Tree Series Series.Radial Series.Tested
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{I J E L:Type}[Fintype I][Fintype J][Fintype E][Fintype L]{U A:Hook G E I}
lemma lit_tilt (H:Bundle U A) (t:ℝ): Measurable (fun p:RoomK G I × RoomK G E => tilt U A t p.1 p.2):=by
 let f:= fun p:RoomK G I × RoomK G E=>(t,p)
 have h:Measurable f:= measurable_const.prodMk measurable_id
 have hp:Measurable fun p:RoomK G I × RoomK G E=> Real.exp (-U t p.1 p.2 /t^2):= ((((H.burden.comp h).neg).div_const _).exp)
 exact (H.cased.measurable.comp h).mul hp
lemma scan_reads (H:Bundle U A) (t:ℝ): Measurable (scan U A t):= ((lit_tilt H t).stronglyMeasurable.integral_prod_right' (ν:=physical G E)).measurable
lemma scan_mass (H:Bundle U A) (t:ℝ): Integrable (scan U A t) (physical G I):=by
 obtain ⟨C,hC⟩:= H.major t
 apply Integrable.integral_prod_left (f:=fun p:RoomK G I × RoomK G E=> tilt U A t p.1 p.2) (Integrable.of_bound ((lit_tilt H t).aestronglyMeasurable) C (Eventually.of_forall fun p=>hC p.1 p.2))

def rightSum (F A:Hook G E I) (t:ℝ):= ∫ x, scan F A t x ∂physical G I

variable {f c:Side}
-- actual invariant functions

def Allowed (G:Gauge)(f:Side)(F:ℝ→Shape G f → ℝ) : Prop:=∀ k:Site f→G.El,compatible k → ∀ U t,F t (goat k U)=F t U
def Archive (G:Gauge)(f:Side)(P A:Hook G E (OEdge f)): Prop:= Allowed G f (scan P A)
variable (S:StepData c f) (k:Scale) {F:Forest S.ratio}{U A:Hook G E (OEdge f)}

def pushO (S: StepData c f) (k:Scale) (w:spins G f) (t:ℝ)(v:spins G c):= Real.exp (-(k.beta t / t^2)*bond S w v)
lemma pushedO (f:Wind F→ G.El) (t:ℝ) (V:Shape G c): tilt (nextO S F k) 1 t V f= pushO S k (cloth F f) t V:=by
 unfold tilt pushO nextO; rw [Pi.one_apply,Pi.one_apply,Pi.one_apply,one_mul]; apply congr_arg; ring

variable (H:S.patch.Branches S.kernel G)
include H
lemma pump (t:ℝ): Measurable (fun p:spins G f × spins G c=>pushO S k p.1 t p.2):= by
 have h : Measurable (fun p: spins G f × spins G c=> -(k.beta t/t^2) * bond S p.1 p.2):=(bond_meas S H).const_mul _
 exact h.exp
omit H in
lemma income (p:spins G f)(t:ℝ)(v:spins G c): ‖pushO S k p t v‖ ≤ 1:=by
 unfold pushO; rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (k.forward _) (sq_nonneg _))) (bond_nonneg ..))
lemma heightBound (B:Bundle U A) (t:ℝ)(p:spins G c): Integrable (fun q:spins G f=> scan U A t q * pushO S k q t p) (physical G (OEdge f)):=by
 have hi:= scan_mass B t
 refine hi.norm.mono' ?_ (Eventually.of_forall (fun q=>?_))
 · exact ( (scan_reads B t).mul ((pump S k H t).comp (measurable_id.prodMk (measurable_const (a:=p)))) ).aestronglyMeasurable
 rw [norm_mul];exact mul_le_of_le_one_right (norm_nonneg _) (income S k q t p)

variable (B:Stead (full G f) U) (T:Tune A) (P: Archive G f U A) (W:Square F)(hc:Even c.val)(hf:Even f.val)
include B T P W hc hf
lemma promoted (t:ℝ)(y) : scan (fuse (dropQ S F G) U (nextO S F k)) (blade _ (dropQ S F G) A) t y=
     ∫ x: spins G f, scan U A t x*pushO S k x t y ∂physical G _:=by
 rw [puzzling B (cross k S H W hc hf) T]
 symm; simp_rw [pushedO]; refine orchard _ (heightBound S k H (B.allows T) t y) W hf (fun v hv hg w=>?_)
 rw [P v hv w t,pushO,show bond S (goat v w) y=bond S w y from ?_]; rfl
 have ht:=bond_flow S H v hv w y;rw [show v∘ S.ratio.embed=1 from funext hg,goat_one] at ht;exact ht
lemma continues : Archive G c (fuse (dropQ S F G) U (nextO S F k)) (blade _ (dropQ S F G) A):=by
 intro v hv x t
 rw [promoted S k H B T P W hc hf,promoted S k H B T P W hc hf]
 let f:= fun i=> v (S.ratio.parent i)
 have ht:compatible f := lift_site W.odd hv
 have he:f ∘ S.ratio.embed=v :=funext fun a=> congr_arg v (Ratio.embed_parent _ _)
 have hz := (show MeasurePreserving (goatHom f) (physical G (OEdge _)) (physical G (OEdge _)) from perm_goat f).integral_comp' (fun y=>scan U A t y*pushO S k y t (goat v x))
 rw [← hz];apply integral_congr_ae;filter_upwards with y
 change scan U A t (goat f y)*_= _; rw [P f ht y t]; apply congr_arg (scan U A t y * ·); change Real.exp (_ * bond S (goat f y) _)= Real.exp _; rw [← he, bond_flow S H f ht y x]

lemma rung (t:ℝ): rightSum (fuse (dropQ S F G) U (nextO S F k)) (blade _ (dropQ S F G) A) t = rightSum U A t * (S.penaltyZ (k.beta t/t^2) G)^Fintype.card (OEdge c):=by
 unfold rightSum; simp_rw [promoted S k H B T P W hc hf]
 have ht y: (∫ x:spins G c,pushO S k y t x ∂physical G _)=(S.penaltyZ (k.beta t/t^2) G)^Fintype.card (OEdge c):= bond_mass S ..
 let p :=physical G (OEdge c); let d:=physical G (OEdge f)
 have hi:= scan_mass (B.allows T) t
 let b(x:spins G f):= ‖scan U A t x‖
 let F(g:spins G c × spins G f):= scan U A t g.2 * pushO S k g.2 t g.1
 have he:Integrable F ((physical G (OEdge c)).prod (physical G (OEdge _))):=by
    have hW: Integrable (fun g:spins G c × spins G f=> b g.2) ((physical G (OEdge c)).prod (physical G (OEdge _))):= hi.norm.comp_snd ..
    refine hW.mono' ?_ (Eventually.of_forall (fun v=>by unfold F; rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (income S k v.2 t v.1)))
    have hv: Measurable (fun p:spins G c × spins G f=>pushO S k p.2 t p.1):=(by change Measurable ((fun p:spins G f × spins G c=>pushO S k p.1 t p.2) ∘ Prod.swap); exact (pump S k H t).comp measurable_swap)
    exact Measurable.aestronglyMeasurable (((scan_reads (B.allows T) t).comp measurable_snd).mul hv)
 rw [← integral_prod F he, integral_prod_symm F he]; unfold F; simp_rw [integral_const_mul,ht, integral_mul_const]

end YM.RegulatorIR.Binding

namespace YM.RegulatorIR.Binding
open PertExtension Laplace Chart Lattice Geometry Geometry.Field Geometry.End Orb Gauge MeasureTheory Filter Function Set Metric Exterior Wilson RG Tree Series Series.Radial Series.Tested
open scoped ContDiff Topology NNReal ENNReal BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{f: Side}{I:Type}[Fintype I]{U A:Hook G I (OEdge f)}

abbrev tip (A: Hook G I (OEdge f)) := blade Empty (Last.shoot f G) A
def apogee (F: Hook G I (OEdge f)) : Hook G (I ⊕ Orb.Cotree f) Empty:= fuse (Last.shoot f G) F 0
lemma achieved (H:Stead (full G f) U) (C:Tune A)(he: Archive G f U A)(hp:Even f.val)(t:ℝ): scan (apogee U) (tip A) t 1=rightSum U A t:=by
 rw [apogee,tip,puzzling H (Last.carries hp) C]
 simp only [tilt,Pi.one_apply,Pi.zero_apply,neg_zero,zero_div,Real.exp_zero,mul_one]
 exact (End.finish (scan U A t) (scan_mass (H.allows C) t) hp fun k hv u=> he k hv u t).symm

-- read off rightSum
lemma wind (H:Stead (full G f) U)(C:Tune A)(he:Archive G f U A)(hp:Even f.val): Aspiration (fun t:ℝ=> (t ^ Laplace.dim G (I⊕ Orb.Cotree f))⁻¹ * rightSum U A t) (tomorrow (apogee U) (tip A) 0):= by
 have hh:Bundle (apogee U) (tip A):= (H.integrates (Last.carries hp)).allows (blade_c _ C)
 intro i; obtain ⟨c,hc,h⟩:= hh.beats 0 le_rfl i
 exact ⟨c,hc,h.mono fun t ht=>by
   change ‖_*rightSum U A t- _‖ ≤ _; rw [← achieved H C he hp]; apply le_trans (le_of_eq ?_) (ht 0 (by simp)); unfold normalized; rw [smul_zero,expOrigin]⟩
lemma head (P:Scale)(A:Hook G Empty (OEdge f))(t:ℝ)(x): scan (startO P) A t x= tilt (startO P) A t x 1:=by
 unfold scan;have he z: tilt (startO P) A t x z= tilt (startO P) A t x 1:=congr_arg _ (Subsingleton.elim ..);simp_rw [he]; simp
lemma allowed_top (P: Scale)(A:Hook G Empty (OEdge f))(h:Allowed G f (fun t u=> A t u 1)): Archive G f (startO P) A :=by
 intro k hk U t;rw [head,head,tilt,tilt, show A t (goat k U) 1=A t U 1 from h k hk U t]; unfold startO valueO; rw [goat_lift k _ hk,energy_gauge]
end YM.RegulatorIR.Binding
