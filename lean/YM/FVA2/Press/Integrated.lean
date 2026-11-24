import YM.FVA2.Press.Curl
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
/-!
# Integrate momentum plane polynomials along each link

`projection` goes to radial gauge; then the Survey sampler sees exactly this slot
with none of the lower ranks. Projected Taylor order an explicit inequality throughout. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press.Integration
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Native MS.Theater
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {k d:ℕ} {H:Hol G} (A:XSpace.Survey G H d)
local notation "E" => tilt A
local notation "V" => CoverConfig G
local notation "B" => GaugePanel G A.size
local notation "C" => G.Color
local notation "X" => Edge Cover
local notation "L" => Work.G03.castPos
private def field (u:Feet G k)(l:X)(t:ℝ):= Tensor.diagonal (u.val l.2) (L l.1+t • basis l.2)
def integration (G:Gauge)(k:ℕ) : Feet G k →ₗ[ℝ] (Edge Cover → G.Color) where
 toFun u l:= ∫ t:ℝ in 0..1, field u l t
 map_add' p q:= funext fun l=> by
    have h (p:Feet G k): IntervalIntegrable (field p l) volume 0 1:= ((Tensor.diag_smooth _ ω).continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable ..
    exact intervalIntegral.integral_add (h p) (h q)
 map_smul' r p:= funext fun l=> intervalIntegral.integral_smul r (f:=field p l)
lemma unitCell (x:Head G (k+1))(l:X) : integration G k (gradS G k x) l= Tensor.diagonal (x.val ()) (L (l.1+step l.2))-Tensor.diagonal (x.val ()) (L l.1):= by
 let y:=L l.1; let i:=l.2; let f:=Tensor.diagonal (x.val ()); let u(t:ℝ):= y+t • basis i; let p:=f ∘ u
 have he(t:ℝ): field (gradS G k x) l t=fderiv ℝ f (u t) (basis i):= congr_fun (workL (i:= ()) (basis i) x) (u t)
 have hz(t:ℝ): HasDerivAt p (fderiv ℝ f (u t) (basis i)) t:= ( (Tensor.diag_smooth (x.val ()) ω).differentiable (by simp) (u t)).hasFDerivAt.comp_hasDerivAt (f:=u) t (by unfold u; simpa using! HasDerivAt.const_add y ((hasDerivAt_id' t).smul_const (basis i)))
 rw [show integration G _ _ l= p 1-p 0 from intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=> by rw [he]; exact hz t ) (Continuous.intervalIntegrable (show Continuous (field (gradS G k x) l) from (Tensor.diag_smooth _ ω).continuous.comp (continuous_const.add (continuous_id.smul continuous_const))) ..), Work.G03.castPos_step]; unfold p u; simp; rfl -- syntax

/-- Specialize one radial degree. -/
def oneSnap (v:Labels.Taylor G k)(h:k<d-1): Snap G d:= Pi.single ⟨k,h⟩ v
lemma snaps_eq (v:Labels.Taylor G k)(h:k<d-1) : expand d (oneSnap v h) k=v:= by rw [expand, dif_pos h, oneSnap, Pi.single_eq_same]
lemma snaps_off (v:Labels.Taylor G k)(h:k<d-1) (u)(H:u≠k) : expand d (oneSnap v h) u=0:= by
 unfold expand oneSnap; split
 next h' => exact Pi.single_eq_of_ne (Fin.ne_of_val_ne H) _
 next=> rfl
lemma accessing (v:Labels.Taylor G k)(h:k<d-1) : access (oneSnap v h) = integration G (k+1) (step_in G k v):= by
    funext ⟨x,i⟩; rw [Work.G03.edge_sum, Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr h),snaps_eq];
    · rfl
    intro b _ h'; rw [snaps_off _ _ _ h', Work.G03.edgeInt]; simp [Labels.Taylor.value,Tensor.diagonal]
def collect (A:XSpace.Survey G H d)(k:ℕ) : Feet G k →ₗ[ℝ] Snap G d := A.extract.toLinearMap ∘ₗ (fderiv ℝ (lamp A) 0).toLinearMap ∘ₗ coord A ∘ₗ integration G k
lemma collect_blank (x:Head G (k+1)): collect A k (gradS G k x)=0:= by
    unfold collect; simp only [LinearMap.comp_apply]; rw [show integration G k (gradS G k x)=_ from funext (unitCell x)]; exact gauge_d A (fun l=>Tensor.diagonal _ (L l)) -- fst x
lemma collect_one (v:Labels.Taylor G k)(h:k<d-1): collect A (k+1) (step_in G k v)= oneSnap v h:= by
    unfold collect; simp only [LinearMap.comp_apply]; rw [← accessing v h]; exact project_d ..
lemma project_eq (x:Feet G k) : collect A k x=collect A k (carve G k x):= by rw [carveΩ,map_sub,map_smul,collect_blank,smul_zero,sub_zero]
lemma constant (x:Feet G 0): collect A 0 x=0:= by rw [project_eq A x, show carve G 0 x=0 from ?_,map_zero]; apply (Submodule.mem_bot ℝ).mp; rw [← weightT G]; exact house x
lemma projection (x:Feet G (k+1))(h:k<d-1): collect A (k+1) x= oneSnap (yard G k x) h:= by rw [project_eq, ← taxiY,collect_one A _ h]
-- coordinate view on the real sensor, before evaluating Fourier amplitudes
variable (i: Labels.Key G)
def channel (i:Labels.Key G): Snap G d→L[ℝ] ℝ:= Complex.reCLM ∘L Work.G05.snapCoord d i
def box (i:Labels.Key G)(x: tilt A) := channel i (A.recover (lamp A x))
lemma channel_eq (p:Snap G d) : Labels.coord (expand d p) i=(channel i p:ℂ):= (Work.G05.snapCoord_eq ..).symm -- #check
lemma hot : ContDiff ℝ ω (box A i):= ((channel (d:=d) i).contDiff (𝕜:=ℝ) («E»:=Snap G d)).comp (A.recover_smooth.comp (lamp_smooth A))
lemma box0 : box A i 0=0:= by rw [box,lamp0, A.recover_zero,map_zero]
lemma box_der (x:Feet G k) : fderiv ℝ (box A i) 0 (coord A (integration G k x))= channel i (collect A k x):= by
 let P:= A.recover; let D:E→L[ℝ] B:= fderiv ℝ (lamp A) 0
 have h:DifferentiableAt ℝ P (lamp A 0):= A.recover_smooth.differentiable (by simp) (lamp A 0); have hv:P ∘ lamp A = (fun x=>P (lamp A x)):=rfl; let K:= channel (d:=d) i
 change fderiv ℝ (K ∘ P ∘ lamp A) 0 _=_
 rw [fderiv_comp (g:=⇑K) _ (K.differentiableAt («E»:=Snap G d)) (h.comp _ ((lamp_smooth A).differentiable (by simp) 0)),fderiv_comp (g:=P) _ h ((lamp_smooth A).differentiable (by simp) 0),K.fderiv,lamp0]; rfl
end YM.FVA2.Press.Integration
