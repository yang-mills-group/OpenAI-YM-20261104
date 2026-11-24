import YM.Qlocal.Quipu.Ballad
import YM.Qlocal.Quipu.Poem
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
-- witness gauge.Flow limit plus at any fixed position all short canonical slip entries. Costs next. gauge U(t) definition fixes spelling uppercase. Use engine `rule` with `exteriorL`. no unit dilations hidden.St.V.
local notation "S"=> Coarse G
local notation "Ω"=> rule (Coarse G) n
local notation "X"=> fieldDir G n 1
noncomputable abbrev ports (G:Gauge)(n:Side) : rule (Coarse G) n ≃L[ℝ] fieldDir G n 1:= (exteriorL G n).trans (tint G _)
local notation "M"=> ports G n
variable (U:Config G n)(o:Lattice.Order)(p:Site n)(v w:Cover)
protected def nearby (h:Site n)(p:Site n) := Lattice.lift (h-p)
local notation "Φ"=> Incline.nearby
lemma wiz {v:Cover}(h:2*size v<n.val): Incline.nearby (bent p v) p=v:= by
 unfold Incline.nearby bent; rw [add_sub_cancel_right]; apply lift_eq_iff.mpr; refine ⟨rfl,fun i=>?_⟩; have hv : (v i).natAbs≤ size v:= Finset.single_le_sum (f:=fun i=>(v i).natAbs) (fun i _=> Nat.zero_le _) (mem_univ i); omega
lemma base (q:Site n): wrap n (Incline.nearby q p)+p=q:= by unfold Incline.nearby; rw [wrap_lift,sub_add_cancel]
lemma way (q:Site n): size (Incline.nearby q p) ≤ 4*n.val:= by
 unfold Incline.nearby size; apply le_trans (b:=∑ _ : Axis, n.val) (Finset.sum_le_sum (fun i _=>?_)); · simp -- ordering?
 have he:= lift_centers (q-p) i; omega
protected def loom (o:Lattice.Order) (p q: Site n) := route 0 (Incline.nearby q p) o
local notation "L"=> Incline.loom o p -- avoid ambiguous
lemma extraordinarily (q:Site n): (Incline.loom o p q).length ≤ 4*n.val:= by unfold Incline.loom; rw [Stationary.route_length,sub_zero]; exact way p q
-- transport U global and all μ
variable (χ:G.El)
noncomputable def flow (U:Config G n) (o:Lattice.Order) (p:Site n)(u:G.El)(q:Site n): G.El:= u * travel U p (Incline.loom o p q)
noncomputable def gloss := Lattice.gauge (flow U o p χ) U
-- lemma trail link through flow.Short.Ph.
lemma joins (u:Cover)(i:Axis)(hu:2*(size u +1)<n.val) : gloss U o p χ (bent p u,i)= χ*travel U p (trail o u i)*χ⁻¹:= by
 let b':=u+step i; let v₁:=bent p u; let v₂:=bent p b'
 have hx: v₁+step i=v₂:= by unfold v₁ v₂ bent b'; rw [map_add,wrap_step]; abel
 have hv₁: Incline.nearby (bent p u) p=u:= wiz p (by omega)
 have hv₂: Incline.nearby v₂ p=b':= wiz p (by have he:(size b') ≤ size u+1 := (size_add ..).trans_eq (by simp [size,Lattice.step,Pi.single_apply,apply_ite Int.natAbs]); omega)
 unfold gloss Lattice.gauge flow Incline.loom; erw [show bent p u+_= _ from hx, hv₁,hv₂]; rw [show travel U p (trail o u i)= travel (expandAt p U) 0 (trail o u i) from ?_,carry]; swap; · rw [travel_at,map_zero,zero_add]
 simp_rw [travel_at,map_zero,zero_add]; change (χ*travel U p (route 0 u o))*U _*(χ*travel U p (route 0 b' o))⁻¹=χ*(travel U p (route 0 u o)*U (v₁,i)*(travel U p (route 0 b' o))⁻¹)*χ⁻¹; group; rfl
variable (x:rule (Coarse G) n)
noncomputable abbrev passing (x:rule (Coarse G) n)(t:ℝ):Config G n:= represent (t•ports G n x)
local notation "W"=> passing x
noncomputable abbrev breeze (t:ℝ)(q:Site n):= flow (passing x t) o p χ q
noncomputable abbrev blade (t:ℝ): Config G n:= gloss (passing x t) o p χ
local notation "Q'"=> blade o p χ x
noncomputable abbrev pulled (t:ℝ): rule (Coarse G) n:= ((M).symm (CubicMatch.logged ((Q') t)))
noncomputable abbrev lifts := Laplace.SigmaP.shift (pulled o p χ x) -- match ns
local notation "Ω'"=> lifts o p χ x
lemma coolest(s:Walk) : travel (1:Config G n) p s=1:= by induction s generalizing p <;> simp_all [travel,Lattice.Step.read] -- `W` notation conflict
lemma blank_here : W 0=(1:Config G n):= by rw [passing, zero_smul,link_one]
lemma peace(q:Site n) : breeze o p χ x 0 q=χ:= by rw [breeze, blank_here, flow, coolest (G:=G),mul_one]
lemma bornQ : blade o p χ x 0=1:= by
 ext1 i; rw [blade]; unfold gloss; simp only [Lattice.gauge]; rw [show flow _ o p χ i.1=χ from peace ..,show flow _ o p χ _=χ from peace o p χ x (i.1+step i.2),blank_here]; simp
lemma three_happy : Weather (passing x) 0:= fun i=> ((Work.F03.represent_smooth i).contDiffAt.comp (f:=fun t:ℝ=> t• ((M) x)) _ (by fun_prop)) -- Weather namespace? inspect
lemma mellow(q:Site n)(w: Walk) : ContDiffAt ℝ ω (fun t:ℝ=> G.mat (travel (passing x t) q w)) 0 := Joint.Smooth.travel (three_happy x) q w
lemma gentle(q:Site n) : ContDiffAt ℝ ω (fun t:ℝ=> G.mat (breeze o p χ x t q)) 0:= by
 simp_rw [breeze,flow,G.mat_mul]; exact contDiffAt_const.mul (mellow x p (Incline.loom o p q)) -- q actually p
lemma planeQ : Weather (blade o p χ x) 0:= fun i=> gauged_smooth (u:=fun t:ℝ=> t•(M x)) (by fun_prop) (gentle o p χ x) i -- 
local notation "φ"=> Comparison.RG02.Laplace.along
local notation "F"=> Comparison.RG02.Symmetry.Flow
lemma necessary : ContDiffAt ℝ ω (pulled o p χ x) 0:= (ports G n).symm.contDiff.contDiffAt.comp _ (logged_smooth (bornQ o p χ x) (planeQ o p χ x))
lemma necessary_shift : ContDiffAt ℝ ω (lifts o p χ x) 0:= shifty (necessary o p χ x)
lemma incline_blank : pulled o p χ x 0=0:= by unfold pulled; rw [bornQ,CubicMatch.logged_zero, map_zero]
lemma rhythm (t:ℝ): t • lifts o p χ x t= (ports G n).symm (logged (Q' t)):= (shift_start (incline_blank o p χ x) t).symm
lemma expedition : Comparison.RG02.Symmetry.Flow ((ports G n) ∘ lifts o p χ x) (fun _=> (ports G n) x):=by
 let B0:= breeze o p χ x; have ht (q:Site n): Tendsto (fun t:ℝ=> B0 t q) (𝓝 0) (𝓝 χ):= (peace o p χ x q) ▸ (Smooth.tendsto (Q:=fun t=>B0 t q) (gentle o p χ x q)); -- ambiguity cast
 refine ⟨χ,breeze o p χ x, (tendsto_pi_nhds.mpr ht).mono_left nhdsWithin_le_nhds,?_⟩
 filter_upwards [(read_logged (bornQ o p χ x) (planeQ o p χ x)).filter_mono (show φ≤𝓝 0 from nhdsWithin_le_nhds)] with t hx; unfold Comparison.RG02.Integral.sample; rw [Function.comp_apply,← map_smul,rhythm,ContinuousLinearEquiv.apply_symm_apply, hx]; rfl
end Incline
end YM.Qlocal.Quipu.Eluder
