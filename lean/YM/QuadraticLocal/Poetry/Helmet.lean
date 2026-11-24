import YM.QuadraticLocal.Poetry.Mirage
import YM.QuadraticLocal.Sunrise.Loan
/-!
# Preparing trajectory of all *later orders* when analytic output is a Lantern

Account for completion order at every horizon and relative to ♦Λ; no hiding potential powers at
 g=0. Uses unmasked root gauge curvature for all admissible (even small) periods.P.SeamAlias.
 Real capture will stage at actual rotations. Here must align exactly with frame.Now.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Stationary
open Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type}[Fintype M][Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M) {a C D b:ℝ} {n m:Side}{k d N:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
namespace Helmet
-- two shells. complete before.C. generalized from Work.F03's degree-2 `taylor_limit_two`.
theorem germ {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](f:Y→ℝ)(T:GradeAt k f)(x:Y) : Tendsto (fun t:ℝ=> f (t • x) / t^k) (𝓝[≠] 0) (𝓝 (Radial.jet f k x)):= by
 let u:= ContinuousLinearMap.toSpanSingleton ℝ x; let g:= (f ∘ u); have he := T.coarse (f:=f) (g:=u) u.contDiff.contDiffAt u.map_zero -- use
 obtain ⟨s, hs, hu⟩:= he.smooth.contDiffOn (m:= k) le_top (by simp); obtain ⟨r,hr,hr'⟩:= Metric.mem_nhds_iff.mp hs; let I := Metric.ball (0:ℝ) r; have h0 : 0∈ I:=Metric.mem_ball_self hr; have ht:= Real.taylor_tendsto (n:=k) (convex_ball (0:ℝ) r) h0 (hu.mono hr'); rw [nhdsWithin_eq_nhds.mpr (Metric.isOpen_ball.mem_nhds h0)] at ht
 have H(j:ℕ): iteratedDerivWithin j g I 0=iteratedDeriv j g 0:=iteratedDerivWithin_of_isOpen Metric.isOpen_ball h0; let P:= PositionX.Jet.someJ g k; have hp:P=Radial.jet f k x:= jet_entry (T.smooth.of_le le_top) _
 have hw (x:ℝ) : taylorWithinEval g k I 0 x = x^k*P := by
    rw [taylor_within_apply, Finset.sum_range_succ,Finset.sum_eq_zero]; rotate_left; · intro j hj; rw [H,iteratedDeriv,show iteratedFDeriv ℝ j g 0=0 from he.vanish j (Finset.mem_range.mp hj)]; simp
    rw [zero_add,H]; unfold P PositionX.Jet.someJ; simp; ring
 rw [← hp]; let hP : Tendsto (fun t : ℝ=>(g t-t^k*P)/t^k+P) (𝓝[≠] 0) (𝓝 P):=by unfold g I at hw; simpa only [g, hw, sub_zero, zero_add] using (ht.mono_left (nhdsWithin_le_nhds (s:={0}ᶜ))).add_const P
 refine hP.congr' ?_; filter_upwards [show ∀ᶠ t:ℝ in 𝓝[≠] 0, t≠0 from self_mem_nhdsWithin] with t ht; change (_- _) /t^k+P=g t/t^k; field_simp; ring
-- projection.Real.n. Survives all ages and hyperplanes.
local notation "W"=> Link G n
variable (A:Atom G k)(x:Site n)(u:Stationary.Link G n)(t:rule M n)
def frame := fun v:Link G n=> A.unmasked (input G n v) x
lemma frameGrade : GradeAt k (Helmet.frame A x):= GradeAt.coarse («g»:=fun y:Link G n=> ((0:ℝ),arm G n 1 y)) (Loan.mature k A x) (contDiffAt_const.prodMk ((arm G n 1).contDiff.contDiffAt)) (by exact Prod.ext rfl (map_zero _))
lemma jet_price : Radial.jet (frame A x) k u=A.poly (fun i=> Work.F03.faceCurl (Work.F03.slotFace (A.leg i) x) (arm G n 1 u)):= by
    refine tendsto_nhds_unique (germ _ (frameGrade A x) u) ((Work.F03.atom_limit A x (arm G n 1 u)).congr ?_); intro v; unfold frame input; rw [map_smul]
end Helmet
namespace Lantern
open Picket Rovers
open PositionX.Jet
variable (p:Lantern G M)(x:Site n)(v:rule M n)(e:ℕ)(z: Stationary.Link G n)
-- driver mark encoder.Write of λ ratio where lives.DataΛ.Field import.E.I=carry step.M.Auth.A.
def gleam : ℕ→ Link G n →ℝ:= fun j=> if e≤j then Radial.jet (fun z:Link G n => p.light x (Stationary.input G n z) v) (j-e+p.r) else 0
local notation "G'"=> Lantern.gleam p x v e
lemma frame_cross (d:ℕ): Radial.jet (fun z:Link G n=> p.light x (input G n z) v) d= Ink.invoice x p.roots v • Radial.jet (Helmet.frame p.atom x) d:= Function.const _ (Function.const _ (by
 let t:=Ink.invoice x p.roots v; let f:= Helmet.frame p.atom x; rw [show (fun z:Link G n=> p.light x (input G n z) v)= t • f from funext fun z=> mul_comm (f z) t]; funext z; unfold Radial.jet; rw [iteratedFDeriv_const_smul_apply ((Helmet.frameGrade p.atom x|>.smooth).of_le le_top)]; simp only [_root_.smul_apply,smul_eq_mul,Pi.smul_apply]; ring -- order simp.Right
  ) (inferInstance : Fintype M)
  ) (inferInstance : DecidableEq M)
lemma pre {j:ℕ}(hh:j<e): (G' j)=0:= Function.const _ (Function.const _ (if_neg hh.not_ge
  ) (inferInstance : Fintype M)
  ) (inferInstance : DecidableEq M)
lemma placed (d:ℕ)(hh:e≤d): G' d z= Radial.jet (Helmet.frame p.atom x) (d-e+p.r) z * Ink.invoice x p.roots v:= by unfold gleam; rw [if_pos hh,frame_cross]; exact mul_comm ..
lemma height : p.frame x z v= G' e z:= by rw [placed p _ _ _ z _ le_rfl,Nat.sub_self,zero_add,Helmet.jet_price]; rfl
lemma tide {j:ℕ}:Plausible (G' j):= Function.const _ (Function.const _ (by
 unfold gleam; split; · exact (Project.maturity _ _).read
 exact Plausible.atom 0
  ) (inferInstance : Fintype M)
  ) (inferInstance : DecidableEq M)
lemma arc (f:ℝ→Link G n)(hf:ContDiffAt ℝ ω f 0)(j:ℕ): weigh f G' j=if e≤j then someJ ((fun y=>p.light x y v)∘ Haiku.life f) (j-e+p.r) else 0:=by
 let g (z:Link G n):= p.light x (input G n z) v
 let i:= p.r; have h₀:ContDiffAt ℝ ω g 0:= (Helmet.frameGrade p.atom x|>.smooth).mul contDiffAt_const; have he(j:ℕ)(hj:j<p.r): Radial.jet g j=0:=by unfold g; rw [frame_cross, (show (Radial.jet (Helmet.frame p.atom x) j)=0 from funext fun y=> (Helmet.frameGrade ..|>.jet_z y hj)) ,smul_zero]
 let v₀ := someJ (g ∘ echo f) (j-e+p.r); have he':someJ ((fun y=>p.light x y v)∘ Haiku.life f) (j-e+p.r)=v₀:=rfl; rw [he']; split
 next hv=>
    unfold v₀; rw [weigh_curved h₀ hf, weigh_higher he (j-e)]; nth_rw 1 [← show j-e+e=j from Nat.sub_add_cancel hv]; rw [weigh_higher (m:=e) (show ∀ i<e, Lantern.gleam p x v e i=0 from fun i hi=> if_neg hi.not_ge)]; apply congr_fun _ (j-e); apply congr_arg _ (funext (fun x:ℕ=>?_)); unfold Lantern.gleam; rw [if_pos (Nat.le_add_left ..),Nat.add_sub_cancel]
 next he=>
    unfold weigh; refine Finset.sum_eq_zero (fun i hi=>?_ ); have ht:i ≤ j:= Nat.le_of_lt_succ (Finset.mem_range.mp hi); rw [show Lantern.gleam p x v e i = 0 from if_neg (by omega)]; exact ((Act.static (0:ℝ) (n:=j-i)).writes _ le_rfl).trans (by simp [just])
set_option maxHeartbeats 200000 in
lemma ever (h:p.atom.Invariant) (d:ℕ) : Vernal G n G' d:= by
 refine ⟨fun u w s g ht hv hh hk=> ?_⟩; have hx : ∀ i z, p.light x (Lattice.gauge i z) v = p.light x z v:= by
    intro i z; unfold light Atom.unmasked; simp_rw [Work.F05.slot_gauge]; exact congr_arg (·* _) (h _ _)
 rw [arc p _ v _ u ht _,arc p _ v _ w hv _]; split; swap; · rfl
 have hP:(fun z=>p.light x z v) ∘ Haiku.life w=ᶠ[𝓝 0] (fun z=> p.light x z v) ∘ Haiku.life (G:=G) u:= hk.mono fun i h=> (congr_arg (fun y:Config G n=> p.light x y v) h).trans (hx ..); unfold PositionX.Jet.someJ; rw [(hP.iteratedDeriv _).eq_of_nhds]
end Lantern
end YM.QuadraticLocal.Poetry
