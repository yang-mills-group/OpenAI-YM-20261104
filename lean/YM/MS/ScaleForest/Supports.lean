import YM.MS.ScaleForest.Calibrate
import YM.MS.ScaleForest.Locus
/-!
# Post conversions and regulator limits (point and test)

Take already calibrated wall GUARD and use those finite-field changes for
our two limits. Allows smearing first on the support of each profile.
UV then specialization in ε, then IR. Recall the UV in this prescription
is taken inside forest terms. Here is the test and compact-uniform version
of specializing the MOMENT chart at this stage (incl. polar cancellation,
not limits on unbudgeted summands). Thus can use reports AND the integral
limits through profiles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Panels
open Function Filter Set MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum Tone Detect Osc Fiddle XSpace XSpace.Chiral Cylinder Planted Beamline Quadratic Triangle
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open Planted FVA2 FVA2.Position FVA2.Position.Axes FVA2.Arrival Dframe WilsonMS
open Normalize.Fray
open scoped Topology Classical BigOperators ENNReal
variable {I J:Type} [TopologicalSpace I] [CompactSpace I] (ν:ℝ)
private abbrev CM (I:Type)[TopologicalSpace I] := C(I,ℂ)
/-- Sup metric, also asserts eventual continuity for each section. -/
structure Stills (l:Filter J)(F:J→I→ℂ)(f:I→ℂ) : Prop where
    certs : ∃ (A:J→ C(I,ℂ))(a:C(I,ℂ)), F=ᶠ[l] (fun j=> ⇑(A j)) ∧ f= a ∧ Tendsto A l (𝓝 a)
namespace Stills
variable {F G:J→I→ℂ}{f g:I→ℂ}{l:Filter J}
omit [CompactSpace I] in
lemma strokes (h:Continuous f) : Stills l (fun _=>f) f := ⟨ ⟨ fun _=>⟨ f,h⟩, ⟨ f,h⟩,EventuallyEq.rfl,rfl,tendsto_const_nhds ⟩ ⟩
lemma add (h:Stills l F f)(hx:Stills l G g): Stills l (F+G) (f+g):= by obtain ⟨A,a,hA,rfl,hP⟩:= h.certs; obtain ⟨B,b,hB,rfl,hQ⟩:= hx.certs; exact ⟨ ⟨ A+B,a+b,(hA.and hB).mono (fun i ⟨hi,hj⟩=> by simp only [Pi.add_apply,hi,hj]; rfl),rfl,hP.add hQ⟩⟩
lemma mul (h:Stills l F f)(hx:Stills l G g): Stills l (F*G) (f*g):= by obtain ⟨A,a,hA,rfl,hP⟩:= h.certs; obtain ⟨B,b,hB,rfl,hQ⟩:= hx.certs; exact ⟨ ⟨ A*B,a*b,(hA.and hB).mono (fun i ⟨hi,hj⟩=> by simp only [Pi.mul_apply,hi,hj]; rfl),rfl,hP.mul hQ⟩⟩
lemma taleSum {K:Type}{F:K→J→I→ℂ}{f:K→I→ℂ}(X:Finset K) (h:∀ i∈X,Stills l (F i) (f i)): Stills l (fun j x=>∑ i∈X, F i j x) (fun j=>∑ i∈X, f i j) := by
    induction X using Finset.induction with| empty=> simp_rw [ Finset.sum_empty ]; exact strokes continuous_const| insert i X hi ih=> simp_rw [ Finset.sum_insert hi ]; exact add (h i (by simp)) (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
omit [CompactSpace I] in
theorem stillPoint (h:Stills l F f)(x:I) : Tendsto (fun j=> F j x) l (𝓝 (f x)):= by
    obtain ⟨A,a,hA,rfl,hF⟩:= h.certs; exact (( show Continuous (fun i:CM I=>i x) from (by fun_prop) ).continuousAt.tendsto.comp hF).congr' (hA.mono fun i hi=> (congr_fun hi x).symm)

lemma still_parts {Q:Type}[LinearOrder Q]{F:J→I→Finset Q→T ℂ}{f:I→Finset Q→ T ℂ}(h:∀ p n, Stills l (fun j x=> F j x p n) (fun x=>f x p n)) (s:Finset Q)(n:ℕ): Stills l (fun j x=>byPartition (F j x) s n) (fun x=> byPartition (f x) s n) := by
    have hh (k:ℕ)(s:Finset Q)(n:ℕ) : Stills l (fun j x=> joinsP (F j x) k s n) (fun x=> joinsP (f x) k s n):= by
       induction k generalizing s n with
       | zero => exact strokes continuous_const
       | succ k ih=> simp_rw [joinsP]; apply taleSum ; intro r _; exact taleSum ( Finset.antidiagonal n ) (F:=fun (i:ℕ×ℕ) (j:J)(x:I)=> _ * _) (fun i _=> mul (h r i.1) (ih (s\r) i.2))
    unfold byPartition; exact taleSum (Finset.range _) (fun i _=> mul ( strokes (continuous_const (y:=( ( Nat.factorial i ):ℂ )⁻¹)) ) (hh i s n) )
variable {Gau:Gauge}{b:Bool} [FirstCountableTopology I]

lemma eachNode (L: Plan Gau I b)(ht:Hired L):
   (∀ s:ℝ, Stills dotty (fun z i=> fundraiser ν L z s i 0 []) (fun i=> costTable ν L i s 0 [])) ∧
   Stills atTop (fun s i=> costTable ν L i s 0 []) (stipend ν L) := by
    obtain ⟨R,hR,hL⟩:= nominal_sway (μ:=ν) ht; let Z(z:ℂ)(s:ℝ)(i:I):=nominal ν L z s i 0 []
    simp_rw [ payable ν L ht, backing_nil ]; change (∀ s, Stills dotty _ (Z 0 s)) ∧ Stills atTop (Z 0) _
    let z0:disc R := ⟨0,hR.top⟩; have hc(s:ℝ) : Continuous (fun z:disc R × I=> Z z.1 s z.2):= (hL 0 []).comp (f:=fun z:disc R × I=> (z.1,s,z.2)) (by fun_prop)
    let A(s:ℝ)(z: disc R) : CM I:= ⟨ Z z s,(hc s).curry_right⟩; constructor
    · intro s; let g(z:ℂ): disc R:= if h:z∈disc R then ⟨ z,h⟩ else z0; have here: ∀ᶠ i in dotty,i∈disc R:= Eventually.filter_mono (show dotty ≤ 𝓝 0 from nhdsWithin_le_nhds) (Metric.ball_mem_nhds _ hR.1);
      have hv: Tendsto g dotty (𝓝 z0):= by
          apply tendsto_subtype_rng.mpr
          refine (tendsto_id'.mpr (?_ : dotty ≤ 𝓝 0)).congr' ?_
          · exact nhdsWithin_le_nhds
          filter_upwards [here] with z hz; change z=(g z:ℂ); unfold g; rw [dif_pos hz]
      refine ⟨ ⟨ fun z=> A s (g z), A s z0,?_,rfl,(ContinuousMap.continuous_of_continuous_uncurry (A s) (hc s)).continuousAt.tendsto.comp hv⟩⟩
      filter_upwards [payoff ν L ht,here] with z hz hx; funext i; change _=nominal ν L (g z) s i 0 []; simp only [g, dif_pos hx]; rw [← hz,backing_nil]
    obtain ⟨r,hr,hP⟩:= (abide ν L ht).2.1 (1/2) (by norm_num) (by norm_num); obtain ⟨_,hX,⟨W,hW,hU⟩,hV⟩:= Frontier.enter hP (by norm_num) 0
    let U:CM I:= ⟨ WindowIR (nominal ν L) 0 0,hX.comp (f:=fun i:I=>((⟨ 0,hr.top⟩:disc r), i)) (by fun_prop) ⟩
    refine ⟨ ⟨ fun s=> A s z0, U,EventuallyEq.rfl,funext (fun i=> (authorized_IR ν L ht i).1),?_⟩⟩
    let K(s:ℝ):= W*exp (-(1/2)*s); have hf:=tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (show -(1/2:ℝ)<0 from (by norm_num)) ( f:=id ) tendsto_id); have hK:Tendsto K atTop (𝓝 0):=(by simpa only [mul_zero,Function.comp_apply,id_eq] using hf.const_mul W)
    exact tendsto_iff_dist_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=> dist_nonneg) (by filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs; rw [ dist_eq_norm ]; exact (ContinuousMap.norm_le _ (by unfold K; positivity)).mpr (fun i=> hU 0 hr.top i s hs)) hK)
end Stills
end YM.MS.ScaleForest.Panels
