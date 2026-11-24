import YM.Integration.WilsonSeparatedPrefixMovingCellFactor
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Smooth address multipliers act on the original finite test page, at a fixed price. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingAddressPage
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore MeasureTheory
open scoped BigOperators Topology Classical ContDiff
open WilsonCoeffUV.Layout

variable {D j:ℕ}
theorem axes (f:Scroll D)(hj:j≤D)(z:Chamber):
    ‖iteratedFDeriv ℝ j f.val z.val‖≤(4:ℝ)^j*‖page D f‖:=by
  classical
  let P:=iteratedFDeriv ℝ j f.val z.val
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro v
  let w:=fun i:Fin j=>fun a:Axis=>v i a • dot a
  have split (i:Fin j):∑a:Axis,w i a=v i:=by ext i';simp [w,dot,Finset.sum_apply,Pi.single_apply]
  have changeBasis:=P.toMultilinearMap.map_sum w
  simp only [split] at changeBasis
  change ‖P.toMultilinearMap v‖≤_
  rw [changeBasis]
  apply (norm_sum_le _ _).trans
  have each (a:Fin j→Axis):‖P.toMultilinearMap (fun i=>w i (a i))‖≤‖page D f‖*∏i,‖v i‖:=by
    simp only [w,MultilinearMap.map_smul_univ,smul_eq_mul,norm_mul]
    rw [norm_prod, mul_comm ‖page D f‖]
    exact mul_le_mul (Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>norm_le_pi_norm (v i) _))
      (creased f hj a z) (norm_nonneg _) (by positivity)
  calc ∑a:Fin j→Axis,‖P.toMultilinearMap (fun i=>w i (a i))‖ ≤ ∑_:Fin j→Axis,‖page D f‖*∏i,‖v i‖:=
          Finset.sum_le_sum fun a _=>each a
       _ = _:=by simp [Axis,Fintype.card_pi];ring

def multiply (u:Scroll D):Scroll D→ₗ[ℝ]Scroll D where
  toFun f:=⟨fun x=>u.val x*f.val x,(scribble u le_rfl).mul (scribble f le_rfl)⟩
  map_add' f g:=Subtype.ext (funext fun x=>mul_add (u.val x) (f.val x) (g.val x))
  map_smul' c f:=Subtype.ext (funext fun x=>mul_left_comm (u.val x) c (f.val x))

def tariff (D:ℕ):ℝ:=∑m∈Finset.range (D+1),∑i∈Finset.range (m+1),(m.choose i:ℝ)*4^(m-i)
theorem funded (u:Scroll D)(K:ℝ)(nk:0≤K)(wk:∀m≤D,∀z:Chamber,‖iteratedFDeriv ℝ m u.val z.val‖≤K):
    ∃T:Volume D→L[ℝ]Volume D,(∀f:Scroll D,T (page D f)=page D (multiply u f)) ∧ ‖T‖≤tariff D*K:=by
  classical
  have cost (m:ℕ)(hm:m≤D):∑i∈Finset.range (m+1),(m.choose i:ℝ)*4^(m-i)≤tariff D:=
    Finset.single_le_sum (f:=fun m=>∑i∈Finset.range (m+1),(m.choose i:ℝ)*4^(m-i))
      (fun _ _=>Finset.sum_nonneg fun _ _=>by positivity) (Finset.mem_range.mpr (by omega))
  have nn:0≤tariff D:=by unfold tariff;positivity
  apply factoring (page D) ((page D).comp (multiply u)) submitted (tariff D*K) (mul_nonneg nn nk)
  intro f
  apply pledge _ (by positivity)
  intro m hm directions z
  have bound:=norm_iteratedFDeriv_mul_le (scribble u le_rfl) (scribble f le_rfl)
    (x:=z.val) (Nat.cast_le.mpr hm)
  change ‖(iteratedFDeriv ℝ m (fun x=>u.val x*f.val x) z.val) (dot ∘ directions)‖≤_
  apply ((iteratedFDeriv ℝ m (fun x=>u.val x*f.val x) z.val).le_opNorm _).trans
  have unit:∀i:Fin m,‖(dot ∘ directions) i‖=1:=by intro i;change ‖(Pi.single (directions i) 1:Axis→ℝ)‖=1;rw [Pi.norm_single,norm_one]
  simp only [unit,Finset.prod_const_one,mul_one]
  apply bound.trans
  calc ∑i∈Finset.range (m+1),(m.choose i:ℝ)*‖iteratedFDeriv ℝ i u.val z.val‖*‖iteratedFDeriv ℝ (m-i) f.val z.val‖
      ≤∑i∈Finset.range (m+1),((m.choose i:ℝ)*4^(m-i))*(K*‖page D f‖):=by
          apply Finset.sum_le_sum
          intro i hi
          calc _ ≤ (m.choose i:ℝ)*K*((4:ℝ)^(m-i)*‖page D f‖):=by
                apply mul_le_mul (mul_le_mul_of_nonneg_left (wk i (by have:=Finset.mem_range.mp hi;omega) _) (by positivity))
                  (axes f (by omega) z) (norm_nonneg _) (by positivity)
               _ = _:=by ring
       _ ≤ _:=by rw [←Finset.sum_mul];nlinarith [mul_le_mul_of_nonneg_right (cost m hm) (mul_nonneg nk (norm_nonneg (page D f)))]
end YM.Integration.WilsonSeparatedPrefixMovingAddressPage
