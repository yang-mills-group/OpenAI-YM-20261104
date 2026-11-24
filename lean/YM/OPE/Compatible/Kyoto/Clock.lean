import YM.OPE.Compatible.Kyoto.Toll
import YM.OPE.Compatible.Cres.Flown
/-!
# Per-patch evaluation with one-station slope. Stamp accounting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Dial
open Function Filter Set Lattice WithLp Finset
open scoped Topology BigOperators Classical
open Stroke Hark Pipes Lake
variable {I:Type}{n B:Side}{L:Filter I}{V Ω Bf Bc T ε q p:I→ℝ}{ρ S t δ Λ:ℝ}{u r j d:ℕ}
section book
variable (D:Fin (d+1)→ℕ)
local notation "D!"=> (fun i:Fin (d+1)=> Dryst (D i))
variable (T:I→ Mel (fun i=>Dryst (D i))→L[ℝ] Mel (fun i=> Dryst (D i))) (hB:Tendsto V L atTop) (ht:RateLE L V T 0) (hv: RateLE L V ε (-(1/2)))
include hB ht
open ContinuousLinearMap
set_option quotPrecheck false
local notation "V*"=> Mel D!
lemma pricesS (i:Fin (d+1)): RateLE L V (fun v=> ζCost (PDiag (T v).toLinearMap i)) 0:=by
       let z: Mel D!→L[ℝ] Jewel (D! i):= ContinuousLinearMap.proj i; let p:= ContinuousLinearMap.single ℝ (fun i:Fin (d+1)=>Jewel (D! i)) i; have hh : RateLE L V (fun v=> z ∘L (T v ∘L p)) 0:=by
            have hx:=RateLE.bil ht (RateLE.const p hB) (Z:=_) (Eventually.of_forall (fun v=> opNorm_comp_le (T v) p)); exact (RateLE.bil (RateLE.const z hB) hx (Eventually.of_forall fun v=> opNorm_comp_le z _)).mono (by simp)
       let x:= ‖(τ₀ (D! i)).toContinuousLinearMap‖; apply ((hh.norm.mul (RateLE.const x hB)).mono (by simp)).congr; exact Eventually.of_forall fun v=> congr_arg (fun s: Jewel (D! i)→L[ℝ] Jewel (D! i)=> ‖s‖*x) (show z ∘L (T v ∘L p)=(PDiag (T v).toLinearMap i).toContinuousLinearMap from ContinuousLinearMap.ext fun _=>rfl)
include hv
lemma borderW : RateLE L V (fun i=> FeeF D ((border (ε i) (T i).toLinearMap).toContinuousLinearMap) B) 0:=by
        let f(i):= (FilmP D! (ε i)).toContinuousLinearMap; let z:= PlaS D!; have hV:= hv.mono (show -(1/2:ℝ)≤0 by norm_num); have hx: RateLE L V f 0:= ( (RateLE.const (z 0) hB |>.add ((hV.smul (RateLE.const (z 1) hB)).mono (by simp)) hB).add (((hV.pow 2 hB).smul (RateLE.const (z 2) hB)).mono (by simp)) hB).congr (Eventually.of_forall fun i=> ContinuousLinearMap.ext fun x=> (filmW x _).symm)
        let U:= (Junit D!).toContinuousLinearMap; have hK:=RateLE.bil ht (RateLE.const U hB) (Eventually.of_forall (fun v=> opNorm_comp_le (T v) U)); have hp:RateLE L V (fun i=> (border (ε i) (T i).toLinearMap).toContinuousLinearMap) 0:= ((RateLE.bil hx hK (Eventually.of_forall (fun v=> opNorm_comp_le (f v) _))).mono (by simp)).congr (Eventually.of_forall fun i=> ContinuousLinearMap.ext fun _=>rfl); exact ((RateLE.const ((B.val:ℝ)^d) hB).smul (τreal _ _ V hB hp)).mono (by simp)
abbrev ChargeP (D:Fin (d+1)→ℕ)(p:Side)(V:(i:Fin (d+1))→ℕ→ΦB (Dryst (D i)))(S:ℝ):= ∀ (i:Fin (d+1))(j:ℕ)(T:Mel (fun i=>Dryst (D i))→ₗ[ℝ] Mel (fun i=>Dryst (D i))),Pipes.Stamp (Drift.lapPrice p) V T j→∀ x:Dryst (D i),∀ r:ℝ,|r|≤1→ |‖border r T (Pi.single i x) i‖^2 - (Drift.lapPrice p i.val^j * ‖x‖)^2|≤ (j*(Drift.lapPrice p i.val^j)^2*S*r^2+ |r|^3*3*(ζCost (PDiag T i))^2)*‖x‖^2 -- duplicate D binder macro capture? fix
variable (P:(i:Fin (d+1))→ℕ→ ΦB (Dryst (D i)))
variable (hh:ChargeP D n P S) (hA: 1≤ S) (hr:0<t)(hz:∀ᶠ i in L,Bf i-Bc i=t) (hΩ:Tendsto Bf L atTop)(hg: RateLE L V Bf 1)(hq:∀ᶠ i in L,Bf i* ε i^(2:ℕ) ≤ 2)(hw:∀ᶠ i in L,Stamp (Drift.lapPrice n) P (T i).toLinearMap r)
include hh hA hr hz hΩ hg hq hw
lemma Tavern (hp:B=n^r) (ha:(↑r:ℝ)*S*2 < t*j/2):∀ᶠ i in L, Flyer (FeeF D ((border (ε i) (T i).toLinearMap).toContinuousLinearMap) B) (B.val:ℝ) (Reven j (Bc i) (Bf i)):=by
       let f(i:Fin (d+1)):=Drift.lapPrice n i.val^r
       have hσ:= fun (i:Fin (d+1))=> Γslope j r hr hz hB hΩ hg hv hq (pricesS D T hB ht i) hA (show 0<f i from by unfold f Drift.lapPrice; positivity) ha; filter_upwards [(hv.tends (by norm_num) hB).norm.eventually (ge_mem_nhds (by norm_num: ‖(0:ℝ)‖<1)), revenueZ j hr hΩ hz, hw,eventually_all.mpr hσ] with i hi ht hZ hv; exact Visor D _ _ hp ht.1 (fun _ hv x hx=>Scope hZ x _ hx hv (ε i)) (fun j x=> (hh j r (T i).toLinearMap hZ x (ε i) hi).trans (mul_le_mul_of_nonneg_right (hv j) (sq_nonneg _))) -- charge
end book
end YM.OPE.Dial
