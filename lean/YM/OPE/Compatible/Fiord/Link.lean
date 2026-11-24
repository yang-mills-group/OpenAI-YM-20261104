import YM.OPE.Compatible.Fiord.Site
import YM.OPE.Compatible.Fathom.Cycle
/-!
# Tensor Schur identity
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Paver
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP
attribute [local instance] Gauge.frobInner
open Shell Char Planned.PrimaryIntegral295.Carrier Terp
variable {n c f:Side}{I J:Type}{G:Gauge}{r i j d:ℕ}{K:KernelChoices}
open Silt.Float Silt Cloud
open Finset
section cm
open Spells
section
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable (A:Law E)(P:Law F)
variable [Fintype I]
noncomputable def coordinateDual (p:PAD I): Module.Dual ℝ (PAD I) where
      toFun:=fun w=>p ⬝ᵥ w
      map_add' :=fun _ _=>dotProduct_add ..
      map_smul' :=fun _ _=>dotProduct_smul ..
lemma markH (p:PAD I): crewZ (coordinateDual p)=p:=by
       funext x; change dotProduct p (Pi.single x 1)=_; unfold dotProduct; rw [sum_eq_single x]; rw [Pi.single_eq_same,mul_one]; · intro i _ hi; simp only [Pi.single_eq_of_ne hi, mul_zero]
       simp
lemma proof_C (p q:PAD I)(Z:E→L[ℝ] PAD I): p ⬝ᵥ (chamber A Z *ᵥ q)=A.wick ((coordinateDual p).comp Z.toLinearMap) ((coordinateDual q).comp Z.toLinearMap):=by rw [Salvet,markH,markH]
-- stat.Property could avoid churn by direct Wick
end
open Merchant Variance Silt.Phere Jargon Merchant.SiteL
variable {Y:Sponsor G}{T:Seasons Y} {t:ℝ} (V: Alps Y T i t)(hp:4 ≤ i)
local notation "X!"=>Bid.Dir G n
set_option quotPrecheck false
local notation "U!"=> (flats G n).toContinuousLinearMap
noncomputable abbrev PressD : Bid.Dir G n→ₗ[ℝ] Module.Dual ℝ (Bid.Dir G n):= chrom (Dune V)
local notation "H!"=> PressD V (n:=n)
local notation "M!"=>Prog Y.K V.gear G n
local notation "K!"=> Vessel Y.K V.gear G n hp
include hp
lemma offsetΦ (x:Bid.Dir G n): H! x=(coordinateDual (M! *ᵥ (flats G n) x)).comp (flats G n).toLinearEquiv.toLinearMap:=by
       apply LinearMap.ext; intro y; change chrom (Dune V) x y= dotProduct (M!*ᵥ flats G n x) (flats G n y); rw [Merchant.podium,sheen _ _ _ hp,entrusted,alignZ _ _ _ hp]
lemma breatheT (x: Vec G n 1):Health (Prog Y.K V.gear G n) ((M!)*ᵥ x):=by
       intro y hy; rw [← show _= M! from (alignZ _ _ _ hp), ← entrusted];rw [hy,dotProduct_zero] -- ensure M! only pattern
lemma truism (x:Vec G n 1)(hx:Health (Prog Y.K V.gear G n) x): Favorable (PressD V (n:=n)) (Vessel Y.K V.gear G n hp) ((coordinateDual x).comp (U!).toLinearMap):=by
       let p:= (coordinateDual x).comp (U!).toLinearMap; let K:=K!; unfold Favorable; apply LinearMap.ext; intro y; let t:= U! y; let z:=M! *ᵥ t; let C:Module.Dual ℝ X!:= PressD V y
       have he:C=(coordinateDual z).comp (U!).toLinearMap:=offsetΦ V hp y
       change chrom (Dune V) (K.inverse p) y= x ⬝ᵥ t; rw [show chrom (Dune V) (K.inverse p) y=chrom (Dune V) y (K.inverse p) from (by rw[Merchant.podium,Merchant.podium,sheen V _ _ hp,sheen V _ _ hp]; apply invertG; exact alignZ _ _ _ hp)]
       change K.wick p C= x ⬝ᵥ t; rw [wickTurn, he, ←proof_C]; rw [show chamber K (U!)= _ from (Hport Y.K _ G n hp).choose_spec.1, blankV _ hp z (breatheT V hp t),show z= (M!)ᵀ*ᵥ t from (by rw[alignZ _ _ _ hp]), ← entrusted,HealthN hp V.gear _ hx]; exact dotProduct_comm ..
-- licence.Churn transfer
variable (R:Board n (r+1))(D:Law (Merchant.Chamber G r))
local notation "W!"=> sailT G R
noncomputable abbrev ΘCog:=mate (sailT G R) (PressD V) D
noncomputable abbrev SweepR : (Bid.Dir G n × Merchant.Chamber G r)→L[ℝ] Bid.Dir G n:= (ΘCog V R D) ∘L ContinuousLinearMap.fst ℝ (Bid.Dir G n) _+(W!) ∘L ContinuousLinearMap.snd ℝ _ _
omit hp in
private lemma ClanX {I E J:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup J][NormedSpace ℝ J][FiniteDimensional ℝ J][Fintype I](W:E→L[ℝ] J)(d:J→ₗ[ℝ] Module.Dual ℝ J) (K:Law J)(D:Law E)(U:J→L[ℝ] PAD I)(hL:SiteL W d D)(hz:∀ x:J,Favorable d K (d x))(x y:PAD I)(p q:Module.Dual ℝ J)(hx:Favorable d K p)(hy:Favorable d K q)(hP:p=(coordinateDual x).comp U.toLinearMap)(hQ:q=(coordinateDual y).comp U.toLinearMap):
       let T:= (mate W d D) ∘L ContinuousLinearMap.fst ℝ J E+W∘L ContinuousLinearMap.snd ℝ J E
       x ⬝ᵥ (chamber K U *ᵥ y)=x ⬝ᵥ (chamber (united K D) (U∘L T) *ᵥ y):=by
            let F:=mate W d D; let Z:=U∘L F; let H:=U∘L W; intro T; subst p q; rw [show (U ∘L T)=chorus Z H from ?_,churn _ _ _ _, Matrix.add_mulVec,dotProduct_add,proof_C K,proof_C K,proof_C D]; exact (aspect W d D K hL hz _ _ hx hy).symm; apply ContinuousLinearMap.ext; intro x; exact map_add U (F x.1) (W x.2) 
set_option maxHeartbeats 200000 in
lemma LeaseX (hL:SiteL (W!) (PressD V) D): Licence ((flats G n).toContinuousLinearMap ∘L SweepR V R D) (united (Vessel Y.K V.gear G n hp) D) V.gear Y.K:=by
        let A:=M!; let K:=K!; let d:=PressD V (n:=n); let F:= ΘCog V R D; let U:= U!; intro x y hx hy; have hz(w:Bid.Dir G n): Favorable d K (d w):=by rw [show d w=_ from offsetΦ V hp w]; exact truism V hp _ (breatheT V hp _)
        let p:= (coordinateDual x).comp U.toLinearMap; let q:= (coordinateDual y).comp U.toLinearMap; let Z:= U∘L F; let H:=U∘L W!; calc
            _ = x ⬝ᵥ (chamber K U *ᵥ y):= vessel_c V.gear hp _ _ hx hy
            _ = x ⬝ᵥ (chamber (united K D) ((flats G n).toContinuousLinearMap ∘L SweepR V R D) *ᵥ y):=by
                  have hu := ClanX (W!) d K D U hL hz x y p q (truism V hp x hx) (truism V hp y hy) rfl rfl
                  unfold SweepR ΘCog; with_reducible_and_instances exact hu

end cm
end YM.OPE.Cascade.Paver
