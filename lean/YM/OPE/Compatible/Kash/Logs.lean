import YM.OPE.Compatible.Kash.Winter
/-! # Sap lifts, flag currency compatible under upward/downward motion. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{P:ChartRatio G}{R:Patch}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Alps Roles Planned.PrimaryIntegral295.Carrier Hark Quit.Jac
variable {d:ℕ}{W I E:Type}{τ:Phase→ℕ}
variable {n:Side}(x:Site n)
local notation "Q"=>Shade G
local notation "Y!"=>Tower (Shade G) d τ
section
variable (T:Tower (Shade G) d τ)
noncomputable abbrev Mast (τ:Phase→ℕ)(i:Phase): Seat (d+i.val) (τ i) (Shade G)→L[ℝ] Seat (d+1+i.val) (τ i) (Shade G):= Drift.kindle G _ _ _ (by omega)
noncomputable def soar (T: Tower (Shade G) d τ) :Tower (Shade G) (d+1) τ:= fun i=> Mast τ i (T i)
lemma soak:Drift.spread G (d+1) τ (soar T)=Drift.spread G d τ T:=funext fun i=>kindle_eq (T i) (by omega)
lemma Low : Vtap (soar T) x=Vtap T x:=by
        funext i; unfold Vtap; rw[soak]; exact JetS.eta _ _ (flairS_eq T 0 ..) (flairS_eq T 1 ..) (flairS_eq T 2 ..)
lemma flight_s (p:solar G d τ): soar p.val∈solar G (d+1) τ:=by
       refine ⟨?_,fun n x=>?_⟩; · rw[soak]; exact p.property.1
       change (tor n).Marbles (Vtap (soar _) _); rw[Low]; exact p.property.2 ..
noncomputable def see (p:solar G d τ):solar G (d+1) τ:=⟨soar p.val,flight_s p⟩
end
section
variable (T:Tower (Shade G) (d+1) τ) (h:Antitone τ)
noncomputable def slump : Tower (Shade G) d τ:= fun i=> if hp:i=0 then 0 else let j:Phase:= ⟨i.val-1,by have h:= i.isLt;omega⟩; MastA (by have ht:i.val≠0:=fun he=>hp (Fin.ext he); change i.val-1+1=i.val; omega) (T j)
where MastA {i j:Phase}(hj:j.val+1=i.val)(Z:Seat (d+1+j.val) (τ j) (Shade G)): Seat (d+i.val) (τ i) (Shade G):= glasses (Shade G) _ (τ j) (τ i) (h (show j ≤ i from by change j.val ≤  i.val;omega)) (Drift.kindle G _ _ _ (by omega) Z)
lemma shift (i j:Phase)(he:i.val=j.val+1): lilies _ _ _ (slump T h i)=lilies _ _ _ (T j):=by
       have hp:j=⟨i.val-1,by clear he j; have h:=i.isLt;omega⟩:=by apply Fin.ext; change j.val=_-1;omega
       subst j; unfold slump; rw[dif_neg]; simp only [slump.MastA,putG,forgets]; exact kindle_eq _ _; intro H; subst i; contradiction
lemma spreadYs : spread G d τ (slump T h)=Drift.glide (spread G (d+1) τ T) 1:=by
        funext i; fin_cases i
        · change lilies _ _ _ (slump T h 0)=0; rw [show slump T h 0=0 from dif_pos rfl,map_zero]
        · exact shift T h 1 0 rfl
        exact shift T h 2 1 rfl
lemma DelayK (x:Site n): Vtap (slump T h) x=fun i=> Ū*Vtap T x i:=by
        funext i; unfold Vtap; rw [spreadYs,Drift.baton];change Ū^1*_= _; rw [pow_one];rfl -- rhs ranks already d+1
lemma sail_t (p:solar G (d+1) τ): slump p.val h∈solar G d τ:=by
        refine ⟨?_,fun n x=>?_⟩; swap;· change (tor n).Marbles (Vtap _ _); rw [DelayK]; exact prodMar (tor n) (staysP ..) (p.property.2 ..)
        rw [spreadYs]; intro i j; fin_cases i
        · rw [Drift.glide_nil _ (by decide)]; exact fun _=>rfl
        · exact p.property.1 0 j
        exact p.property.1 1 j
noncomputable def slipK (p:solar G (d+1) τ):solar G d τ:= ⟨slump p.val h,sail_t h p⟩
end
end YM.OPE.Variance
