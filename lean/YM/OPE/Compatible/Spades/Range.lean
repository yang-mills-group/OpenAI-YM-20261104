import YM.OPE.Compatible.Spades.Mass
/-!
# Wick singular transfer at off-R directions. use Sensor
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff ENNReal
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt Tensor Cloud
open Cascade.Paver
variable {E F X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable {I J:Type}{i j k r:ℕ}
section
variable [FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] (A:Law E)(μ:Measure E)[μ.IsAddHaarMeasure](V:F→L[ℝ] E)
variable [Fintype I] (S:E→L[ℝ] PAD I)
local notation "J"=> PAD I
structure Sensor (p':PAD I→ℝ)(k:ℕ) :Prop where
       stays : Stature p' k
       allure i : i ≤ k→∀ v:Fin i→ PAD I,taxA A μ S p' v=0
lemma sensorU (p:PAD I→ℝ) (h:Stature p k):Sensor A μ S (p-runG A μ S p h) k:=⟨h.sub (Stature.poly ((sailCost (CurveG A μ S p h) k).cost) k),mouldC A μ S p h⟩ -- fixed
variable [MeasurableSpace F][BorelSpace F](ν:Measure F)[ν.IsAddHaarMeasure](B: Law F)(T:F→L[ℝ] PAD I)
omit [BorelSpace E][μ.IsAddHaarMeasure] [FiniteDimensional ℝ E] in lemma Sensor.pick {p:PAD I→ℝ} (hp:Sensor A μ S p (k+1))(v:PAD I):Sensor A μ S (pointD v p) k:=by
       refine ⟨hp.stays.lower v,fun i hi x=>?_⟩; unfold taxA; rw [← rungs (hp.stays.smooth.of_le (Nat.cast_le.mpr (Nat.succ_le_succ hi)))]; exact hp.allure _ (by omega) _
lemma tSensor {p:PAD I→ℝ} (h: Chip A S T B)(hp: Sensor A μ S p k):Sensor B ν T p k:=⟨hp.stays,fun i hi x=> (margin A B S.toLinearMap μ ν T.toLinearMap h.wick _).symm.trans (hp.allure i hi x)⟩
lemma Sensor.toHaven {p:PAD I→ℝ} (hp: Sensor A μ S p k): Haven μ A (k+1) (p ∘ S):=by
       refine (corresponding A μ k (hp.stays.blot S)).2 (fun i hi x=>?_); unfold Vas; rw [show Fline (p ∘ S) x= Fline p (S ∘ x) ∘ S from funext fun i'=>DFunLike.congr_fun (S.iteratedFDeriv_comp_right hp.stays.smooth i' (Nat.cast_le.mpr hi)) x]; exact hp.allure _ hi _
lemma P3Chip (a:(PAD I)→L[ℝ] PAD I)(hp:Chip A S (a ∘L S) A)(f:PAD I→ℝ) (x:PAD I):stroll A μ S f (a x)= stroll A μ S (f ∘ a) x:=by
       unfold stroll; refine Eq.trans (show _=_ from margin A A S.toLinearMap μ μ (a ∘L S).toLinearMap hp.wick (fun i=>f (a x+i))) ?_; apply congr_arg; ext1 i; change f _= f (a _); rw[map_add];rfl
lemma incentive (a:J→L[ℝ] J)(hp:Chip A S (a ∘L S) A)(f:J→ℝ)(h:Stature f k)(hf:f ∘ a=f)(x:J): runG A μ S f h (a x)= runG A μ S f h x:=by
       let V:= CurveG A μ S f h; let U:= FarG A μ S h; have he (j:ℕ)(hj:j ≤ k)(v:Fin j→ J)(x:J): Fline f v x=Fline f (a∘v) (a x):=by unfold Fline; have hp:= DFunLike.congr_fun (a.iteratedFDeriv_comp_right h.smooth x (Nat.cast_le.mpr hj)) v; rwa[hf] at hp
       have ht(j:ℕ)(hj:j ≤ k)(v:Fin j→ J): U j v=U j (a ∘ v):=by
           unfold U; rw[SemG _ _ _ h j hj, SemG _ _ _ h j hj]; apply congr_arg; exact ((congr_arg (A.average μ) (funext fun i=>he j hj v (S i))).trans (margin A A S.toLinearMap μ μ (a ∘L S).toLinearMap hp.wick (Fline f (a ∘ v))).symm)
       let W:=fun i:ℕ=> (V i).compContinuousLinearMap (fun _=>a); have hg: V ∈ harmon (PAD I) k:=TurnedT ..; have hw : W∈harmon (PAD I) k:=eer a _ W (fun _=>rfl) hg; have hy:Strike k W=Strike k V ∘ a:=rfl; apply congr_fun (f:=Strike k W); apply congr_arg; refine arises A μ S W V hw hg (funext fun j=>?_); rw [hy,← P3Chip A μ S a hp]; unfold V; change stroll A μ S (runG A μ S f h) (a j)=stroll A μ S _ j; rw [Clad]; exact sum_congr rfl fun i hi=> (ht i (by have h:=mem_range.mp hi;omega) (fun _=>j)).symm -- check RHS?
end
end YM.OPE.Jargon
