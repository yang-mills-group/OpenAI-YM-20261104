import YM.OPE.Compatible.Spades.Stem
/-!
# Wick shrinking and heavy polarp under arbitrary transformed marginals
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
noncomputable def CurveG (q:J→ℝ)(h:Stature q k) :Song (PAD I):=Expire (Silt.chamber A S) (FarG A μ S h) k
noncomputable abbrev runG (q:J→ℝ)(h:Stature q k):J→ℝ:= Strike k (CurveG A μ S q h)
lemma waveS (P:Song (PAD I))(h:P∈ harmon (PAD I) k): stroll A μ S (Strike k P)=Strike k (LiftV (Silt.chamber A S) P k):=by
      funext i; have he:=basisH μ A S i 1 P h; simp only [one_smul,one_pow] at he; exact he
lemma TurnedT (q:J→ℝ)(h:Stature q k):CurveG A μ S q h∈harmon (PAD I) k:=peak _ _ _ _ (WealthF ..)
lemma Clad (q:J→ℝ)(h:Stature q k): stroll A μ S (runG A μ S q h)=Strike k (FarG A μ S h):=by
      unfold runG; rw [waveS _ _ _ _ (TurnedT ..)]; unfold CurveG; rw [vigil (Silt.chamber A S) _ (WealthF ..)]
lemma arises (P Q:Song (PAD I))(hp:P∈harmon (PAD I) k)(hq:Q∈ harmon (PAD I) k)(h:stroll A μ S (Strike k P)=stroll A μ S (Strike k Q)):P=Q:=by
      let T:= Silt.chamber A S; have he : LiftV T P k=LiftV T Q k:=by
           funext i; rw [waveS _ _ _ _ hp,waveS _ _ _ _ hq] at h; exact (gradeC (peak (A:=T) _ _ _ _ hp) _).symm.trans ((congr_arg (fun x:J→ℝ=>coeff x i 0) h).trans (gradeC (peak _ _ _ _ hq) _)) -- elaborating ambiguity
      have hz(p:Song (PAD I))(hp:p∈harmon (PAD I) k): Expire T (LiftV T p k) k=p:=by
           unfold Expire LiftV; rw [← switching]; -- name puts neg on outer
           simpa only [neg_neg] using negatives (by have he: (-1:ℝ) • opus T= -opus T:= (neg_smul (1:ℝ) (opus T)).trans (by rw [one_smul]) ; exact he ▸ opusReducer T (-1): reduces (harmon (PAD I)) (-opus T)) p hp (1/2:ℝ) k le_rfl
      exact (hz P hp).symm.trans ((congr_arg (fun w=>Expire T w k) he).trans (hz Q hq))
lemma Phire (p:J→ℝ)(h:Stature p k)(v:Fin i→J)(hp:i≤k):taxA A μ S p v=taxA A μ S (runG A μ S p h) v:=by
      apply mul_left_cancel₀ (show ((i.factorial:ℝ)⁻¹)≠0 from by positivity); rw [← boundY A μ S (runG A μ S p h) ((sailCost ..).cost),Clad, gradeC (WealthF ..)]; exact (SemG _ _ _ h i hp v|>.symm)
local notation "g"=> Silt.chamber
structure Chip (T:F→L[ℝ] (PAD I))(B:Law F):Prop where
       wick (u v: Dual' (PAD I)): A.wick (u.comp S.toLinearMap) (v.comp S.toLinearMap)=B.wick (u.comp T.toLinearMap) (v.comp T.toLinearMap)
omit [FiniteDimensional ℝ F] in
lemma mouldC (p:J→ℝ)(hp:Stature p k)(i:ℕ)(hi:i ≤ k)(v:Fin i→J):taxA A μ S (p-runG A μ S p hp) v=0:=by
       unfold taxA; let H:= Stature.poly (p:=runG A μ S p hp) (sailCost ..|>.cost) k; rw [FlSub ((hp.mono hi).smooth) ((H.mono hi).smooth)]; apply (duneSub _ _ (exil _ _ S (hp.mono hi) v) (exil _ _ S (H.mono hi) v)).trans; apply sub_eq_zero.mpr; exact Phire A μ S _ hp v hi -- comp rewrite
variable [MeasurableSpace F][BorelSpace F](ν:Measure F)[ν.IsAddHaarMeasure](B: Law F)(T:F→L[ℝ] PAD I)
-- Discharges even derivative tensors off the measured subspace
lemma Xtract (h: Chip A S T B)(f:J→ℝ)(hp:Stature f k): Haven ν B (k+1) ((f-runG A μ S f hp) ∘ T):=by
       let q:= f-runG A μ S f hp; have hq : Stature q k:= hp.sub (Stature.poly ((sailCost (CurveG A μ S f hp) k).cost) _); refine (corresponding B ν k (hq.blot T)).2 fun i hi x=>?_
       have he:Fline (q ∘ T) x=Fline q (T ∘ x) ∘ T:=funext fun v=>DFunLike.congr_fun (T.iteratedFDeriv_comp_right hq.smooth v (Nat.cast_le.mpr hi)) _; unfold Vas; change B.average ν (Fline _ _) =_; rw [he]; exact (margin A B S.toLinearMap μ ν T.toLinearMap h.wick _).symm.trans (mouldC A μ S f hp i hi _)
end
end YM.OPE.Jargon
