import YM.OPE.Compatible.Straws.Hill
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Arc
omit [MeasurableSpace E][BorelSpace E] in abbrev ziao (x:E)(i:Fin (finrank ℝ E)):= (Module.finBasis ℝ E).coord i x
omit [MeasurableSpace E][BorelSpace E] in def armour (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](b:ℝ)(x:E):ℝ:= b*∑ i,ziao x i ^2
omit [MeasurableSpace E][BorelSpace E] in
lemma zBom (b:ℝ):Bond (armour E b):=by let q(i:Fin (finrank ℝ E)) := ⇑((Module.finBasis ℝ E).coord i); exact (Bond.keep b).mul (Bond.sum (fun i=> q i^2) _ fun i _=> (Bond.glyph _).pow 2)
omit [MeasurableSpace E][BorelSpace E] in
lemma zin (b:ℝ): fderiv ℝ (armour E b) 0=0:=by
     suffices hp:HasFDerivAt (armour E b) (0:E→L[ℝ] ℝ) 0 from hp.fderiv
     let σ(i:Fin (finrank ℝ E)):= toContinuousLinearMap ((Module.finBasis ℝ E).coord i)
     have hx(i:Fin (finrank ℝ E)): HasFDerivAt (fun x:E=> ziao x i ^2) (0:E→L[ℝ] ℝ) 0:=by simpa [pow_two] using! HasFDerivAt.fun_mul ((σ i).hasFDerivAt (x:=0)) ((σ i).hasFDerivAt (x:=0)) -- defeq
     simpa only [Finset.sum_const_zero, smul_zero] using! ((HasFDerivAt.fun_sum (u:=Finset.univ) (fun i _=> hx i)).const_mul b) -- names
omit [MeasurableSpace E][BorelSpace E] in
lemma zAtom (b:ℝ): Radial.Stationary (armour E b):=⟨((zBom b).smooth.of_le le_top).contDiffAt,by unfold armour ziao;simp,fun i=>by unfold Radial.jet; rw [iteratedFDeriv_one_apply,zin]; simp⟩
omit [MeasurableSpace E][BorelSpace E] in
lemma zCash (b:ℝ)(x:E): jet (armour E b) 2 x= armour E b x:=by
     let f:=armour E b; have hx(t:ℝ): f (t • x)=t^2*f x:=by unfold f armour ziao; simp only [map_smul,smul_eq_mul,mul_pow, ←Finset.mul_sum];ring
     have ht:= ((Pawn.trio (zAtom b)).stale x).limit; apply tendsto_nhds_unique ht; apply tendsto_const_nhds.congr'; filter_upwards [Tested.eventually_pos] with i (hi: 0 < i); change f x=f (i • x)/i^2; rw [hx];field_simp
omit [MeasurableSpace E][BorelSpace E] in
lemma zCosts : ∃ k>0,∀ x:E,k*‖x‖^2 ≤ armour E 1 x:=by
     simp_rw [←zCash]; apply Radial.quadratic_min; intro x hx; rw [zCash]; unfold armour; rw [one_mul]; apply Finset.sum_pos'; exact fun i _=> sq_nonneg _; let f:=Module.finBasis ℝ E; have hh: ∃ i, f.coord i x≠0 :=by by_contra h; push Not at h; exact hx (by rw [← f.sum_repr x]; simp_rw [show ∀ i,f.repr x i=0 from fun i=>h i, zero_smul]; simp)
     obtain ⟨i,hi⟩:=hh; exact ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩
end Arc
end YM.OPE.Libra
