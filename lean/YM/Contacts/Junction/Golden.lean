import YM.Contacts.Junction.Craft
/-! # linear vs canonical saddle apertures. Turn only.B.V. -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a:ℝ}{n k j r i:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
local notation "β" => N.β
namespace Sunrise
variable {V F:Type}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup F][NormedSpace ℝ F]
   {f:V→ F}
lemma differ {x:V}(hx:0≤a)(hy:‖x‖≤a)(hu : f 0=0)(h:∀ z:V, ‖z‖ ≤ a→Brush 2 C 1 f z) : ‖fderiv ℝ f 0 x-f x‖ ≤ C*a*‖x‖:= by
   let L:=iteratedFDeriv ℝ 1 f; let K:=fderiv ℝ f; let S:Set V:=closedBall 0 a; have H : ∀ z∈ S,DifferentiableAt ℝ K z ∧ ‖fderiv ℝ K z‖≤C ∧DifferentiableAt ℝ f z:= by
      intro z hz; have h:=(h z (mem_closedBall_zero_iff.mp hz)); refine ⟨(h.smooth.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num), ?_,h.smooth.differentiableAt (by norm_num)⟩; -- some Mathlib equality variant
      have hp:= (Brush.offer.1 h).2 2 le_rfl; unfold normJ at hp; rwa [← norm_iteratedFDeriv_fderiv (n:=1), norm_iteratedFDeriv_one] at hp
   have he: (0:V)∈S:= mem_closedBall_self hx; have hz:= (convex_closedBall (0:V) a); let Y' : V→ F := fun x=> f x-K 0 x; have hp(z) (h:z∈S): ‖K z - K 0‖≤ C*a:= by
        have ht:0≤C:=(show ∀ z:V, ‖z‖ ≤ a → Brush 2 C 1 f z from (by assumption)) 0 (norm_zero.trans_le hx) |>.nonneg
        exact (hz.norm_image_sub_le_of_norm_fderiv_le (fun i hi=> (H i hi).1) (fun i hi=>(H i hi).2.1) he h).trans (mul_le_mul_of_nonneg_left (by rw [sub_zero]; exact mem_closedBall_zero_iff.mp h) ht)
   have hk:= hz.norm_image_sub_le_of_norm_hasFDerivWithin_le (fun i hi=> (((H i hi).2.2).hasFDerivAt.sub (K 0).hasFDerivAt).hasFDerivWithinAt) hp he (mem_closedBall_zero_iff.mpr hy); rw [norm_sub_rev]; simpa only [hu,map_zero,Pi.sub_apply, sub_zero] using hk
lemma hiking {V: Dew G} {w z:V.Y} (x:V.X)(_hf:0 ≤ s)(ht:0<t) (he:‖w-z‖≤ t*(a-s)) : Fare.staying V.B w t s (ship x) ⊆ Fare.staying V.B z t a (ship x):= by
   rintro i ⟨d,⟨e,b,rfl⟩,rfl⟩; let k:= w-z; let p:=t⁻¹ • k+e; have h:‖p‖≤a:= by apply (norm_add_le ..).trans; rw [norm_smul_of_nonneg (inv_pos.mpr ht).le]; exact (le_of_eq (sub_add_cancel a s)).trans' (add_le_add ((inv_mul_le_iff₀ ht).2 he) (mem_closedBall_zero_iff.mp b));
   refine ⟨w+t • e,⟨p,mem_closedBall_zero_iff.mpr h,?_⟩,rfl⟩; unfold p; dsimp only; rw [smul_add,smul_inv_smul₀ ht.ne']; unfold k; abel
end Sunrise
open Sunrise
abbrev linearStay (u: Dew G)(T:ℝ)(z:u.X) := Fare.staying u.B (u.L z) u.grad T (ship z)
abbrev relative (u:Dew G)(T:ℝ)(z:u.X) := Fare.staying u.B (Lapis.orbit u.B u.ρ z) u.grad T (ship z)
namespace Travel
variable (p: Travel N Q Φ)(hG:G.Simple)(hk:2≤k)(hn:k≤n)(hP: LocalRatio P)(hd:0< d)
local notation "X₀" => (arcCoast Φ d)
local notation "Yp" => (fun i=> StagePort.flag (Φ i))
include p hd
lemma greenery : ∀ᶠ i in atTop, let v:=Φ i; let D:=v.dew; let s:= X₀ i; ∀ x:D.X, ‖x‖≤v.flag→ ‖Lapis.orbit D.B D.ρ x-D.L x‖≤D.grad*s/2:= by
   have hv:= wordPos p.dawn p.scale; let Z i:=(Φ i).taxi; let q i:=Z i*lensT n M (Z i); have hQ:= chairCost p.dawn p.scale M p.scale|>.1; let r:= Yp; have he:= p.f_current.forward; have hp:= p.parameter.back;
   have ht': ∀ᶠ i in atTop, γ i>0:= p.parameter.pos; have ht t:1≤ Delay.fineMonitor G L t:= Real.one_le_exp (sq_nonneg _); let X:= X₀; let g i:=(γ i)⁻¹;
   have H':N.Rush (- -(1/2)+vow*2) (fun i=> g i * (q i * r i^2)):= by have h: N.Rush (vow* (2:ℝ)) (fun i=>r i^2):= (by simpa only [Nat.cast_ofNat] using he.powers 2); exact hp.times (hQ.times h (zero_add _)) rfl
   have he' := sliding H' (by norm_num [vow]) (d/2) (half_pos hd); filter_upwards [p.f_current.pos,he',ht', p.dawn, Meter.sliding he vow_ok _ hv.2.1] with i hi h hi' hp' hq u D s x hx;
   have hz : ∀ x:D.X, ‖x‖≤ r i → Brush 2 (q i) 1 (Lapis.orbit D.B D.ρ) x := by intro x hx; obtain ⟨B,hB,hC⟩:=hp'.service; have hh := (luminous _ D.label _ _ _ _ _ _ B (n:=n) hp'.stitches.large hp'.staples hB (Z i) hp'.stitches.one hp'.stitches.overall _ (mem_ball_zero_iff.mpr (show ‖x‖ < (B.tables (Φ i).dew.T.high (Φ i).dew.S.patch).horizon from (by rw [hC]; exact hx.trans_lt ((le_abs_self _).trans_lt hq))))).smaller (show 2 ≤ n+2 from by omega); rw [hC] at hh; exact hh
   have hJ:Lapis.orbit D.B D.ρ 0=0:= by obtain ⟨B,hB,hϕ⟩:= hp'.service; exact Lapis.zeroO D.B D.T.up D.T.high D.ρ σ C B hB
   rw [norm_sub_rev]; apply (differ hi.le (a:=r i) hx hJ hz).trans; calc
     _ ≤ q i*r i*r i:= mul_le_mul_of_nonneg_left hx (mul_nonneg (hz _ hx|>.nonneg) hi.le)
     _ ≤ γ i *(s/2):= by rw [mul_assoc,← sq]; apply (inv_mul_le_iff₀ hi').1; exact ((le_abs_self _).trans h.le).trans (div_le_div_of_nonneg_right (le_mul_of_one_le_right hd.le (ht _)) (by norm_num))
     _ = _:= by change γ i* (s/2)= (γ i)* _ /2; ring
lemma travels : ∀ᶠ i in atTop, let v:=Φ i; let D:=v.dew; let s:= X₀ i; ∀ x:D.X, ‖x‖< v.flag→
     linearStay D (s/2) x⊆ relative D s x ∧ relative D s x⊆ linearStay D (2*s) x := by
   filter_upwards [p.parameter.pos,p.greenery hd] with i hi hx v D s x hy; have hs : 0 ≤ s:= mul_nonneg hd.le (Delay.monitor_pos G L _|>.le); replace hx:= hx x hy.le; change ‖Lapis.orbit D.B D.ρ x-D.L x‖ ≤ D.grad*s/2 at hx; have hg:0<D.grad := hi;
   refine ⟨hiking (V:=D) _ (half_pos (?_)).le hg ?_, hiking (V:=D) _ hs hg ?_ ⟩;
   · exact mul_pos hd (Delay.monitor_pos ..)
   · rw [norm_sub_rev]; exact hx.trans_eq (by ring)
   exact hx.trans (by nlinarith only [mul_nonneg hs hg.le])
end Travel
end Provision
end YM.Contacts.Junction
