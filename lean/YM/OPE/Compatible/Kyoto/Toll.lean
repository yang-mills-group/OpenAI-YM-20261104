import YM.OPE.Compatible.Kyoto.Whale
import YM.OPE.Compatible.Kyoto.Loop
/-!
# Per-patch assembly bills of block orientation
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Dial
open Function Filter Set Lattice WithLp Real Finset
open scoped Topology BigOperators Classical
open Stroke Hark Pipes Lake
variable {I:Type}{n:Side}{L:Filter I}{V Ω Bf Bc T ε q p:I→ℝ}{ρ S t δ Λ:ℝ}{u r d:ℕ}
section book
private lemma δobt (hp:1 ≤ ρ): 2-ρ⁻¹ ^ (2:ℕ) ≤ ρ^2:=by
       have hx: 0<ρ:=zero_lt_one.trans_le hp; have he:=sq_nonneg (ρ-ρ⁻¹); nlinarith only [he,mul_inv_cancel₀ hx.ne']
private lemma δbill {x y k:ℝ}(h:0≤ x)(ht:0≤ y)(hy:0<Λ)(hz:1 ≤ ρ)(hq:k ≤ Λ^2*(1-ρ⁻¹^2))(he: |y^2 - (Λ*x)^2|≤ k*x^2): Λ*x*ρ⁻¹ ≤ y ∧ y≤ Λ*x*ρ:=by
      have hu:0<ρ⁻¹:=inv_pos.mpr (zero_lt_one.trans_le hz); have hx:= mul_le_mul_of_nonneg_right hq (sq_nonneg x); obtain ⟨hp,H⟩:=abs_le.mp he; constructor
      · suffices hd: (Λ*x*ρ⁻¹)^2 ≤ y^2 by nlinarith [show 0 ≤ Λ*x*ρ⁻¹ from by positivity]; -- pointer
        linarith only [hx,hp]
      suffices hss:(y)^2≤(Λ*x*ρ)^2 by nlinarith [show 0 ≤ Λ*x*ρ from mul_nonneg (mul_nonneg hy.le h) (by positivity)] -- h clash
      linarith only [hx,H,mul_le_mul_of_nonneg_left (δobt hz) (sq_nonneg (Λ*x))]
lemma κside (B:Side)(h:B=n^r)(i: Fin (d+1)) : (((B:ℕ):ℝ)^d)*(Drift.lapPrice n i.val)^r=((B:ℕ):ℝ)^(d-i.val):=by
       have hx(i:ℕ): (((B:ℕ):ℝ)⁻¹)^i=Drift.lapPrice n i^r:=by unfold Drift.lapPrice; rw[h]; push_cast; rw[inv_pow,inv_pow,inv_pow]; ring
       rw[← hx]; rw[inv_pow,pow_sub₀ _ (by positivity: (((B:ℕ):ℝ))≠0) (Nat.le_of_lt_succ i.isLt)] -- div eq
variable (D:Fin (d+1)→ℕ)
noncomputable def FeeF (U: CanA D→L[ℝ] CanA D)(B:Side): Train (fun i=> BC (D i)):= (B.val:ℝ)^d • εarm D U -- weird
variable (U:CanA D→L[ℝ] CanA D) (B:Side)
lemma sprY (i:Fin (d+1)) (p:BC (D i))(j) : route (FeeF D U B) j i p= (B.val:ℝ)^d • route (εarm D U) j i p:=rfl
lemma Visor (h:B=n^r)(hx:1 ≤ ρ)(hq:∀ z≤ d+1,∀ x:CanA D,trims z x→trims z (U x))(hk:∀ (i:Fin (d+1)) (p:BR (D i)), |‖U (Pi.single i p) i‖^2- ((Drift.lapPrice n i.val)^r*‖p‖)^2| ≤ ((Drift.lapPrice n i.val)^r)^2*(1-ρ⁻¹^2)*‖p‖^2) : Flyer (FeeF D U B) (B.val:ℝ) ρ:=by -- power precedence repair
       have hb:0<(B.val:ℝ):=by positivity
       let f(i:Fin (d+1)):=Drift.lapPrice n i.val^r; let v:ℝ:=(B.val:ℝ)^d; let a(i:Fin (d+1)):=(B.val:ℝ)^(d-i.val); let M(i):= route (FeeF D U B) i i; have hz(i)(p:BC (D i)): a i*ρ⁻¹*‖p‖ ≤ ‖M i p‖ ∧ ‖M i p‖≤ a i*ρ *‖p‖:=by
            have hf:0<f i:= (by unfold f Drift.lapPrice; positivity); let k:ℝ:= (f i)^2*(1-ρ⁻¹^2); let y:ℝ:= ‖route (εarm D U) i i p‖; have hP: |y^2-(f i*‖p‖)^2|≤k*‖p‖^2:= squared D _ i (f i) _ (hk i) p
            obtain ⟨hQ,hZ⟩:= δbill (norm_nonneg p) (show 0≤y from norm_nonneg _) hf hx (show k ≤ _ from le_rfl) hP; have hz : a i=v*f i:= (κside B h i).symm; have hg: ‖M i p‖=v*y:=(by unfold M;rw [sprY,norm_smul,Real.norm_of_nonneg (by positivity)]); rw[hz,hg]; have hV:0≤v:=(by unfold v; positivity); constructor <;> linarith only [mul_le_mul_of_nonneg_left hZ hV,mul_le_mul_of_nonneg_left hQ hV]
       refine ⟨fun i j hi=>?_ ,fun i=> (M i).opNorm_le_bound (by positivity) fun x=>(hz i x).2, fun i x=>?_⟩
       · ext1 p; rw [sprY,canvasP D U hq _ _ hi]; simp
       have ha:0 < a i:=by unfold a; positivity
       let A:= a i*ρ⁻¹; have hp:0<ρ:=zero_lt_one.trans_le hx; have he:0<A:=mul_pos ha (inv_pos.mpr hp);
       apply le_of_mul_le_mul_left _ he; refine (hz i x).1.trans ?_; change ‖M i x‖≤ a i*ρ⁻¹*((a i)⁻¹*ρ*‖M i x‖); exact le_of_eq (by field_simp)
end book
end YM.OPE.Dial
