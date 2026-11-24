import YM.FormalOPE.RG10.Horizon.Matrix

/-!
# Rowwise Gram inverse bounds with Q-critical through-order precision
Exactly one exponential cost per weight; not assuming coefficient sizes for perturbed Gram but
provided the REAL scale law with kinetic convention. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Apertures
open Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries
variable {G:Gauge}{F:Frames G}{R:Rails F} {P:Plan F}{Y:Drivers}{Z:Patience P Y} (h:Street Z R)(hc:∀ n,Continuous (fun s=>coeff n (R.flow.psi s)))
namespace Halo
variable (B:Halo)(d:ℕ)
local notation "θ" => R.flow.warp
local notation "W" => Deck.price F d
local notation "ρ" => R.route d
local notation "J₁" => Deck F d
private lemma vendors (M:ℝ→Matrix J₁ J₁ fps)(N:ℝ→Matrix J₁ J₁ fps)
    (hM:∀ r i j, Polys (fun t=>coeff r (M t i j)))(hN:∀ r i j,Polys (fun t=>coeff r (N t i j))) (r i j):Polys (fun t=>coeff r ((M t * N t) i j)):= by
 simp_rw [Matrix.mul_apply,map_sum,coeff_mul]; apply Polys.sum; intro a _; apply Polys.sum; intro n _; exact Polys.muls (hM _ _ _) (hN _ _ _)
variable (hδ:∀ n j k,Continuous (fun s=> coeff n ((R.route d).train s j k)))
include h hδ hc
theorem expense_front (n:ℕ) (i j: J₁): Polys (fun t=> Real.exp (t * W i) * coeff n (B.Lens R Z d t i j)):= by
 let M (t:ℝ) := (ρ).lift t * B.look R Z d; have he(t:ℝ) : (B.Lens R Z d t i j)= C (Real.exp (-t * W i)) * (θ (-t) (M t i j)) := by
    have hx : R.drive t d * B.look R Z d= Matrix.diagonal (fun i:J₁=>C (Real.exp (-t* W i))) * M t:= by
       unfold M; rw [← Matrix.mul_assoc];
       congr 1; ext i j:1; rw [Matrix.diagonal_mul]; exact (ρ).lift_entrance t i j
    rw [B.launch R Z d t h,hx]; simp [Matrix.diagonal_mul,R.flow.at_const]
 have hv(t:ℝ): Real.exp (t*W i) * Real.exp (-t*W i) =1:= by simp [Real.exp_neg]
 simp_rw [he,coeff_C_mul,← mul_assoc,hv,one_mul]
 have hp r: Polys (fun t=>coeff r (M t i j)):= vendors d _ (fun _=> B.look R Z d) (ρ|>.uniform_lift hδ) (fun _ _ _=>Polys.const _) ..
 simpa only [neg_neg] using! (Polys.stretch (R.ok.fares hc (n:=n) (f:=fun t=>M (-t) i j) (fun i _=> (hp i).stretch))) -- precedence
omit h in
theorem expense_back (n:ℕ) (i j:J₁) : Polys (fun t=> Real.exp (-t * W j)* coeff n (B.invertAt R Z d t i j)) := by
 let M(t:ℝ) := ((B.look R Z d)⁻¹.map (θ (-t))) * ((R.route d).lift (-t));
 have he t: external R d t= (ρ).lift (-t) * Matrix.diagonal (fun j=> C (Real.exp (t* W j))) := by
   ext a b:1; rw [Matrix.mul_diagonal]; by_cases H: W a=W b
   · change (ρ).drive _ _ _= _; rw [Passe.lift_entrance,neg_neg,H,mul_comm];
   rw [external,Rails.drive, Passe.station_block (ρ) (-t) a b H,Passe.lift_layer (ρ) (-t) a b H,zero_mul]
 have hf (t:ℝ) : Real.exp (-t* W j) * Real.exp (t* W j)=1:= by simp [Real.exp_neg]
 have hh (t:ℝ) : B.invertAt R Z d t = M t * Matrix.diagonal (fun j=> C (Real.exp (t* W j))) := by rw [invertAt,he,← Matrix.mul_assoc];
 simp_rw [hh,Matrix.mul_diagonal,mul_comm _ (C _),coeff_C_mul,← mul_assoc,hf,one_mul];
 apply vendors
 · intro r i j; exact (Polys.stretch (R.ok.fares hc (n:=r) (ht:=fun x (_:x≤r)=>Polys.const _) (f:= fun _=>(B.look R Z d)⁻¹ i j)))
 intro r i j; exact ((ρ).uniform_lift hδ r i j).stretch
end Halo
end YM.FormalOPE.RG10.Apertures
