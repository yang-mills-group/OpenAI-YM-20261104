import YM.Juniper.Bright.Fusion
/-!
 # Composite receipt with PRESERVED K/seam/sqrt alarms

 Beyond `.completed`, including cut estimate for arbitrary k used
 with Desirable. Full activities $W$ distortion paid by `Ξ.markΦ`. `High`
 retains designation-root tests, earns reserve independent of positions.
 NOTE it may keep some old $.inl E$ in LOW label output: its longitudinal
 kernel weight is still small but unless prove separately, DON'T estimate flat
 for that. The legacy needs its special transfer or inspection at ended visits.
 
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G} {S: StepData c f} {T: Tube G S} {R : Rep G f}
    {W μ x C A v r a s q B d M i γ:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W} {I:Cash W x μ L Q o C T R}
    {j n k b: ℕ}
variable (Ξ: Captain I j s d v M A q r B γ k χ) (hD:1 ≤ grow G L x)(h:Desirable n Ξ.conduit)(ha:Armada Q L μ a x i B j k)
    (h₁: degreePrice (radiusB x) (grow G L x * (Q.costs L μ 1 x 0).rootHit) Q.δ ≤ 1/2)
    (h₂: degreePrice (radiusB x) (grow G L x * salary Q L μ B x j k) i ≤ 1/2)
local notation "D" => (grow G L x)
local notation "λ*"=> boltKey S (welfare n c f)
local notation "λ**" => strength I (D) (λ*)
include Ξ hD h h₁ h₂ ha
lemma guarantee : Trees.Ready I.smallAt (radiusB x) (fun s:I.ThinP=> λ** s.val * Ξ.stone s) (a+i) (D*salary Q L μ B x j k) i (1/2):=by
   let v:= contact Ξ.conduit hD k h h₁
   let e:= 2^j*B; have he:0≤e:=mul_nonneg (by positivity) Ξ.balance
   have hy s: 0 ≤ λ** s :=mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) (mul_nonneg (pow_nonneg (zero_le_one.trans hD) _) (Real.exp_nonneg _))) (Real.exp_nonneg _)
   refine ⟨mul_pos (zero_lt_one.trans_le hD) ((ha.purchases Ξ).1),ha.delta,h₂,by norm_num, fun z=>mul_nonneg (hy _) (Ξ.stone_pos _),fun i=> ?_⟩
   have ht:= budget_scale he (budget_pull (fun z:I.ThinP=> z.val) Subtype.val_injective (v i))
   refine budget_loosen (budget_mono ht (fun i=> ?_) (fun j=>?_)) ?_
   · dsimp only; split
     next hx=> exact mul_nonneg (mul_nonneg (hy _) (Ξ.stone_pos _)) (Real.exp_nonneg _)
     rfl
   · dsimp only; split
     next hx=>
       rw [if_pos (show i∈I.unionP j.val from hx), ← mul_assoc, mul_left_comm e, show e * Ξ.conduit.meant j.val k= Ξ.stone j from (by rw [Captain.stone,(show e=_ from rfl : e=2^_ * B),mul_assoc])]
       exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ha.little (Nat.cast_nonneg _))) (mul_nonneg (hy _) (Ξ.stone_pos _))
     exact ht.1 j
   unfold salary; have hv := ha.earned; have he := hD; unfold e; rw [mul_left_comm]; gcongr; linarith -- simp

omit hD h h₁ h₂ ha
variable (n)
def maturity (I:Cash W x μ L Q o C T R) (n:ℕ) (t:I.fragrances) := Height.breadth I t + ∑ i,bill S (boltKey S (welfare n c f)) (t.2 i).val
def ratesOf (I:Cash W x μ L Q o C T R) (n:ℕ) (z:I.fragrances) := D^maturity I n z * Real.exp (Q.mark L μ x*Height.overlap I z) * Real.exp (Q.ε*Height.depth I z)
lemma arrangement (z:I.fragrances): clusters I.seam (fun s:I.ThinP=> λ** s.val * Ξ.stone s) z.2 = ratesOf I n z * Ξ.design z:=by
   unfold ratesOf maturity breadth overlap Height.depth strength gust Captain.design clusters -- remove Depth
   simp only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,Nat.cast_sum,pow_add,mul_sum,Real.exp_sum]
   ring
variable {n}
def high (I:Cash W x μ L Q o C T R) (n:ℕ) (t:I.fragrances) := n ≤ maturity I n t ∨ 1≤Height.overlap I t ∨ Pressure.Stores.till x / (L.val:ℝ) ≤ Height.depth I t
omit Ξ
include hD
lemma extract_income (hd: D^n ≤ Real.exp (Q.mark L μ x))(hk:D^n ≤Real.exp (Q.ε*(Pressure.Stores.till x / (L.val:ℝ))))(t:I.fragrances) (ht: high I n t) : D^n ≤ ratesOf I n t:= by
   dsimp only [ratesOf]; have he':=mul_nonneg Q.usable.le (show 0 ≤ Height.depth I t from sum_nonneg fun i _=> I.positive_volume _)
   have he:= I.laws.acquired.marked
   have hv : 1≤Real.exp (Q.mark L μ x * Height.overlap I t) := Real.one_le_exp (mul_nonneg (show 0≤Q.mark L μ x from he) (Nat.cast_nonneg _))
   have hy : 1 ≤ (grow G L x)^ maturity I n t := one_le_pow₀ hD
   have hp:= Real.one_le_exp he'
   rcases ht with h|h|h
   · exact (pow_le_pow_right₀ hD h).trans ((le_mul_of_one_le_right (zero_le_one.trans hy) hv).trans (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hy) (zero_le_one.trans hv)) hp))
   · exact hd.trans ((Real.exp_monotone (le_mul_of_one_le_right (show 0≤Q.mark L μ x from he) (show (1:ℝ)≤ Height.overlap I t from by exact_mod_cast h))).trans ((le_mul_of_one_le_left (zero_le_one.trans hv) hy).trans (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hy) (zero_le_one.trans hv)) hp)))
   exact hk.trans ((Real.exp_monotone (mul_le_mul_of_nonneg_left h Q.usable.le)).trans (le_mul_of_one_le_left (zero_le_one.trans hp) (one_le_mul_of_one_le_of_one_le hy hv)))
include hD h h₁ h₂ ha
include Ξ
lemma fortune (hK:D^n ≤ Real.exp (Q.mark L μ x))(hk:D^n ≤Real.exp (Q.ε*(Pressure.Stores.till x / (L.val:ℝ)))) (ℓ:ℕ):
    Ac.Hit (Captain.reachability (H:=I)) (radiusB x) (fun z=> if high I n z then Ξ.markΦ z ℓ else 0) a
        ((D^n)⁻¹*collars G i x j ℓ*(D*salary Q L μ B x j k*(1-1/2)⁻¹)) := by
  intro X
  let hF:=guarantee Ξ hD h ha h₁ h₂
  have ht:=log_hit_tail _ _ _ I.testS hF (add_nonneg ha.gain ha.delta.le) 0 X
  simp only [pow_zero,mul_one] at ht
  have hv :0 ≤ shiftG x:=by unfold shiftG; positivity
  have he:0≤collars G i x j ℓ:= by unfold collars; have he:=ha.delta; unfold polyPrice; positivity
  have hp':0<D:= zero_lt_one.trans_le hD
  have hp:= budget_scale (mul_nonneg (inv_nonneg.mpr (pow_nonneg hp'.le n)) he) ht
  refine budget_mono hp (fun z=> ?_) fun z=> ?_
  · dsimp only; split_ifs
    next => exact mul_nonneg (show 0≤Ξ.markΦ z ℓ from mul_nonneg (pow_nonneg (by positivity) _) (Ξ.pvc _)) (Real.exp_nonneg _)
    next => simp
    exact le_rfl
  dsimp only; split
  next hx=>
     by_cases hV : high I n z
     · rw [if_pos hV, if_pos (show 0 ≤ z.fst ∧ X∈unionOf I.smallAt z.snd from ⟨Nat.zero_le _,hx⟩),arrangement]
       let K:ℝ:= coverNumber (radiusB x) (Captain.reachability z); have hh:0≤K:= Nat.cast_nonneg _
       let z':=Real.exp (a*K); let A:=Ξ.design z
       change (shiftG x*(1+K))^(ℓ*j)* A * Real.exp (a*K) ≤ ((D^n)⁻¹*collars G i x j ℓ)*(ratesOf I n z*A*Real.exp ((a+i)*K))
       refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (extract_income hD hK hk z hV) (Ξ.pvc _)) (Real.exp_nonneg _)) (mul_nonneg (by positivity) he)) -- extract args
       have hh':= polynomial_cost ha.delta hh (ℓ*j)
       unfold collars; rw [mul_pow,add_mul,Real.exp_add]
       apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh' (pow_nonneg hv _)) (show 0≤A from Ξ.pvc z)) (Real.exp_nonneg _))
       apply le_of_eq; unfold polyPrice; field_simp
     rw [if_neg hV,zero_mul]; exact hp.1 z
  exact hp.1 z
end YM.Juniper.Bright
