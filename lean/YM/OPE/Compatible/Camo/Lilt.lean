import YM.OPE.Compatible.Camo.Hatch
/-! # caps on all horizontal costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m n M:ℕ}{ε v t c r z u s e a β C R A D:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:I→Host K T}{V B F z:I→ℝ}{l:Filter I}{b:I→ℕ}
variable (hp:Tendsto V l atTop)
include hp
lemma quickY (x:ℝ)(h:RateLE l V B 0): RateLE l V (fun i=> wealthV x (B i)) 0:= (RateLE.const (1:ℝ) hp).add ((h.add (RateLE.const _ hp) hp).norm) hp
variable (hz:RateLE l V (fun i=> (b i:ℝ)) 0)
include hz
lemma rtv : RateLE l V (fun i=> RtM (b i)) 0:=by
       unfold RtM ballCost; push_cast; have he := ((RateLE.const (16:ℝ) hp).mul hz).mono (show (0:ℝ)+0≤0 by norm_num); exact (((he.add he hp).add (RateLE.const 1 hp) hp).pow 4 hp).mono (by norm_num)
lemma CrownΛ (G:Gauge)(q:ℕ)(A:ℝ): RateLE l V (fun i=> crownG G (b i) A q) 0:= (((κ_growth _ _ hp _ hz).mul (RateLE.const _ hp)).mul (RateLE.const _ hp)).mono (by norm_num)
lemma hikeΛ (G:Gauge)(A:ℝ)(m i:ℕ): RateLE l V (fun j=> hikeP (J1+crownG G (b j) A) m i) 0:=by
        induction m generalizing i with
        | zero=> exact RateLE.const (1:ℝ) hp
        | succ m hm=> exact (((RateLE.const (1:ℝ) hp).add (CrownΛ hp hz G _ A) hp).mul (hm _)).mono (by norm_num)
variable {X:∀ i,Seats (L i).ForestQ}{q:∀ i,Sender (L i)} (x:∀ i,Site (L i).f)(U:I→ Train j)(Y:4 ≤ j){N: ChartRatio G}(hN:LocalRatio N)(H:StackP N r R β)(η:Phase)(hs:G.Simple)(h:∀ᶠ i in l,(L i).Rich s c e (B i) u C∧ Training (L i) (x i) (X i) (b i)∧ Funded (L i) (X i) (q i) (F i) k∧ ((X i).card:ℝ)≤ z i ∧ 0≤B i∧(L i).b=0)(hB:RateLE l V B 0)(ht:0<s)(hc:0≤c)(he:0<e)(hF:RateLE l V F 0)(hZ:RateLE l V z 0)
include H hs h ht hc he hN η hB hZ hF
abbrev Υden (L:Host K T)(U:Train j)(Y:4 ≤ j):Measure (Bid.Dir G L.c):= quart (Vessel K.K U G L.c Y) (Chart.tangent G (Body 1 L.c))
local notation "f₀"=> fun i=> Censor (L i) (q i) N η (x i) (b i)
set_option quotPrecheck false
local notation "Πμ"=>fun i=> Υden (L i) (U i) Y
local notation "A!"=> ((terra_money K.K Y).choose+1)
lemma ΥΨ : Grain (Πμ) l V (f₀) 0:=by
        obtain ⟨D,n,hD,hP⟩:= wC G s c u C β k; let p(i):= wealthV β (B i)*D; let f(i:I):= Ūfee (p i) n (b i) (z i) (F i); have he' : RateLE l V f 0:= (((quickY hp β hB).mul (RateLE.const D hp)).mul (((RateLE.const (1:ℝ) hp).add ((((rtv hp hz).norm).add hZ.norm hp).add hF.norm hp) hp).pow n hp)).mono (by norm_num)
        intro j hj; refine ⟨_,(he'.mul (hikeΛ hp hz G A! n j)).mono (by simp),?_⟩; filter_upwards [h] with i hi; obtain ⟨hi,hV,hy,hX,hZ,ha⟩:=hi; obtain ⟨hu,hI⟩:= Seat_V (L:=L i) (U i) Y
        exact Parad (x i) _ hN H η hs ha hi ht hc he hZ hX hV hy hI hu (hP (B i)) (mul_nonneg (show 0≤wealthV β (B i) from (by unfold wealthV; positivity)) hD) _ j hj
variable (hu:0<u)
include hu
omit hz
lemma ΥMotion (hx: RateLE l V (fun i=> burst (Gov s u/2) (b i)) t): Grain (Πμ) l V (fun i=> Censor (L i) (q i) N η (x i) (b i)-skry (GPY (L i) (q i) N) η) t:=by
        obtain ⟨D,n,hD,hT⟩:=w45F G s c u C β k; let p(i):= wealthV β (B i)* D; let Y'(i):= Ywall (Gov s u/2) (z i) (F i) (p i) n (b i); have hp': RateLE l V Y' t:= ((hx.mul ((quickY hp β hB).mul (RateLE.const D hp))).mul (((RateLE.const (1:ℝ) hp).add (hZ.norm.add hF.norm hp) hp).pow n hp)).mono (by simp)
        intro j hj; let Z:=Gov_price ht hu; refine ⟨_,(((hp'.mul (RateLE.const ((1-Real.exp (-(Gov s u/2)))⁻¹) hp)).mul (RateLE.const (Noble G n A! Z.1 j) hp)).mono (by simp)),?_⟩; filter_upwards [h] with i hi; obtain ⟨hi,hV,hO,hX,hU,hW⟩:=hi; obtain ⟨hz',hH⟩:= Seat_V (L:=L i) (U i) Y; exact harvest_M (x i) _ hN hO H η hs hW hi ht hc he hU hX hH hz' (hT (B i)) (mul_nonneg (show 0≤wealthV β (B i) from (by unfold wealthV; positivity)) hD) _ hV j hj
end
end YM.OPE.Borealis.Galea
