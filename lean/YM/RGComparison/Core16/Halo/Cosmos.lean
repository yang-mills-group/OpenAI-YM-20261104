import YM.RGComparison.Core16.Lam.Range
/-!
# Thick seam budgets to integrate across all the given periods.
Edge measure choice all at physical periods incl winding. Λ(c) = elementary gauge-clock from Card. Taylor local field kernels can vary directly by phase; payment demands require TRUE projections to this one sector basis. All PP bounds real pre-form operation vs oriented representative.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Halo
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk Stage Push.Uniform Push.AbsoluteSums.Animals Lam
open PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {C F c f:Side}

-- use `chit axis b1` and Realty.G.Center `Strong normalization`; λ weighted stencil from incoming log jets (nondim local estimates, independent of physical torus p choices).

def ch (a:G.ColorIndex) (i:Site c): Operand G c:= ((i,0),a)
def wt (a b:Site c) : ℝ:= - (((lift (b-a) 1):ℤ):ℝ)^2 /2
def gaugeCard (a b:Site c)(d : ℕ):= (separation a b:ℝ)^d
lemma unit (a b:Site c) : |wt a b| ≤ gaugeCard a b 2:= by
    let u: ℤ:=lift (b-a) 1; have h:u.natAbs ≤ separation a b:= (component_le ..).trans_eq (separation_comm b a)
    have hx: (|u|:ℤ) ≤ (separation a b:ℕ) := by rw [← Int.natCast_natAbs]; exact_mod_cast h
    have hh : |(u:ℝ)| ≤ (separation a b:ℝ):=by rw [← Int.cast_abs]; exact_mod_cast hx
    unfold wt gaugeCard; rw [abs_div,abs_of_pos (show (0:ℝ)<2 from zero_lt_two), abs_neg, abs_of_nonneg (by positivity : 0≤(u:ℝ)^2)]; nlinarith only [pow_le_pow_left₀ (abs_nonneg (u:ℝ)) hh 2,sq_abs (u:ℝ),sq_nonneg (separation a b:ℝ),(show (u:ℝ) = (lift (b-a) 1:ℝ) from rfl)] -- opacity

def frontage (a: Site c)(F : Site c→Site c→ℝ)(k:ℕ):=∑ i∈neighbors k a, wt a i*F a i

def outs (F:Site c→Site c→ℝ)(x:Site c) := ∑ i,wt x i*F x i
def vol (c:Side):ℝ:= Fintype.card (Site c)
lemma vol_pos (c:Side): 0 < vol c:= Nat.cast_pos.mpr Fintype.card_pos

def assembly (F:Site c→ℝ):= (∑ x,F x)/vol c
def cache (F: Site c→ Site c→ ℝ):= assembly (outs F)

def tail (y:ℝ)(x:ℕ):= Real.exp (-y * x)
lemma payoff (y:ℝ)(x:ℕ):0<tail y x:= Real.exp_pos _
lemma prevail (a:ℝ) {n m:ℕ} (ha:0  ≤  a) (h:n ≤ m):tail a m ≤ tail a n:=Real.exp_monotone (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr h) (neg_nonpos.mpr ha))

def ceiling (k:ℕ)(α : ℝ):ℝ:= k.factorial/α^k
lemma umbrella {α:ℝ}(h:0<α)(k:ℕ):0 < ceiling k α:= by unfold ceiling; positivity
lemma momentCap {α:ℝ}(h:0<α)(k n:ℕ): (n:ℝ)^k * tail α n ≤ ceiling k α:= by
    let x:ℝ:=α*n; have hx:0 ≤ x:= mul_nonneg h.le (Nat.cast_nonneg _); have ht:= Real.pow_div_factorial_le_exp x hx k
    unfold tail; rw [neg_mul,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos x)]; rw [div_le_iff₀ (Nat.cast_pos.mpr k.factorial_pos)] at ht
    unfold ceiling; change _ ≤ _/α^k* Real.exp x; rw [div_mul_eq_mul_div,le_div_iff₀ (pow_pos h _)]; exact le_trans (le_of_eq ((mul_comm ..).trans ((mul_pow α (n:ℝ) k).symm))) (ht.trans_eq (mul_comm ..))
lemma cadence {α:ℝ}(F:Site c→Site c→ℝ){x:ℝ}(h:0<α)(hx:0≤x)(he:∀ i j,|F i j| ≤ x*Decay (3*α) i j) (a:Site c)(I:Support c)(k n:ℕ)(hd:∀ i∈I,n ≤ separation a i):
    ∑ i∈I, |F a i| * gaugeCard a i k ≤ x*(tail α n * (ceiling k α * countCost α)):=by
   let K:= ceiling k α; let b:= tail α n; have hk :0<K:= umbrella h k; have hb:0<b:= payoff ..
   have hf (i:Site c)(hi:i∈I): |F a i| * gaugeCard a i k ≤ (x*b*K)*Decay α a i:=by
       let q:= separation a i; let y:= tail α q; have hy:0<y:= payoff ..
       let v:= gaugeCard a i k; have hp :0≤v:= by unfold v gaugeCard; positivity
       refine (mul_le_mul_of_nonneg_right (he a i) hp).trans ?_
       rw [show Decay (3*α) a i = y^3 from ?_]; swap; unfold y tail Decay; rw [←Real.exp_nat_mul]; congr 1; unfold q; push_cast; ring
       change x*y^3*v ≤ _*y; calc
                   _ = x*((v*y)*y)*y := by ring
                   _ ≤ x*(K*b)*y:= by gcongr; exact momentCap h k q; exact prevail α h.le (hd _ hi)
                   _ = _:= by ring
   refine (sum_le_sum (fun i hi=> hf i hi)).trans ?_; calc
      _ ≤ x*b*K*(∑ i,Decay α a i):= by rw [← mul_sum]; refine mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> decay_pos ..|>.le)) ?_; positivity
      _ ≤ x*b*K*countCost α:=by gcongr; exact decay_count h a
      _ = _:=by unfold b K; ring
lemma temple {α:ℝ}(F:Site c→Site c→ℝ){x:ℝ}(h:0<α)(hx:0≤x)(he:∀ i j, |F i j| ≤ x*Decay (3*α) i j)(a: Site c)(I: Support c)(n:ℕ)(hI:∀ i∈I,n ≤ separation a i):
      |∑ i∈I, wt a i*F a i| ≤ x*(tail α n * (ceiling 2 α *countCost α)):= (abs_sum_le_sum_abs ..).trans ((sum_le_sum (f:=fun i=>|wt a i*F a i|) (fun i _=> (abs_mul ..).trans_le ((mul_le_mul_of_nonneg_right (unit a i) (abs_nonneg (F a i))).trans_eq (mul_comm ..)))).trans (cadence F h hx he a I 2 n hI))
lemma cancels {α:ℝ}(F:Site c→Site c→ℝ){x:ℝ}(h:0<α)(hx:0≤x)(he:∀ i j, |F i j| ≤ x*Decay (3*α) i j)(a: Site c)(n:ℕ):
    |outs F a-frontage a F n| ≤ x*(tail α n * (ceiling 2 α* countCost α)):=by
   unfold frontage outs; rw [← sum_sdiff (subset_univ (neighbors n a)),add_sub_cancel_right]; exact temple F h hx he a _ n fun i hi=> le_of_not_ge (mt (neighbors_mem ..).2 (mem_sdiff.mp hi|>.2)) -- not_ge types
end YM.RGComparison.Core16.Halo
