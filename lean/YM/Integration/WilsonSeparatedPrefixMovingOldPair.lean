import YM.Integration.WilsonSeparatedPrefixMovingUnformed

/-! Recenter a genuinely born connected pair once. Its first birth, at a
shorter mesh, pays the moment incurred when the complete pair travels on
native rooted coordinates before the exterior arrives. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingOldPair
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

variable {G:Gauge}{D e u r l k:ℕ}{E W:Credit}

theorem promote {V:Era G ℝ}{x A:ℝ}(hx:0<x)(fit:x≤1)(income:Flush e u x V A):
    Flush e u 1 V ((x^u)⁻¹*A):=by
  have amount:0≤(x^u)⁻¹:=by positivity
  refine ⟨mul_nonneg amount income.1,?_⟩
  intro j hj r hr
  have ranked:=income.2 j hj r hr
  apply budget_minor (cap_scale ranked amount) (fun w=>mul_nonneg (hedge_nn zero_le_one _) (norm_nonneg _))
  intro w
  have cheap:hedge 0 1 u w≤(x^u)⁻¹*hedge 0 x u w:=by
    dsimp only [hedge,autumn];rw [←inv_pow,←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    rw [←div_eq_inv_mul,le_div_iff₀ hx]
    linarith only [fit]
  calc
    _≤((x^u)⁻¹*hedge 0 x u w)*‖V.2 j r w‖:=mul_le_mul_of_nonneg_right cheap (norm_nonneg _)
    _=_:=mul_assoc .. 

theorem rooted {V:Era G ℝ}{A:ℝ}(alive:Auth k V)(income:Flush e u 1 V A)
    (P:Patch)(φ:Rarity D)(x y:ℝ)(o:CellR)(central:(0:Cover)∈VisitsT φ x y o):
    Income V k e u (OrbP P φ x y o) ((9:ℝ)^u*A):=by
  refine ⟨alive,?_⟩
  intro δ hd j r hj
  have paid:=income.2 j hj r (Nat.zero_le _)
  have budget:Rent (OrbP P φ x y o) u (V.2 j r) ((9:ℝ)^u*A):=by
    apply budget_minor (cap_scale paid (show (0:ℝ)≤9^u by positivity))
      (fun w=>mul_nonneg (zero_le_one.trans (quoteT_pos w ..)) (norm_nonneg _))
    exact fun w=>(mul_le_mul_of_nonneg_right (spiralC P φ x y o 0 central w u) (norm_nonneg _)).trans_eq
      (mul_assoc ..)
  refine ⟨budget,budget,?_⟩
  rw [sub_self]
  exact Award.zero.more (mul_nonneg budget.C hd)

/-- Use the actual authenticated birth of A and B, including its scalar.
At any genuine later date this issues its center and parent profile. -/
theorem original (G:Gauge)(l r e u:ℕ)(E W:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E)(_dorm:Dormitory R (l+r) u W)
      (m i j N:ℕ)(_live:R.anchor ≤ m)(_mi:m ≤ i)(_ij:i ≤ j)(_top:j < N)(A B:Era G ℝ),
      let birth:=JoinGap R.draws R.paid j N l r A B
      let deposited:=cruises R.draws R.paid N (l+r) j i birth
      let x:=paceT R.draws.S m j
      Auth (l+r) birth → ∀ pay:ℝ,Flush e u x birth pay →
      ∀Z:ℝ,PadRank R i j Z →
        let fee:=C.buy Z*((x^u)⁻¹*pay)
        Auth (l+r) deposited ∧ Flush e u 1 deposited fee ∧
        ∀D:ℕ,∀ φ:Rarity D,∀P:Patch,∀s y:ℝ,∀o:CellR,(0:Cover)∈VisitsT φ s y o →
          Income deposited (l+r) e u (OrbP P φ s y o) ((9:ℝ)^u*fee):=by
  obtain ⟨C,carry⟩:=waveSeen G (l+r) e u E W
  refine ⟨C,?_⟩
  intro R dorm m i j N live mi ij top A B birth deposited x accepted pay funds Z room fee
  have lease:Escort R i j (fun _=>1):=by
    refine ⟨live.trans mi,ij,fun _ _ _=>zero_le_one,fun _ _ _=>le_rfl,?_⟩
    intro j' _ _ 
    exact div_le_self zero_le_one (by exact_mod_cast (R.draws.S.block j').pos)
  have grant:=promote (pace_pos R.draws.S m j) (pace_le _ (mi.trans ij)) funds
  have earned:Flush e u 1 deposited fee:=(carry R dorm i j (fun _=>1) j N N _ (max 0 (R.tempC j j)) Z
    lease room le_rfl top.le top.le (le_max_right _ _) _ _ (Fringed.same grant accepted (le_max_left _ _))).f_l
  have inherited:=cruising R.draws R.hG R.green ij top.le accepted
  exact ⟨inherited,earned,fun D Φ P s y o inside=>rooted inherited earned P Φ s y o inside⟩

end YM.Integration.WilsonSeparatedPrefixMovingOldPair
