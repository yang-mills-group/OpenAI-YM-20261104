import YM.GradedFar.Orbit
/-!
# Supplementary physical log budget on compact whole moments

For (G.6)'s size (not seeking the extra O(1) at the particular use of G.1 in its
proof) it suffices even to use these rough costs directly from LogTrace. Scale slots by
`r^j`, formal prices independent. This will allow proving G.6 **also without compact H
comparison**, at the cost of some more log powers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Filter Function Set Finset Spec Table Extraction OPE OPE.Orbits OPE.Log
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J] (d:I→ℕ) (e:J→ℕ)
local notation "Φ" => Viewers F
variable {P:Prescription F.sector.derivatives} (hG:G.Simple) (bank:LogTrace F P) {M δ:ℝ} (hm:0 ≤ M) (hd:0<δ)

def ForEvery (M δ t:ℝ) (z:Φ×Launch I):=Tiny M δ t z.2
include bank hm hd hG
lemma compact_read (u:Labels S d): Sold (𝓝[>](0:ℝ)) (ForEvery F M δ) TagCost
    (fun r (_:Φ×Launch I)=>1/r^(∑i,d i)) (fun _ (z:Φ×Launch I)=> Orbits.moment (spectator F z.1) z.2.x u):=by
  let T (r:ℝ)(_z:Φ×Launch I):= 1/r^(∑i,d i)
  let f(z:Φ×Launch I) a := P.ope a z.2.x (names u) z.2.center*ZeroReading F P a none 0; let g z:= ∑ i∈bands F.sector.derivatives 0, f z i
  have ht (z:Φ×Launch I): g z=P.truncated (spectator F z.1) 0 z.2.x (names u) z.2.center vacant bare:=
    Finset.sum_congr rfl fun i hi=> congrArg (_*·) (zero_common F P hG i hi z.2.center z.1).symm
  have hS : Safe (𝓝[>]0) (ForEvery F M δ) TagCost T:= by simpa [T] using compact_pay d (ForEvery F M δ) 0
  have hs: Sold (𝓝[>]0) (ForEvery F M δ) TagCost T (fun _ z=> g z):=by
    refine Sold.sum (F':=fun i (_:ℝ) z=> f z i) hS ?_; intro i hi
    obtain ⟨k,h⟩:=bank.terms I (names u) δ M hd hm i; refine ⟨k,‖ZeroReading F P i none 0‖,norm_nonneg _,?_⟩
    filter_upwards [h] with r hr z hz
    specialize hr z.2.x z.2.center hz; dsimp only [f]; rw [norm_mul]
    have h:= hr.2; rw [Nat.eq_zero_of_le_zero ((full_bands ..).mp hi),pow_zero] at h
    exact (mul_le_mul_of_nonneg_right h (norm_nonneg _)).trans_eq (by rw [mul_comm,← mul_assoc]; rfl)
  let f' (r:ℝ)(z:Φ×Launch I):= Orbits.moment (spectator F z.1) z.2.x u - g z
  have he : Sold (𝓝[>]0) (ForEvery F M δ) TagCost T f':= by
    obtain ⟨k,h⟩:=bank.horizons _ (Fin 0) (names u) bare δ M 1 hd hm zero_lt_one 0
    refine ⟨k,1,zero_le_one,?_⟩
    filter_upwards [h,self_mem_nhdsWithin,(ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,hS]
      with r hr (hp:0<r) (hs:r≤1) h z hz
    have hh:= ((hr z.2.x vacant z.2.center hz ⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩).2.2).phaseBound z.1
    unfold f'; rw [one_mul, Orbits.observed, ht, renameWrite (Equiv.refl I) (z:=z.2.x) (w:=names u) (v:=names u)
      (spectate F z.1).laws.toSymmetric (tiny_inj hp hd hz) rfl rfl]; refine hh.trans ?_
    have hy :=(h z hz).1
    change badge r^k*(r^(0+1:ℕ)/r^(∑i,d i)) ≤ TagCost r z^k*(1/r^(∑i,d i))
    rw [pow_one]; change 1≤ badge r at hy; unfold TagCost; gcongr
  exact (he.add hS hs).congr (fun _ _=> sub_add_cancel ..)

variable (j:ℕ)
lemma parent_cost (u:S.Field j)(w:Labels S e) : ∃ k:ℕ, ∃ b:ℝ,0≤b ∧ ∀ᶠ t:ℝ in 𝓝[>]0,∀ o y, WithinRoom t M δ (beside (sole o) y) o →
    ∀v:Φ, ‖upon (spectator F v) j o y w u‖ ≤ b*badge t^k*(1/t^(j+∑i,e i)):=by
  obtain ⟨k,b,hb,H⟩:= compact_read F (Sum.elim (fun _:Unit=>j) e) hG bank hm hd (stages (sole u) w)
  refine ⟨k,b,hb,H.mono ?_⟩; intro t ht o y hz v; specialize ht (v,⟨beside (sole o) y,o⟩) hz
  change _ ≤ b*badge t^k*(1/t^∑ i, Sum.elim (fun _:Unit=>j) e i) at ht
  rw [Fintype.sum_sum_type] at ht; change _ ≤ b*badge t^k*(1/t^((∑ _:Unit,j) + ∑ i,e i)) at ht -- parentheses sum risk
  simp only [Fintype.sum_unique] at ht; exact ht
end YM.Integration.GradedFar.Fork
