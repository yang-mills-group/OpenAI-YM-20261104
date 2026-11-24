import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Rooms
import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Originals
/-! # Physical LogTrace purchases on this tree. Adapted directly from
`YM/Integration/WilsonPublicForkStage`. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork.Chart
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open Node
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J] {P:Prescription F.sector.derivatives}

local notation "nearSet" => Flash259HorizonFork.near I J
local notation "outerSet" => Flash259HorizonFork.outer I J
local notation "tree" => Flash259HorizonFork.frame I J
def bare {α:Type}:Fin 0 → α:=Fin.elim0

private theorem restored {b n c u:ℝ}(hb:0<b)(h:u ≤ c*(n/b)) : b*u ≤ c*n:= by
  calc _ ≤ b*(c*(n/b)):=mul_le_mul_of_nonneg_left h hb.le
       _=_:=by field_simp

theorem inner (bank:LogTrace F P)(p:Node I J → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠr:ℝ in 𝓝[>]0,∀(t:ℝ)(x:I→E4)(o:E4)(z:J→E4),(∀i,‖x i‖ ≤ M) → (∀i j,i≠j→δ≤‖x i-x j‖) → 
      r^(load p)*‖coalesce P nearSet (sites o r t x z) p child w‖  ≤  badge r^k*r^w.1:=by
  obtain ⟨k,h⟩:=bank.terms ↥nearSet (crop p nearSet) δ M dp mn w
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with r issued pos
  intro t x o z hx sep
  have bill:=(issued (crop (sites o r t x z) nearSet) o
    (Flash259HorizonFork.inner o pos hx sep)).2
  rw [innerdeg] at bill
  exact restored (pow_pos pos _) bill

theorem outside (bank:LogTrace F P)(p:Node I J → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(o:E4)(z:J→E4),Ready r t M δ x z → ∀v:Viewers F,
      t^(w.1+duty p)*‖flux P (spectator F v) outerSet
          (sites o r t x z) (update p child (P.letter w)) base (bare:Fin 0 → E4) bare 0‖ ≤ badge t^k*t:=by
  let b:=outerSet
  let u:=update p child (P.letter w)
  obtain ⟨k,h⟩:=bank.horizons ↥b (Fin 0) (crop u b) bare δ M 1 dp mn zero_lt_one 0
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r x o z hz v
  have he:ClearOf o (bare:Fin 0 → E4) 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:= (issued (crop (sites o r t x z) b) bare o
    (Flash259HorizonFork.outside o hz mn dp.le) he).2.2.phaseBound v
  change _ ≤ badge t^k*(t^(0+1)/t^sigma (crop (update p child (P.letter w)) outerSet)) at bill
  rw [outerdeg,pow_one] at bill
  exact restored (pow_pos pos _) bill

theorem full (bank:LogTrace F P)(p:Node I J → C.book.Token){M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(o:E4)(z:J→E4),Ready r t M δ x z → ∀v:Viewers F,
      mass p r t*‖flux P (spectator F v) (tree).leaves
        (sites o r t x z) p base (bare:Fin 0 → E4) bare 0‖ ≤ t*(badge t*badge r)^k:=by
  obtain ⟨k,h⟩:=bank.testing tree p (bare:Fin 0 → C.book.Token) 0 M δ 1 mn dp zero_lt_one
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r x o z hz v
  let sites':=sites o r t x z
  let rad:Node I J→ℝ:=radius r t
  have convoy:=Flash259HorizonFork.convoy o hz mn dp.le
  have he:ClearOf (sites' (tree).root) (bare:Fin 0 → E4) 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:=(issued sites' rad bare rfl convoy he k le_rfl).ready.phaseBound v
  have wager:=convoy.sizes.fee_pos (b:=(tree).leaves) p 1 (tree).initial
  have eq:=convoy.sizes.reward_eq 1 p
  have cost:=mul_le_mul_of_nonneg_left bill wager.le
  change (tree).fee p rad (tree).leaves (tree).root 1*
      ‖flux P (spectator F v) (tree).leaves sites' p base (bare:Fin 0 → E4) bare 0‖ ≤ _ at cost
  rw [Arboreal.listPrice,←mul_assoc,mul_comm ((tree).fee ..) ((tree).tariff ..),eq,one_mul] at cost
  change _ ≤ (Arboreal.prestige tree (radius r t))^k at cost
  rw [Flash259HorizonFork.prestige] at cost
  change (tree).fee p (radius r t) (tree).leaves (tree).root 1*_ ≤ _ at cost
  rw [Flash259HorizonFork.fee,pow_one] at cost
  have paid:=mul_le_mul_of_nonneg_left cost pos.le
  rwa [←mul_assoc,mul_div_cancel₀ (mass p r t) pos.ne'] at paid

set_option maxHeartbeats 800000 in
theorem joint (bank:LogTrace F P)(p:Node I J→C.book.Token)(h:ℕ)(a:Mode F.sector.derivatives)
    (zero:a.1=0){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(o:E4)(z:J→E4),Ready r t M δ x z → 
      mass p r t*‖coalesce P (tree).leaves (sites o r t x z) p base a-
        ∑b∈bands F.sector.derivatives h,coalesce P nearSet (sites o r t x z) p child b*
          coalesce P outerSet (sites o r t x z) (update p child (P.letter b)) base a‖
        ≤ (badge t*badge r)^k*(r/t)^(h+1):=by
  obtain ⟨k,hk⟩:=WilsonThermometerWeakNestedChild.original F bank tree p a (fun _=>h)
    child Flash259HorizonFork.middle M δ mn dp
  refine ⟨k,hk.mono ?_⟩
  intro t available r x o z hz
  have rate:=available (sites o r t x z) (radius r t) rfl (Flash259HorizonFork.convoy o hz mn dp.le)
  have held (de:DecidableEq (Node I J)):(tree).live (@Finset.erase (Node I J) de (tree).zones child)=outerSet:=by
    ext u;cases u <;> simp [Arboreal.live,frame,outer,rim]
  rw [Flash259HorizonFork.fee,zero,pow_zero,div_one,
     Flash259HorizonFork.prestige,ratio,incoming,held] at rate
  change _≤(badge t*badge r)^k*(r/t)^(h+1) at rate
  convert rate using 1
  congr 3
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg₂ (·*·)
  · rfl
  · apply congrArg (fun pp=>coalesce P outerSet (sites o r t x z) pp base a)
    funext j
    by_cases hj:j=child
    · subst j;simp [Function.update]
    · simp [Function.update,hj]

end YM.OPE.Flash259HorizonFork.Chart
end
