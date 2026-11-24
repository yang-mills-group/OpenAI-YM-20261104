import YM.Integration.WilsonThermometerWeakPairRooms
import YM.Integration.WilsonThermometerWeakPairTriangle

/-! Three physical charges before the real two-scale reading: the raw child
kernel, its surviving sibling, and the genuinely joint outer remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairStage
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open WilsonThermometerWeakPairFork WilsonThermometerWeakPairRooms
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {P:Prescription F.sector.derivatives}
local notation "sites" => WilsonThermometerWeakPairFork.position
def bare {α:Type}:Fin 0 → α:=Fin.elim0

private theorem restored {b n c u:ℝ}(hb:0<b)(h:u ≤ c*(n/b)) : b*u ≤ c*n:= by
  calc _ ≤ b*(c*(n/b)):=mul_le_mul_of_nonneg_left h hb.le
       _=_:=by field_simp

theorem inner (bank:LogTrace F P)(p:Fin 5 → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠr:ℝ in 𝓝[>]0,∀(t:ℝ)(x y z:E4),‖x‖ ≤ M → ‖y‖ ≤ M → δ ≤ ‖x-y‖ → 
      r^(load p)*‖coalesce P near (sites r t x y z) p 1 w‖  ≤  badge r^k*r^w.1:=by
  obtain ⟨k,h⟩:=bank.terms ↥near (crop p near) δ M dp mn w
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with r issued pos
  intro t x y z hx hy sep
  have bill:=(issued (crop (sites r t x y z) near) 0
    (WilsonThermometerWeakPairRooms.inner pos hx hy sep)).2
  rw [innerdeg] at bill
  exact restored (pow_pos pos _) bill

theorem outside (bank:LogTrace F P)(p:Fin 5 → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x y z:E4),‖z‖ ≤ M → δ ≤ ‖z‖ → ∀v:Viewers F,
      t^(w.1+(p 4).1)*‖flux P (spectator F v) WilsonThermometerWeakPairRooms.outside
          (sites r t x y z) (update p 1 (P.letter w)) 0 (bare:Fin 0 → E4) bare 0‖ ≤ badge t^k*t:=by
  let b:=WilsonThermometerWeakPairRooms.outside
  let u:=update p 1 (P.letter w)
  obtain ⟨k,h⟩:=bank.horizons ↥b (Fin 0) (crop u b) bare δ M 1 dp mn zero_lt_one 0
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r x y z hz sep v
  have he:ClearOf (0:E4) (bare:Fin 0 → E4) 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:= (issued (crop (sites r t x y z) b) bare 0
    (WilsonThermometerWeakPairRooms.outer pos mn hz sep) he).2.2.phaseBound v
  change _ ≤ badge t^k*(t^(0+1)/t^sigma (crop (update p 1 (P.letter w)) WilsonThermometerWeakPairRooms.outside)) at bill
  rw [outerdeg,pow_one] at bill
  exact restored (pow_pos pos _) bill

theorem full (bank:LogTrace F P)(p:Fin 5 → C.book.Token){M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x y z:E4),0<r → r ≤ t → ‖x‖ ≤ M → ‖y‖ ≤ M → ‖z‖ ≤ M → 
      2*δ ≤ ‖z‖ → δ ≤ ‖x-y‖ → r*M ≤ t*δ → ∀v:Viewers F,
      mass p r t*‖flux P (spectator F v) frame.leaves
        (sites r t x y z) p 0 (bare:Fin 0 → E4) bare 0‖ ≤ t*(badge t*badge r)^k:=by
  obtain ⟨k,h⟩:=bank.testing frame p (bare:Fin 0 → C.book.Token) 0 M δ 1 mn dp zero_lt_one
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r x y z hr rt hx hy hz fz sep room v
  let sites':=sites r t x y z
  let rad:=radius r t
  have convoy:=actual hr rt mn hx hy hz fz sep room
  have he:ClearOf (sites' frame.root) (bare:Fin 0 → E4) 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:=(issued sites' rad bare rfl convoy he k le_rfl).ready.phaseBound v
  have wager:=convoy.sizes.fee_pos (b:=frame.leaves) p 1 frame.initial
  have eq:=convoy.sizes.reward_eq 1 p
  have cost:=mul_le_mul_of_nonneg_left bill wager.le
  change frame.fee p rad frame.leaves frame.root 1*
      ‖flux P (spectator F v) frame.leaves sites' p 0 (bare:Fin 0 → E4) bare 0‖ ≤ _ at cost
  rw [Arboreal.listPrice,←mul_assoc,mul_comm (frame.fee ..) (frame.tariff ..),eq,one_mul] at cost
  change _ ≤ (Arboreal.prestige frame (radius r t))^k at cost
  rw [WilsonThermometerWeakPairRooms.prestige] at cost
  change frame.fee p (radius r t) frame.leaves frame.root 1*_ ≤ _ at cost
  rw [WilsonThermometerWeakPairRooms.fee,pow_one] at cost
  have paid:=mul_le_mul_of_nonneg_left cost pos.le
  rwa [←mul_assoc,mul_div_cancel₀ (mass p r t) pos.ne'] at paid

end YM.Integration.WilsonThermometerWeakPairStage
end
