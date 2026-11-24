import YM.Integration.WilsonPublicForkRooms
import YM.Integration.WilsonThermometerWeakNestedChild

/-! Three physical charges before the real two-scale reading: the raw child
kernel, its surviving sibling, and the genuinely joint outer remainder. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkStage
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open WilsonPublicForkGeometry WilsonPublicForkGeometry.Node WilsonPublicForkRooms
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I:Type} [Fintype I] {P:Prescription F.sector.derivatives}
local notation "sites" => WilsonPublicForkGeometry.position
local notation "nearSet" => WilsonPublicForkGeometry.near I
local notation "outerSet" => WilsonPublicForkGeometry.outer I
local notation "tree" => WilsonPublicForkGeometry.frame I
def bare {α:Type}:Fin 0 → α:=Fin.elim0

private theorem restored {b n c u:ℝ}(hb:0<b)(h:u ≤ c*(n/b)) : b*u ≤ c*n:= by
  calc _ ≤ b*(c*(n/b)):=mul_le_mul_of_nonneg_left h hb.le
       _=_:=by field_simp

theorem inner (bank:LogTrace F P)(p:Node I → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠr:ℝ in 𝓝[>]0,∀(t:ℝ)(x:I→E4)(z:E4),(∀i,‖x i‖ ≤ M) → (∀i j,i≠j→δ≤‖x i-x j‖) → 
      r^(load p)*‖coalesce P nearSet (sites r t x z) p child w‖  ≤  badge r^k*r^w.1:=by
  obtain ⟨k,h⟩:=bank.terms ↥nearSet (crop p nearSet) δ M dp mn w
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with r issued pos
  intro t x z hx sep
  have bill:=(issued (crop (sites r t x z) nearSet) 0
    (WilsonPublicForkRooms.inner pos hx sep)).2
  rw [innerdeg] at bill
  exact restored (pow_pos pos _) bill

theorem outside (bank:LogTrace F P)(p:Node I → C.book.Token)(w:Mode F.sector.derivatives)
    {M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(z:E4),‖z‖ ≤ M → δ ≤ ‖z‖ → ∀v:Viewers F,
      t^(w.1+(p far).1)*‖flux P (spectator F v) outerSet
          (sites r t x z) (update p child (P.letter w)) base (bare:Fin 0 → E4) bare 0‖ ≤ badge t^k*t:=by
  let b:=outerSet
  let u:=update p child (P.letter w)
  obtain ⟨k,h⟩:=bank.horizons ↥b (Fin 0) (crop u b) bare δ M 1 dp mn zero_lt_one 0
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r x z hz sep v
  have he:ClearOf (0:E4) (bare:Fin 0 → E4) 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:= (issued (crop (sites r t x z) b) bare 0
    (WilsonPublicForkRooms.outside pos mn hz sep) he).2.2.phaseBound v
  change _ ≤ badge t^k*(t^(0+1)/t^sigma (crop (update p child (P.letter w)) outerSet)) at bill
  rw [outerdeg,pow_one] at bill
  exact restored (pow_pos pos _) bill

theorem full (bank:LogTrace F P)(p:Node I → C.book.Token){M δ:ℝ}(mn:0 ≤ M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(z:E4),0<r → r ≤ t → (∀i,‖x i‖ ≤ M) → ‖z‖ ≤ M → 
      2*δ ≤ ‖z‖ → (∀i j,i≠j→δ≤‖x i-x j‖) → r*M ≤ t*δ → ∀v:Viewers F,
      mass p r t*‖flux P (spectator F v) (tree).leaves
        (sites r t x z) p base (bare:Fin 0 → E4) bare 0‖ ≤ t*(badge t*badge r)^k:=by
  obtain ⟨k,h⟩:=bank.testing tree p (bare:Fin 0 → C.book.Token) 0 M δ 1 mn dp zero_lt_one
  refine ⟨k,?_⟩
  filter_upwards [h,self_mem_nhdsWithin] with t issued pos
  intro r x z hr rt hx hz fz sep room v
  let sites':=sites r t x z
  let rad:Node I→ℝ:=radius r t
  have convoy:=actual hr rt mn dp.le hx hz fz sep room
  have he:ClearOf (sites' (tree).root) (bare:Fin 0 → E4) 1:=⟨fun i=>Fin.elim0 i,fun i=>Fin.elim0 i⟩
  have bill:=(issued sites' rad bare rfl convoy he k le_rfl).ready.phaseBound v
  have wager:=convoy.sizes.fee_pos (b:=(tree).leaves) p 1 (tree).initial
  have eq:=convoy.sizes.reward_eq 1 p
  have cost:=mul_le_mul_of_nonneg_left bill wager.le
  change (tree).fee p rad (tree).leaves (tree).root 1*
      ‖flux P (spectator F v) (tree).leaves sites' p base (bare:Fin 0 → E4) bare 0‖ ≤ _ at cost
  rw [Arboreal.listPrice,←mul_assoc,mul_comm ((tree).fee ..) ((tree).tariff ..),eq,one_mul] at cost
  change _ ≤ (Arboreal.prestige tree (radius r t))^k at cost
  rw [WilsonPublicForkRooms.prestige] at cost
  change (tree).fee p (radius r t) (tree).leaves (tree).root 1*_ ≤ _ at cost
  rw [WilsonPublicForkRooms.fee,pow_one] at cost
  have paid:=mul_le_mul_of_nonneg_left cost pos.le
  rwa [←mul_assoc,mul_div_cancel₀ (mass p r t) pos.ne'] at paid

set_option maxHeartbeats 800000 in
theorem joint (bank:LogTrace F P)(p:Node I→C.book.Token)(h:ℕ)(a:Mode F.sector.derivatives)
    (zero:a.1=0){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x:I→E4)(z:E4),0<r → r≤t → (∀i,‖x i‖≤M) → ‖z‖≤M →
      2*δ≤‖z‖ → (∀i j,i≠j→δ≤‖x i-x j‖) → r*M≤t*δ →
      mass p r t*‖coalesce P (tree).leaves (sites r t x z) p base a-
        ∑b∈bands F.sector.derivatives h,coalesce P nearSet (sites r t x z) p child b*
          coalesce P outerSet (sites r t x z) (update p child (P.letter b)) base a‖
        ≤ (badge t*badge r)^k*(r/t)^(h+1):=by
  obtain ⟨k,hk⟩:=WilsonThermometerWeakNestedChild.original F bank tree p a (fun _=>h)
    child middle M δ mn dp
  refine ⟨k,hk.mono ?_⟩
  intro t available r x z hr rt hx hz fz sep room
  have rate:=available (sites r t x z) (radius r t) rfl (actual hr rt mn dp.le hx hz fz sep room)
  have held (de:DecidableEq (Node I)):(tree).live (@Finset.erase (Node I) de (tree).zones child)=outerSet:=by
    ext u;cases u <;> simp [Arboreal.live,frame,outer]
  rw [WilsonPublicForkRooms.fee,zero,pow_zero,div_one,
     WilsonPublicForkRooms.prestige,ratio,incoming,held] at rate
  change _≤(badge t*badge r)^k*(r/t)^(h+1) at rate
  convert rate using 1
  congr 3
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg₂ (·*·)
  · rfl
  · apply congrArg (fun pp=>coalesce P outerSet (sites r t x z) pp base a)
    funext j
    by_cases hj:j=child
    · subst j;simp [Function.update]
    · simp [Function.update,hj]

end YM.Integration.WilsonPublicForkStage
end
