import YM.Integration.WilsonThermometerWeakPairStage

/-! Engineering-normalized estimates for every projection of the two-level
tree and both scalar root subtractions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairResidual
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
open WilsonThermometerWeakPairFork WilsonThermometerWeakPairRooms
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {P:Prescription F.sector.derivatives}
local notation "sites" => WilsonThermometerWeakPairFork.position
local notation "farSet" => WilsonThermometerWeakPairRooms.outside

theorem root (bank:LogTrace F P)(p:Fin 5→C.book.Token)(h:ℕ)(a:Mode F.sector.derivatives)
    (zero:a.1=0){M δ:ℝ}(mn:0≤M)(dp:0<δ):
    ∃k:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(r:ℝ)(x y z:E4),0<r → r≤t → ‖x‖≤M → ‖y‖≤M → ‖z‖≤M →
      2*δ≤‖z‖ → δ≤‖x-y‖ → r*M≤t*δ →
      mass p r t*‖coalesce P frame.leaves (sites r t x y z) p 0 a-
        ∑b∈bands F.sector.derivatives h,coalesce P near (sites r t x y z) p 1 b*
          coalesce P farSet (sites r t x y z) (update p 1 (P.letter b)) 0 a‖
        ≤ (badge t*badge r)^k*(r/t)^(h+1):=by
  obtain ⟨k,hk⟩:=WilsonThermometerWeakNestedChild.original F bank frame p a (fun _=>h)
    1 middle M δ mn dp
  refine ⟨k,hk.mono ?_⟩
  intro t available r x y z hr rt hx hy hz fz sep room
  have rate:=available (sites r t x y z) (radius r t) rfl (actual hr rt mn hx hy hz fz sep room)
  have held (de:DecidableEq (Fin 5)):frame.live (@Finset.erase (Fin 5) de frame.zones 1)=farSet:=by
    have idem:de=(instDecidableEqFin 5):=Subsingleton.elim _ _
    rw [idem];exact WilsonThermometerWeakPairFork.pruned
  rw [WilsonThermometerWeakPairRooms.fee,zero,pow_zero,div_one,
     WilsonThermometerWeakPairRooms.prestige,ratio,WilsonThermometerWeakPairFork.inputs,held] at rate
  change _≤(badge t*badge r)^k*(r/t)^(h+1) at rate
  convert rate using 1
  congr 3
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg₂ (·*·)
  · rfl
  · apply congrArg (fun pp=>coalesce P farSet (sites r t x y z) pp 0 a)
    funext j
    by_cases hj:j=1
    · subst j;simp [Function.update]
    · simp [Function.update,hj]

theorem product {r t c e B K:ℝ}{d m w:ℕ}(hr:0<r)(rt:r≤t)(en:0≤e)(bn:0≤B)
    (kn:0≤K)(before:r^d*c≤B*r^w)(after:t^(w+m)*e≤K*t):
    (r^d*t^m)*(c*e)≤(B*K)*t:=by
  have ht:=hr.trans_le rt
  have positive:=pow_pos ht w
  apply le_of_mul_le_mul_left _ positive
  calc
    t^w*((r^d*t^m)*(c*e))=(r^d*c)*(t^(w+m)*e):=by rw [pow_add];ring
    _≤(B*r^w)*(K*t):=mul_le_mul before after (mul_nonneg (pow_nonneg ht.le _) en)
        (mul_nonneg bn (pow_nonneg hr.le _))
    _≤(B*t^w)*(K*t):=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le rt _) bn) (mul_nonneg kn ht.le)
    _=t^w*((B*K)*t):=by ring

end YM.Integration.WilsonThermometerWeakPairResidual
end
