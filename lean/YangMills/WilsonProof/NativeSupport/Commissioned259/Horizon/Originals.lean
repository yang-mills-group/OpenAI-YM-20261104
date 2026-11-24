import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Geometry
/-! # Step clone from `Integration/WilsonThermometerWeakNestedChild.original`
and the two algebraic helpers used in `...PublicForkOrdinary`.
Direct proofs copied with import minimized (names local to here); uses the original
mathematics/purchases. No hypothesis on plate payments added.
-/

set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork.WilsonThermometerWeakNestedChild
open Function Finset Filter Set Spec Table Extraction OPE OPE.Arboreal OPE.Arboreal.Mountain
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
  {I:Type}[Fintype I]{P:Prescription F.sector.derivatives}

theorem original (bank:LogTrace F P)(s:Arboreal I)(p:I→C.book.Token)
    (a:Mode F.sector.derivatives)(D:I→ℕ)(i:I)(one:s.middle s.zones={i})
    (M δ:ℝ)(mn:0≤M)(dp:0<δ):
    ∃order:ℕ,∀ᶠt:ℝ in 𝓝[>]0,∀(x:I→E4)(r:I→ℝ),r s.root=t→s.Convoy M δ r x→
      s.fee p r s.leaves s.root a.1*
        ‖coalesce P s.leaves x p s.root a-
          ∑v∈bands F.sector.derivatives (D i),
            coalesce P (s.inputs s.zones i) x p i v*
            coalesce P (s.live (s.zones.erase i)) x (update p i (P.letter v)) s.root a‖
        ≤ (Arboreal.prestige s r)^order*(s.ratioAt r i)^(D i+1):=by
  obtain ⟨order,paid⟩:=bank.tickets s p a D M δ mn dp
  refine ⟨order,paid.mono ?_⟩
  intro t issued x r hr h
  have mem:i∈s.middle s.zones:=by simp [one]
  have inside: i∈s.zones:=(mem_erase.mp mem).2
  have ne:i≠s.root:=(mem_erase.mp mem).1
  have border:s.Border s.zones i:=by
    intro j hj anc
    by_cases eq:j=s.root
    · exact (ne ((eq ▸ anc).excess)).elim
    · have jmem:j∈s.middle s.zones:=mem_erase.mpr ⟨eq,hj⟩
      simpa only [one,Finset.mem_singleton] using jmem
  have remains:s.middle (s.redact s.zones i)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    rw [Arboreal.middle,s.redact_one border] at hj
    obtain ⟨nr,ni,hz⟩:=show j≠s.root ∧ j≠i ∧ j∈s.zones from by simpa using hj
    have hmem:j∈s.middle s.zones:=mem_erase.mpr ⟨nr,hz⟩
    exact ni (Finset.mem_singleton.mp (one ▸ hmem))
  have calcRow:= (issued x r hr h order le_rfl).combination
  rw [Nest.contracted P border mem x p a D] at calcRow
  simp_rw [Nest.staging P x a (s.redacted s.Action mem) remains D, s.redact_one border] at calcRow
  have wage:= h.sizes.fee_pos (b:=s.leaves) p a.1 s.initial
  have total:= mul_le_mul_of_nonneg_left calcRow wage.le
  rw [Arboreal.listPrice,Arboreal.grace,one,sum_singleton] at total
  calc _≤_:=total
       _=_:=by
         rw [←mul_assoc,←mul_assoc,mul_comm (s.fee ..) (s.tariff ..),h.sizes.reward_eq a.1 p,one_mul]

end YM.OPE.Flash259HorizonFork.WilsonThermometerWeakNestedChild
end

set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork.WilsonThermometerWeakPairTriangle
open Finset Function OPE OPE.Arboreal
open scoped Classical BigOperators
variable {I J:Type}

theorem account (i:Finset I)(j:Finset J)(X:ℂ)(Y c:I→ℂ)(A v:J→ℂ)(B:I→J→ℂ):
    ‖X-∑u∈i,c u*Y u‖ ≤ ‖X-∑w∈j,A w*v w‖+
        ∑w∈j,‖A w-∑u∈i,c u*B u w‖*‖v w‖+
        ∑u∈i,‖c u‖*‖Y u-∑w∈j,B u w*v w‖:=by
  have transfer : ∑w∈j,∑u∈i,c u*B u w*v w = ∑u∈i,∑w∈j,c u*(B u w*v w):= by
    rw [sum_comm];simp only [mul_assoc]
  have amount:X-∑u∈i,c u*Y u=(X-∑w∈j,A w*v w)+
      (∑w∈j,(A w-∑u∈i,c u*B u w)*v w)-(∑u∈i,c u*(Y u-∑w∈j,B u w*v w)):=by
    simp_rw [sub_mul,mul_sub,sum_sub_distrib,sum_mul,mul_sum];rw [transfer];ring
  rw [amount]
  calc
    _≤(‖X-∑w∈j,A w*v w‖+‖∑w∈j,(A w-∑u∈i,c u*B u w)*v w‖)+
          ‖∑u∈i,c u*(Y u-∑w∈j,B u w*v w)‖:=
      (norm_sub_le ..).trans (add_le_add (norm_add_le ..) (le_refl _))
    _≤_:=by
      have left:=norm_sum_le j (fun w=>(A w-∑u∈i,c u*B u w)*v w)
      have right:=norm_sum_le i (fun u=>c u*(Y u-∑w∈j,B u w*v w))
      simp only [norm_mul] at left right
      exact add_le_add (add_le_add (le_refl _) left) right

end YM.OPE.Flash259HorizonFork.WilsonThermometerWeakPairTriangle
end

set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork.WilsonThermometerWeakPairBudget
open Finset
open scoped Classical BigOperators
variable {I J:Type}
theorem original (i:Finset I)(j:Finset J)(X:ℂ)(Y c:I→ℂ)(A v:J→ℂ)(B:I→J→ℂ)
    {W b q t:ℝ}(wp:0≤W)(bp:0≤b)(qp:0≤q)(tp:0≤t)
    (full:W*‖X-∑w∈j,A w*v w‖≤b*t)
    (outer:∀w∈j,W*‖A w-∑u∈i,c u*B u w‖≤b*q)
    (inner:∀u∈i,W*(‖c u‖*‖Y u-∑w∈j,B u w*v w‖)≤b*t):
    W*‖X-∑u∈i,c u*Y u‖ ≤ (1+(∑w∈j,‖v w‖)+i.card)*b*(t+q):=by
  have debt:=mul_le_mul_of_nonneg_left (WilsonThermometerWeakPairTriangle.account i j X Y c A v B) wp
  rw [mul_add,mul_add,mul_sum,mul_sum] at debt
  have D:∀w∈j,W*(‖A w-∑u∈i,c u*B u w‖*‖v w‖)≤(b*q)*‖v w‖:=fun w hw=>by
    rw [←mul_assoc];exact mul_le_mul_of_nonneg_right (outer w hw) (norm_nonneg _)
  have h:=debt.trans (add_le_add (add_le_add full (sum_le_sum D)) (sum_le_sum inner))
  rw [←mul_sum,sum_const,nsmul_eq_mul] at h
  have nn:0≤∑w∈j,‖v w‖:=sum_nonneg (fun w _=>norm_nonneg _)
  have tq:t≤t+q:=le_add_of_nonneg_right qp
  have qt:q≤t+q:=le_add_of_nonneg_left tp
  calc
    _≤_:=h
    _≤b*(t+q)+(b*(t+q))*(∑w∈j,‖v w‖)+(i.card:ℝ)*(b*(t+q)):=by gcongr
    _=_:=by ring

end YM.OPE.Flash259HorizonFork.WilsonThermometerWeakPairBudget
end

set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork.WilsonThermometerWeakPairResidual
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log
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

end YM.OPE.Flash259HorizonFork.WilsonThermometerWeakPairResidual
end
