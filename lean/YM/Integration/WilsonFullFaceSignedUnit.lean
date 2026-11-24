import YM.Integration.WilsonFullFaceSignedPower

/-! At the identity the small signed capture has a measured scalar. Price
its complete ordinary polynomial, including every proper product. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonFullFaceSignedUnit
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open Push.Local Planned.GuardedAtom Comparison.RG02.Cumulants Next.Foundations
open WilsonRootedKioskOccupiedSlip WilsonFullFaceSignedInterpolation
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {X ι ν : Type} {o : Fin 3→Site n} {P : Rep G n}
local notation "J" => Stock.census (Fin 3)

private theorem ordinary (w : Fin 3→ℝ) (hw : ∀j,0<w j) (s : (J).Mode) (a : Poly J)
    (quiet : a.part (J).quiet=0) {C : ℝ} (one : 1≤C)
    (each : ∀t : Hot (J),Poly.toll w t.val*‖a.part t.val‖≤C) :
    Poly.toll w s*‖(Poly.pass a).part s‖≤(Fintype.card (parts (J)).Mode:ℝ)*C^3 :=by
  rw [pass_partition _ quiet]
  have shard (q : (parts (J)).Mode) (ok : q∈shards (J) s) :
      Poly.toll w s*‖∏t∈q.val,a.part t.val‖≤C^3 :=by
    have split : Poly.toll w s=∏t∈q.val,Poly.toll w t.val:=by
      rw [←show unionOf q=s from (mem_filter.mp ok).2];exact prod_biUnion (parts_wise q)
    rw [split,norm_prod,←prod_mul_distrib]
    have muls : (∏t∈q.val,Poly.toll w t.val*‖a.part t.val‖) ≤ ∏_∈q.val,C :=
      prod_le_prod (fun t _=>mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun t _=>each t)
    have count : q.val.card≤3:=(WilsonCapturedPrimarySoftLoad.size ok).trans (by simpa using card_le_univ s.val)
    exact (muls.trans_eq (prod_const ..)).trans (pow_le_pow_right₀ one count)
  have bound:=mul_le_mul_of_nonneg_left (norm_sum_le (shards (J) s) (fun q=>∏t∈q.val,a.part t.val)) (Poly.worth hw s).le
  rw [mul_sum] at bound
  have total:=sum_le_sum shard
  simp only [sum_const,nsmul_eq_mul] at total
  refine (bound.trans total).trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (zero_le_one.trans one) _))
  exact_mod_cast card_le_univ (shards (J) s)

theorem priced (L : Lamps X ι G P.p o J) (B : Lamps X ν G P.p o J) (H : Hard X P.p P.activities.forced P.activities.K o J)
    (w : Fin 3→ℝ) (hw : ∀j,0<w j) {C e : ℝ} (ep : 0<e) (low : e≤1) (cpos : 0≤C)
    (model : L.Paid w P.p.B (P.p.supportExponent+2) C) (debt : B.Paid w P.p.B (P.p.supportExponent+2) e)
    (x : X) (s : (J).Mode) :
    let A : Gallery X (ι⊕ν) o P J :=⟨L.join B,H⟩
    let t:ℂ:=(P.eval (1:Config G n):ℂ)
    Poly.toll w s*‖t⁻¹*((A.density x 1).part s-t*(Poly.pass (bare L x 1)).part s)‖≤
      e*WilsonFullFaceSignedPower.inter*((Fintype.card (parts (J)).Mode:ℝ)*(C+3)^3) :=by
  intro A t
  have width : 0≤P.p.supportExponent+2:=by linarith only [P.p.exponent_pos]
  let z:ℂ:=(e:ℂ)
  have nz:z≠0:=by dsimp only [z];exact_mod_cast ep.ne'
  have normZ:‖z‖=e:=by simp [z,Real.norm_eq_abs,abs_of_pos ep]
  let node (j:Fin 4):=L.join (scale B ((j.val:ℂ)/z))
  have fee (j:Fin 4) : (node j).Paid w P.p.B (P.p.supportExponent+2) (C+3) :=by
    have scaled:=paid B ((j.val:ℂ)/z) w debt
    have price : ‖(j.val:ℂ)/z‖*e=(j.val:ℝ):=by rw [norm_div,Complex.norm_natCast,normZ];field_simp
    rw [price] at scaled
    have range : (j.val:ℝ)≤3:=by exact_mod_cast (show j.val≤3 by omega)
    exact (node j).loan_monotone (Lamps.joinPaid model scaled) (add_le_add_right range C)
  have l:=model.sums width hw x (1:Config G n)
  have b:=debt.sums width hw x (1:Config G n)
  let tail:=z⁻¹ • B.log x (1:Config G n)
  have off:tail.part (J).quiet=0:=by dsimp only [tail];rw [Poly.part_smul,B.quiet_of_hasSum x 1 b,mul_zero]
  have actual : (L.join B).log x 1=L.log x 1+z • tail:=by rw [Lamps.joinLog x 1 l b];simp [tail,smul_smul,nz]
  have nodes (j:Fin 4):(node j).log x 1=L.log x 1+(j.val:ℂ) • tail:=by
    unfold node
    rw [Lamps.joinLog x 1 l ((paid B ((j.val:ℂ)/z) w debt).sums width hw x 1),reading]
    simp [tail,smul_smul,div_eq_mul_inv]
  have clear : flags P.p.threshold (1:Config G n)=∅:=UVNext.CouplingReset.flags_one P.p
  have phase : P.eval (1:Config G n)=Real.exp (P.exponent 1):=by rw [Rep.eval,P.activities.gas_one (p:=P.p) clear,mul_one]
  have live : t≠0:=Complex.ofReal_ne_zero.mpr (phase ▸ Real.exp_ne_zero _)
  have whole : (t⁻¹) • A.density x 1=Poly.pass ((L.join B).log x 1):=by
    rw [Gallery.density,WilsonFirstReceivedGalleryRegular.clear A x 1 clear,mul_one,←phase,smul_smul,inv_mul_cancel₀ live,one_smul]
  have raw : bare L x (1:Config G n)=L.log x 1:=by
    apply tsum_congr
    intro a
    exact congrArg (Poly.send (L.mode a)) (sub_eq_zero.mp (healthy L x a 1 (one_healthy _ _ P.p.threshold_pos.le))).symm
  have found : t⁻¹*((A.density x 1).part s-t*(Poly.pass (bare L x 1)).part s) =
      z*∑j:Fin 4,coins z j*(Poly.pass ((node j).log x 1)).part s :=by
    have val:=congrArg (fun a:Poly J=>a.part s) whole
    rw [mul_sub,←mul_assoc,inv_mul_cancel₀ live,one_mul,raw,←Poly.part_smul,val,actual]
    rw [table s (by simpa using card_le_univ s.val) (L.log x 1) tail z (L.quiet_of_hasSum x 1 l) off]
    simp_rw [nodes]
  let K:=(Fintype.card (parts (J)).Mode:ℝ)*(C+3)^3
  have bounds (j:Fin 4): Poly.toll w s*‖(Poly.pass ((node j).log x 1)).part s‖≤K:=by
    apply ordinary w hw s _ ((node j).quiet_of_hasSum x 1 ((fee j).sums width hw x 1)) (by linarith only [cpos] : 1≤C+3)
    intro t
    obtain ⟨v,hv⟩:=t.property
    exact WilsonFirstReceivedGalleryRegular.occupied (node j) (fee j) width hw x 1 t.val v hv
  have total : Poly.toll w s*‖∑j:Fin 4,coins z j*(Poly.pass ((node j).log x 1)).part s‖≤WilsonFullFaceSignedRegular.factor e*K :=calc
    _ ≤ Poly.toll w s*∑j:Fin 4,‖coins z j*(Poly.pass ((node j).log x 1)).part s‖:=mul_le_mul_of_nonneg_left (norm_sum_le ..) (Poly.worth hw s).le
    _ = ∑j:Fin 4,‖coins z j‖*(Poly.toll w s*‖(Poly.pass ((node j).log x 1)).part s‖):=by
      rw [mul_sum];apply sum_congr rfl;intro j _;rw [norm_mul];ring
    _ ≤ ∑j:Fin 4,‖coins z j‖*K :=sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (bounds j) (norm_nonneg _)
    _ = _ :=(sum_mul ..).symm
  rw [found,norm_mul,normZ,mul_left_comm]
  have k0:0≤K:=mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by linarith only [cpos]) _)
  exact (mul_le_mul_of_nonneg_left (total.trans (mul_le_mul_of_nonneg_right
    (WilsonFullFaceSignedPower.bounded.choose_spec.2 e ⟨ep.le,low⟩) k0)) ep.le).trans_eq (mul_assoc ..).symm

end YM.Integration.WilsonFullFaceSignedUnit
