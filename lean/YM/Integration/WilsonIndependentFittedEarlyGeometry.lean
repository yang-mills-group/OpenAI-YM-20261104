import YM.Integration.WilsonIndependentFittedForwardLength
import YM.Integration.WilsonIndependentExactPlate

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedEarlyGeometry
open Filter Lattice RG XSpace RegulatorIR RegulatorIR.Ledger WilsonCoeffUV
open WilsonIndependentEvenPassport (old young count)
open WilsonIndependentExactPlate (Requests)
open private speed pos scale from YM.Integration.WilsonOriginalPublicPlantedPeriod
open scoped BigOperators Topology Classical

theorem block {G:Gauge}(V:XSpace.Run)(a phase:ℕ)(ha:0<a)(hj:4≤phase)(i:Requests a)(A:Levels G)(s:ℕ)
    (acts:∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i→
      (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
        (WilsonIndependentExactPlate.S V a ha phase hj).pactP f)
    (j:ℕ)(early:s≤j)(late:j<s+count V a i.val):
    (A.S.block j).val≤V.ratio^(2*a):=by
  let N:=WilsonIndependentExactPlate.M V a i
  have hjN:j<s+N:=late
  let f:Flap (WilsonIndependentExactPlate.M V a):=⟨i,s+N-(j+1),by dsimp only [N] at *;omega⟩
  have address:s+(N-(f.offset+1))=j:=by dsimp only [f];omega
  have material:=congrArg Patch.L (acts f rfl)
  change A.S.block (s+(N-(f.offset+1)))=WilsonIndependentExactPlate.sizeL V a f at material
  rw [address] at material
  rw [material]
  change V.ratio^(if f.offset=0 then a+WilsonIndependentExactPlate.residue a f.volW else a)≤_
  apply Nat.pow_le_pow_right (by have:=V.large;omega)
  have rem:=Nat.mod_lt f.volW.val ha
  unfold WilsonIndependentExactPlate.residue
  split <;> omega

theorem height (S:Schedule)(m n:ℕ)(c:ℝ)(steps:∀i<n,Real.log (S.block (m+i)).val≤c):
    S.scale (m+n)-S.scale m≤(n:ℝ)*c:=by
  induction n with
  | zero=>simp
  | succ n ih=>
    rw [Nat.add_succ,S.scale_succ]
    push_cast
    have p:=ih (fun i hi=>steps i (by omega))
    have q:=steps n (by omega)
    linarith

def cost (V:XSpace.Run)(a:ℕ)(B:ℝ):ℝ:=
  max 1 B+V.reserve*(1+Real.log ((V.ratio^(2*a):ℕ):ℝ))

theorem housed {G:Gauge}(V:XSpace.Run)(a phase:ℕ)(ha:0<a)(hj:4≤phase)(i:Requests a)(A:Levels G)(s:ℕ)
    (acts:∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i→
      (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
        (WilsonIndependentExactPlate.S V a ha phase hj).pactP f)
    (stop:ℕ)(older:stop≤old V a i.val)(B z:ℝ)(home:z≤B):
    z+(A.S.scale (s+old V a i.val)-A.S.scale (s+stop))+
      ((old V a i.val-stop:ℕ):ℝ)≤cost V a B*(i.val:ℝ)^2:=by
  let c:=Real.log ((V.ratio^(2*a):ℕ):ℝ)
  let n:=old V a i.val-stop
  have ratio:1≤V.ratio:=(by have:=V.large;omega)
  have h1:(1:ℝ)≤((V.ratio^(2*a):ℕ):ℝ):=by exact_mod_cast Nat.one_le_pow _ _ ratio
  have pos:0≤c:=Real.log_nonneg h1
  have idx:1≤ i.val:=ha.trans_le i.prop
  have I:(1:ℝ)≤ i.val:=by exact_mod_cast idx
  have J:(1:ℝ)≤(i.val:ℝ)^2:=one_le_pow₀ I
  have endpoint:s+stop+n=s+old V a i.val:=by dsimp only [n];omega
  have lbound:=height A.S (s+stop) n c (fun l hl=>by
    apply Real.log_le_log (by exact_mod_cast (A.S.block (s+stop+l)).property)
    apply Nat.cast_le.mpr
    apply block V a phase ha hj i A s acts
    · omega
    change s+stop+l<s+(old V a i.val+young a i.val)
    omega)
  rw [endpoint] at lbound
  have nsought:n≤V.reserve*i.val*i.val:=(Nat.sub_le ..).trans (Nat.div_le_self ..)
  have ncast:(n:ℝ)≤(V.reserve:ℝ)*(i.val:ℝ)^2:=by
    obtain eq:=Nat.cast_le (α:=ℝ).mpr nsought
    simpa only [Nat.cast_mul,pow_two,mul_assoc] using eq
  have stair:=mul_le_mul_of_nonneg_right ncast (by linarith:0≤1+c)
  have bn:0≤ max 1 B:=zero_le_one.trans (le_max_left ..)
  have rent:B≤ max 1 B*(i.val:ℝ)^2:=(le_max_right ..).trans (le_mul_of_one_le_right bn J)
  change z+_+(n:ℝ)≤(max 1 B+(V.reserve:ℝ)*(1+c))*(i.val:ℝ)^2
  nlinarith only [home,lbound,stair,rent]

theorem payment (V:XSpace.Run)(C:WilsonCoeffUV.Bank.Credit)(B η:ℝ)(posη:0<η):
    ∀ᶠ j:ℕ in atTop,∀y:ℝ,0≤y→y≤B*(j:ℝ)^2→C.buy y≤(V.step j).spacing^(-η):=by
  let b:=max 1 B
  have b0:0≤b:=zero_le_one.trans (le_max_left ..)
  have cp:0≤C.x:=zero_le_one.trans C.good
  have cpos:0<η*speed V:=mul_pos posη (pos V)
  have end₀:Tendsto (fun x:ℝ=>x^(2*C.d)*Real.exp (-(η*speed V*x))) atTop (𝓝 0):=by
    simpa only [Real.rpow_natCast,neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((2*C.d:ℕ):ℝ) (η*speed V) cpos
  have tail:Tendsto (fun j:ℕ=>C.x*b^C.d*((j:ℝ)^(2*C.d)*Real.exp (-(η*speed V*(j:ℝ))))) atTop (𝓝 0):=by
    simpa using (end₀.comp tendsto_natCast_atTop_atTop).const_mul (C.x*b^C.d)
  filter_upwards [tail.eventually (ge_mem_nhds (by norm_num:0<(1:ℝ)))] with j small y yn bound
  have budget:y≤b*(j:ℝ)^2:=bound.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
  have cv:C.buy y*Real.exp (-(η*speed V*(j:ℝ)))≤1:=by
    calc
      _≤(C.x*(b*(j:ℝ)^2)^C.d)*Real.exp (-(η*speed V*(j:ℝ))):=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ yn budget _) cp) (Real.exp_pos _).le
      _=C.x*b^C.d*((j:ℝ)^(2*C.d)*Real.exp (-(η*speed V*(j:ℝ)))):=by rw [mul_pow,pow_mul];ring
      _≤1:=small
  have pay:=mul_le_mul_of_nonneg_right cv (Real.exp_pos (η*speed V*(j:ℝ))).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at pay
  rw [Real.rpow_def_of_pos (V.step j).positive,scale]
  rw [show -(↑j*speed V)*(-η)=η*speed V*↑j by ring]
  exact pay

end YM.Integration.WilsonIndependentFittedEarlyGeometry
