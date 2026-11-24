import YM.Integration.WilsonOriginalPublicPlantedPeriod
import YM.Integration.WilsonIndependentMatchedKernelResidual

/-! The paid credit on the actual compensated Wilson section is subpower at
the report, uniformly over the finer cutoff. Retain its separation gain and
lower the spatial moment before translating the source. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPlantedStableCredit
open WilsonCoeffUV WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open private speed pos scale from YM.Integration.WilsonOriginalPublicPlantedPeriod
open scoped BigOperators Topology Classical

variable {G:Gauge}{h D k u e:ℕ}{F:Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

private theorem tape (S:Schedule)(m i:ℕ):
    (i:ℝ)*Real.log 3≤S.scale (m+i)-S.scale m:=by
  induction i with
  | zero=>simp
  | succ i ih=>
    push_cast
    have hi:Real.log 3≤S.scale (m+i+1)-S.scale (m+i):=arch_pos ..
    rw [←Nat.add_assoc m]
    linarith

def span (L:CutsP H T p v E W K U)(i:ℕ):ℝ:=
  L.vesselsC.draws.S.scale (L.m+i)-L.vesselsC.draws.S.scale L.m

theorem age (L:CutsP H T p v E W K U)(B:ℝ)(home:L.vesselsC.y L.m≤B):
    L.Age≤B+(1+(Real.log 3)⁻¹)*span L L.i:=by
  have logpos:0<Real.log 3:=Real.log_pos (by norm_num)
  have work:(L.i:ℝ) ≤ span L L.i/Real.log 3:=
    (le_div_iff₀ logpos).mpr (tape L.vesselsC.draws.S L.m L.i)
  change L.vesselsC.y L.m+span L L.i+(L.i:ℝ)≤_
  rw [div_eq_mul_inv,mul_comm (span L L.i) _] at work
  linarith

private theorem rising (V:XSpace.Run):Tendsto (fun i:ℕ=> -Real.log (V.step i).spacing) atTop atTop:=by
  simp only [scale,neg_neg]
  simpa only [mul_comm _ (speed V)] using
    ((tendsto_const_mul_atTop_of_pos (pos V)).mpr (tendsto_natCast_atTop_atTop (R:=ℝ)))

/-- The genuine filed age is its home fee, optical span and number of dates.
Only the optical span and constant home price are used. -/
theorem credit (V:XSpace.Run)(C:Credit)(B η:ℝ)(positive:0<η):
    ∀ᶠ j:ℕ in atTop,∀(L:CutsP H T p v E W K U),L.vesselsC.y L.m≤B →
      span L L.i= -Real.log (V.step j).spacing →
      C.buy L.Age≤(V.step j).spacing^(-η):=by
  let b:=2+(Real.log 3)⁻¹
  have bp:0<b:=by have:0<Real.log 3:=Real.log_pos (by norm_num);dsimp [b];positivity
  have cp:0≤C.x:=zero_le_one.trans C.good
  have end₀:Tendsto (fun x:ℝ=>x^C.d*Real.exp (-(η*x))) atTop (𝓝 0):=by
    simpa [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (C.d:ℝ) η positive
  have tail:Tendsto (fun j:ℕ=>C.x*b^C.d*((-Real.log (V.step j).spacing)^C.d*
        Real.exp (-(η*(-Real.log (V.step j).spacing))))) atTop (𝓝 0):=by
    simpa using (end₀.comp (rising V)).const_mul (C.x*b^C.d)
  filter_upwards [(rising V).eventually_ge_atTop B,(rising V).eventually_ge_atTop 0,
    tail.eventually_le_const (show (0:ℝ)<1 by norm_num)] with j older high small L base length
  let X:ℝ:= -Real.log (V.step j).spacing
  have y:0≤L.Age:=by
    change 0≤L.vesselsC.y L.m+span L L.i+(L.i:ℝ)
    rw [length]
    linarith [L.vesselsC.depth L.m L.ha,(Nat.cast_nonneg L.i:0≤(L.i:ℝ))]
  have budget:L.Age≤b*X:=by
    have bill:=age L B base
    rw [length] at bill
    dsimp only [X,b]
    linarith
  have cv:C.buy L.Age*Real.exp (-(η*X))≤1:=by
    calc
      _≤(C.x*(b*X)^C.d)*Real.exp (-(η*X)):=by
        dsimp only [Credit.buy]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ y budget _) cp)
          (Real.exp_pos _).le
      _=C.x*b^C.d*(X^C.d*Real.exp (-(η*X))):=by rw [mul_pow];ring
      _≤1:=small
  have pay:=mul_le_mul_of_nonneg_right cv (Real.exp_pos (η*X)).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one,one_mul] at pay
  rw [Real.rpow_def_of_pos (V.step j).positive]
  simpa only [X,mul_neg,neg_mul,mul_comm η] using pay

/-- Actual normalized cover return at every retained rank, including rank
zero, with the reporter and the independent cutoff on the specified mesh.
The later test can spend a separately selected smaller spatial moment. -/
theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit)
    (V:XSpace.Run)(B η:ℝ)(positive:0<η):
    ∀ᶠ j:ℕ in atTop,∀(L:CutsP H T p v E W K U),L.vesselsC.y L.m≤B →
      span L L.i= -Real.log (V.step j).spacing → ∀ lag≤e, ∀ i≤L.i, ∀ r:ℕ,∀ moment≤u,
      Fruit 0 1 moment ((L.springP i).2 lag r)
        ((V.step j).spacing^(-η)*((V.step j).spacing/Real.exp (-span L i))^(1/4:ℝ)*L.fuel):=by
  obtain ⟨C,paid⟩:=WilsonIndependentMatchedKernelResidual.original H T p v E W K U
  filter_upwards [credit (H:=H) (T:=T) (p:=p) (v:=v) (E:=E) (W:=W) (K:=K) (U:=U)
    V C B η positive] with j budget L base length lag hl i hi r moment hm
  have expEq:Real.exp (-(L.vesselsC.draws.S.scale L.ceilC-
      L.vesselsC.draws.S.scale (L.m+i))/4)=
      ((V.step j).spacing/Real.exp (-span L i))^(1/4:ℝ):=by
    rw [Real.rpow_def_of_pos (div_pos (V.step j).positive (Real.exp_pos _)),
      Real.log_div (V.step j).positive.ne' (Real.exp_pos _).ne',Real.log_exp]
    apply congrArg Real.exp
    dsimp only [span,CutsP.ceilC] at length ⊢
    linarith
  have row:=((paid L).2.2 lag hl i hi r).slice zero_le_one hm
  apply row.more
  rw [expEq]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (budget L base length)
    (Real.rpow_nonneg (div_pos (V.step j).positive (Real.exp_pos _)).le _)) L.hf

end YM.Integration.WilsonOriginalPublicPlantedStableCredit
