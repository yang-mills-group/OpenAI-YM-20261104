import YM.RegulatorIR.Diagram.Wick

/-! Remove the finite time label in the specified coupling first.
Vacuum constants included with exactly the same exponential as used in the
joined input and output. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open Function Formal Interval Finset PowerSeries
open Budget Budget.Layer PertExtension Gaussian MeasureTheory GaussianScore
open scoped Topology BigOperators Classical PowerSeries Polynomial
variable {I J:Type} [Fintype I]

def rated (R:ℕ→ℕ)(V:Orders I): PowerSeries (Jet I) := PowerSeries.mk fun e=>packed (V e) (R e)
lemma rated_v (R:ℕ→ℕ)(V:Orders I)(e): coeff e (rated R V)=packed (V e) (R e):=coeff_mk ..

-- evaluate time series polynomials in real Jet algebra

def lands (t: Jet I):CurveT I→ₐ[ℝ] Jet I:={Polynomial.evalRingHom t with
 commutes' := by intro r; rw [Polynomial.algebraMap_apply]; change Polynomial.eval ..= _; rw [Polynomial.eval_C] }

def emphasis (b:I→ℝ) : Jet I→ₐ[ℝ]ℝ:=MvPolynomial.aeval b
omit [Fintype I] in
lemma language (b:I→ℝ)(p:Jet I): emphasis b p=MvPolynomial.eval b p:=by rw [emphasis]; simp

lemma deserts (T:ℕ→Orders I)(R C':ℕ→ℕ) : map (lands (I:=I) 1).toRingHom (desert R C' T)=rated C' (heated R T) := by
 ext1 e
 rw [desert,PowerSeries.coeff_map,PowerSeries.coeff_mk,rated_v]
 change (∑ i∈range (R e+1), Polynomial.monomial i (packed (T i e) _)).eval 1 = packed _ _
 rw [Polynomial.eval_finsetSum,show heated R T e=∑ i∈range (R e+1),T i e from ?_, pack_sum]; simp [Polynomial.eval_monomial]
 ext1 i; simp [heated,Finset.sum_apply]
lemma plains_init (K:Layer I I)(V:Orders I)(h:Vacuum V): map (lands (I:=I) 0).toRingHom (plains K V)=rated (fun e=>e+2) V:=by
 ext1 e;rw [PowerSeries.coeff_map,rated_v]; change Polynomial.eval 0 _ = _
 rw [← Polynomial.coeff_zero_eq_eval_zero,log_v K V e 0 h];unfold packed; simp_rw [logHeat_first]; simp
lemma owned_init (m:ℕ)(K:Layer I I)(V W:Orders I)(h:Vacuum V)(hf:∀ e,Within (e+(m+1)) (W e)):
   map (lands (I:=I) 0).toRingHom (owned m K V W)=rated (fun e=>e+m+1) W:=by
 ext1 e; rw [PowerSeries.coeff_map,rated_v];change Polynomial.eval 0 _ = _; rw [← Polynomial.coeff_zero_eq_eval_zero,mark_v m K V W e 0 h hf,markHeat_first]
lemma owns_end (m:ℕ)(K:Layer I I)(V W:Orders I) : map (lands (I:=I) 1).toRingHom (owned m K V W) = rated (fun e=>e+m+1) (endHeat (m+1) K (logHeat K V true) W):=by
 rw [owned,deserts]; unfold endHeat; congr 2; exact funext fun x=>Nat.add_comm _ _
lemma plain_end (K:Layer I I)(V:Orders I): map (lands (I:=I) 1).toRingHom (plains K V)= rated (fun e=>e+2) (ceaseHeat K V true) := deserts ..

section finite
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
  (A:Law E) (d:I→Module.Dual ℝ E) [MeasurableSpace E] [BorelSpace E] (μ:Measure E)[μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]

def burn (P:PowerSeries (Jet I))(B:I→ℝ):PowerSeries ℝ:= PowerSeries.mk fun i=> Gaussian.averaged A d μ B (coeff i P)

lemma count (U W:PowerSeries (Jet I))(P:EPS I)(B:I→ℝ) (h:U=map (lands 0).toRingHom P)(hh:W=map (lands 1).toRingHom P)(he:∀ e:ℕ, Pursues (bond A d) (coeff e P)):
  burn A d μ U B = map (emphasis B).toRingHom W :=by
 ext1 i
 rw [burn,PowerSeries.coeff_mk,h,hh,PowerSeries.coeff_map,PowerSeries.coeff_map,PowerSeries.coeff_map]
 change Gaussian.averaged A d μ B ((coeff i P).eval 0)= emphasis B _
 rw [← Polynomial.coeff_zero_eq_eval_zero,Gaussian.heat_identity A d μ _ (he i)]; exact (language B _).symm

lemma red (V:Orders I)(B:I→ℝ) (h:Vacuum V)(hp:gradedSymmetric V):
   burn A d μ (expo (rated (fun e=>e+2) V)) B= map (emphasis B).toRingHom (expo (rated (fun e=>e+2) (ceaseHeat (bond A d) V true))):=by
 let K:= bond A d;let H:=plains K V; apply count A d μ _ _ (expo H) _
 · rw [Formal.map_exp, show map _ H=rated (fun e=>e+2) V from plains_init K V h]
 · rw [Formal.map_exp, show map _ H=rated (fun e=>e+2) _ from plain_end K V]
 exact fun e=> coefficientP (free_heat (log_equation K V h hp) (plain_entry K V h)) e

lemma green (m:ℕ)(V F:Orders I)(B:I→ℝ)(h:Vacuum V)(hp:gradedSymmetric V)(hx:∀ e,Within (e+(m+1)) (F e))(hF:gradedSymmetric F):
    let K:=bond A d; let W:=expo (rated (fun e=>e+2) V); let y:=rated (fun e=>e+m+1) F
    let z:=map (emphasis B).toRingHom (rated (fun e=>e+m+1) (endHeat (m+1) K (logHeat K V true) F))
    burn A d μ (W*y) B=burn A d μ W B*z := by
 intro K W y z
 rw [show burn A d μ W B= _ from red A d μ V B h hp]; rw [← show _ from map_mul (map (emphasis B).toRingHom) _ (rated _ (endHeat _ _ _ _))]
 apply count _ _ _ _ _ (expo (plains K V)*owned m K V F)
 · rw [map_mul,Formal.map_exp,plains_init K V h, owned_init m K V F h hx]
 · rw [map_mul,Formal.map_exp,plain_end,owns_end]
 exact fun i=> Interval.coefficientP (Interval.mark_heat (Gaussian.bond_cross A d) (log_equation _ V h hp) (plain_entry K V h) (mark_equation m K V F h hx hp hF)) _
end finite
end YM.RegulatorIR.Diagram
