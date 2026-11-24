import YM.MSbar.DeltaM.Cloud
import YM.MSbar.DeltaM.Tower
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Kelvin
open Function Filter MeasureTheory Cacao PowerSeries Finset Whisk
open scoped Topology BigOperators Classical ENNReal NNReal ContDiff
open Matrix Further.GaussianScalar MvPolynomial Analysis Bakery Lattice
open ProbabilityTheory
variable {ι σ τ:Type}[Fintype ι][Fintype τ][Fintype σ][DecidableEq ι][DecidableEq σ]{X:Type*}[MeasurableSpace X]{μ:Measure X} [IsProbabilityMeasure μ]
variable {A : Matrix σ σ ℝ}
local notation "ρ!"=> fieldLaw A
variable {M H W p F : ℕ}{t a b c d :ℝ}
noncomputable def stepW (H:ℕ)(c:ℝ):= 1+2*Real.exp (c*((2:ℝ)^H)^2/2)
lemma worth (h:A.PosDef)(c:ℝ)(hc:∀ i,A i i ≤ c) (i:σ)(t:ℕ) : Bank (fieldLaw A) t (fun x:View σ=> x i) (stepW t c) :=by
    let p:ℕ:= 2^t; let f(w:View σ):= w i; have he:0 < p:= Nat.pow_pos (by norm_num);
    have hp: MemLp f (bell t) (fieldLaw A):= by
        haveI:= rootedG h; exact IsGaussian.memLp_dual (fieldLaw A) (ContinuousLinearMap.proj i:View σ→L[ℝ]ℝ) (bell t) ((tL ..).2.1) -- namespace
    have hi:(bell t).toReal=p:=by unfold p bell;push_cast;simp
    let C:=stepW t c; have hC:0 ≤ C:=by unfold C stepW; positivity
    refine ⟨hC, measurable_pi_apply _,?_⟩; change eLpNorm f _ _ ≤ _
    rw [MemLp.eLpNorm_eq_integral_rpow_norm (tL t|>.1) (tL t|>.2.1) hp]; apply ENNReal.ofReal_le_ofReal -- formula norm version
    obtain ⟨hf,h⟩:= pol h c hc i p
    simp_rw [hi,Real.norm_eq_abs,Real.rpow_natCast]; have hu : Integrable (fun i=> |f i|^p) ρ!:= hf.mono' (((measurable_pi_apply i).abs.pow_const _).aestronglyMeasurable) (ae_of_all _ fun x=> by change ‖|f x|^p‖ ≤ _; rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]; exact pow_le_pow_left₀ (abs_nonneg _) (le_add_of_nonneg_left zero_le_one) _)
    let B:= 2*Real.exp (c*(p:ℝ)^2/2); let P':=∫ i,|f i|^p∂(fieldLaw A); have ht:P' ≤ B:= (integral_mono hu hf (fun i=> pow_le_pow_left₀ (abs_nonneg _) (le_add_of_nonneg_left zero_le_one) _)).trans h
    have hp:(p:ℝ)≥1:= Nat.one_le_cast.mpr he;
    have hV: 1+B=C:=by unfold B C stepW p; push_cast; try rfl
    change P' ^ ((p:ℝ)⁻¹) ≤ C; rw [← hV]; have hX:0≤ P':=integral_nonneg (fun i=> pow_nonneg (abs_nonneg _) p); apply le_trans (Real.rpow_le_rpow hX (ht.trans (le_add_of_nonneg_left zero_le_one)) (by positivity)) _; let z:=1+B; have h:1 ≤z:=by unfold z B; have hc':= Real.exp_pos (c * (p:ℝ)^2/2); linarith
    exact (Real.rpow_le_rpow_of_exponent_le h (inv_le_one_of_one_le₀ hp)).trans (Real.rpow_one z).le
-- balls. product budget real.Root.Cl.PDE.
lemma reproduce {p':ℝ} (d F :X→ View σ) (M :ℕ)(L :List σ)
    (he:0 ≤ p') (hx:0 ≤ t) (hw:∀ i∈L,Bank μ (M+L.length) (fun x=> d x i) p' ∧ Bank μ (M+L.length) (fun x=> F x i) p' ∧ Bank μ (M+L.length) (fun x=> d x i - F x i) t) :
    Bank μ M (fun x=> eval (d x) (play L)) (p'^L.length) ∧ Bank μ M (fun x=>eval (F x) (play L)) (p'^L.length) ∧ Bank μ M (fun x => eval (d x) (play L)-eval (F x) (play L)) (L.length*(t*p'^(L.length-1))) :=by
   induction L generalizing M with
   | nil=>
      simp only [play,List.map_nil,List.prod_nil,map_one,sub_self,List.length_nil,Nat.cast_zero,Nat.zero_sub,pow_zero,zero_mul]; refine ⟨(Bank.cast (μ:=μ) 1 M).length ?_, (Bank.cast (μ:=μ) 1 M).length ?_,(Bank.cast (μ:=μ) 0 M).length ?_⟩ <;> simp
   | cons a l ih=>
      simp_rw [List.length_cons, Nat.add_sub_cancel] -- order
      let d₀(x):=eval (d x) (play l);let D₀(x):= eval (F x) (play l); obtain ⟨hΩ,hη,hX⟩:= hw a (List.mem_cons_self)
      rw [show play (a::l)= MvPolynomial.X a * play l from rfl];simp_rw [map_mul,MvPolynomial.eval_X]
      obtain ⟨hp,hc,Hh⟩:= ih (M+1) (fun i hi=> by rw [show M+1+l.length=M+(a::l).length from by rw [List.length_cons]; omega]; exact hw i (List.mem_cons_of_mem _ hi))
      let n:= M+(a::l).length; have hM:M+1≤ n:=by unfold n; simp
      have hz:= hΩ.slips hM; have he:=hη.slips hM; refine ⟨pow_succ' p' l.length|>.symm ▸ hz.Τilt hp, pow_succ' p' l.length|>.symm ▸ he.Τilt hc,?_⟩; -- ▸ brittle
      let w(x):=(d x a-F x a)*D₀ x; let u(x):=d x a*(d₀ x-D₀ x); have ht: Bank μ M (w+u) (t*p'^l.length+p'*(l.length*(t*p'^(l.length-1)))):= ((hX.slips hM).Τilt hc).fest (hz.Τilt Hh)
      have hZ : (fun x=>d x a*d₀ x-F x a*D₀ x)=w+u:=funext fun i=>by change _=w i+u i; unfold w u;ring
      rw [hZ]; apply ht.length; cases h:l.length with |zero=>simp|succ k=>rw [show k+1-1=k by omega,pow_succ']; push_cast; exact le_of_eq (by ring)
end YM.MSbar.Kelvin
