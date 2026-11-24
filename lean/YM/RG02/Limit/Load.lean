import YM.RG02.Limit.Steering

/-!
Marked log drivers with finite Laurent prefactors. Multiplying by a
known finite power at this horizon accounts for ALL negative costs before
packing the series. Includes the spike where no fields in a marked kernel;
such marks are subject to the same valuation test. Do not apply this to
complete masked (possibly discontinuous) expressions nor to old inherited
regular coefficients without proof of the `Loads` obligations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Therm
open Filter Function MeasureTheory Set Metric Marker Extra.Trajectories Grade
open PertExtension PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Asym Wick
open GaussianScore PowerSeries
open scoped ContDiff Topology Classical Real BigOperators
variable {E V : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][DecidableEq V]{B : Census V}

def pins (k : ℕ)(W : ℝ × E → Poly B)(t : ℝ)(x : E) := (((t:ℂ)^k)⁻¹) • W (t,t • x)

/-- Require vanishing after ray rescaling; keep explicit positive/negative
powers of physical kernels in W,k. When evaluated for comparing at g>0,
the LEFT polynomial is `W(t,t•x)/t^k`. -/
structure Loads (k : ℕ)(W : ℝ × E → Poly B) : Prop where
  quiet x : (W x).part B.quiet=0
  born s : ContDiffAt ℝ ∞ (fun x=> (W x).part s) 0
  prices s (x:E) i : i < k → coeff i (ribbon (fun z=> (W z).part s) (1,x))=0

def rises (k : ℕ)(W : ℝ × E→Poly B)(u : E) : Script B :=
    PowerSeries.mk fun i => Poly.inject fun s => coeff (i+k) (ribbon (fun z=> (W z).part s) (1,u))

lemma rise_coeff (k : ℕ)(W : ℝ × E→ Poly B)(u : E)(s : B.Mode)(i : ℕ) :
    (coeff i (rises k W u)).part s= coeff (i+k) (ribbon (fun z=> (W z).part s) (1,u)) := by
   let _ := (inferInstance : FiniteDimensional ℝ E)
   rw [rises,coeff_mk]; rfl

namespace Loads
variable {k : ℕ}{W : ℝ× E→Poly B}(G : Loads k W)
include G

lemma unscales (u:E)(s : B.Mode) : ribbon (fun z=> (W z).part s) (1,u)= X^k * onMode (rises k W u) s := by
   ext1 i
   rw [coeff_X_pow_mul']; split
   next h => rw [mode_coeff,rise_coeff,Nat.sub_add_cancel h]
   next h => exact G.prices s u i (Nat.lt_of_not_ge h)
lemma unscale (u : E) : Aims (fun t => pins k W t u) (rises k W u) := by
   intro s
   apply Near.priced (k:=k)
   rw [← G.unscales]
   refine Near.same (Asym.ribbon_test (G.born s) (1,u)) ?_
   filter_upwards [Tested.eventually_pos] with t ht
   have hh := show (((t:ℂ)^k)) ≠ 0 from pow_ne_zero _ (Complex.ofReal_ne_zero.mpr ht.ne')
   simp only [pins,Poly.part_smul,Prod.smul_mk,smul_eq_mul,mul_one,Complex.real_smul,Complex.ofReal_pow,← mul_assoc,mul_inv_cancel₀ hh,one_mul]
lemma zeroBase (u : E) : basepoint (rises k W u)=0 := by
   rw [basepoint_read]
   have H := ((G.unscale u) B.quiet).tendsto_first
   have he : (fun t=> (pins k W t u).part B.quiet)=fun _=>0 := funext fun t => by simp [pins,G.quiet]
   rw [he,mode_coeff] at H
   exact tendsto_nhds_unique H tendsto_const_nhds
end Loads

def board (f : ℝ× E → ℝ)(k : ℕ)(W : ℝ× E → Poly B)(b : E)(x : E) :=
   rises k W (x+b) + Grade.scalar B (Asym.driven f (bend b x))
lemma board_quiet (f : ℝ× E → ℝ){k : ℕ}{W : ℝ× E→ Poly B}(g : Loads k W)(b x : E) :
    basepoint (board f k W b x)=0 := by
   rw [board,map_add,g.zeroBase, ← hasDen, Grade.den_scalar,← PowerSeries.coeff_zero_eq_constantCoeff_apply, driver_vac,add_zero]

lemma board_ready (f : ℝ× E→ℝ)(k : ℕ)(W : ℝ× E→ Poly B)(b:E) : Edged (board f k W b) := by
   apply Edged.linear (x:=fun x=> rises k W (x+b)) _ (y:=fun x=> scalar B (Asym.driven f (bend b x))) _
   · intro i s; simp_rw [rise_coeff]; exact row_wires ..
   intro i s; simp_rw [scalar,coeff_map]
   by_cases h : s=B.quiet <;> simp only [Poly.bead, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,Poly.part_send, h,↓reduceIte]
   · exact displays f b i
   exact Wires.const _

section
variable [Fintype V]
/-- Actual numerator modes. -/
def lit (f:ℝ × E→ℝ)(k : ℕ)(W:ℝ × E→ Poly B)(s : B.Mode)(t : ℝ)(u : E) :=
    (Poly.pass (pins k W t u)).part s*Complex.ofReal (turbine f t u)

-- no log at the clipped representation. proof with analytic K scaled up to recover grades.
def count (V : Type)[Fintype V](k : ℕ) := k * Fintype.card V

def relay (k : ℕ)(W : ℝ × E → Poly B) (s : B.Mode)(x : ℝ × E) :=
   ∑ i∈Finset.range (Fintype.card V+1), (i.factorial:ℂ)⁻¹ * (x.1:ℂ)^(count V k-k*i)*(W x^i).part s

lemma relay_score (k : ℕ)(W : ℝ × E → Poly B) (s : B.Mode)(u : E){t : ℝ}(ht : 0 < t) :
    relay k W s (t,t • u)=(t:ℂ)^(count V k)*(Poly.pass (pins k W t u)).part s := by
   let _ := (inferInstance : FiniteDimensional ℝ E)
   unfold relay Poly.pass; rw [Poly.part_sum, Finset.mul_sum]; apply Finset.sum_congr rfl
   intro i hi; rw [Poly.part_smul]; unfold pins; rw [smul_pow,Poly.part_smul,mul_assoc]; dsimp only
   rw [inv_pow, ← pow_mul]
   have hn : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.ne'
   have h : k*i ≤ count V k := Nat.mul_le_mul_left k (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
   rw [mul_left_comm ((t:ℂ)^_), ← mul_assoc ((t:ℂ)^_), show (t:ℂ)^count V k *( (t:ℂ)^(k*i))⁻¹ = (t:ℂ)^(count V k-k*i) by
       apply (mul_inv_eq_iff_eq_mul₀ (pow_ne_zero _ hn)).mpr; rw [← pow_add,Nat.sub_add_cancel h]]

lemma relay_smooth {k : ℕ}{W : ℝ× E→ Poly B}(G : Loads k W)(s : B.Mode) :
    ContDiffAt ℝ ∞ (relay k W s) 0 := by
   let _ := (inferInstance : FiniteDimensional ℝ E)
   have ht (i : ℕ) : ∀ s : B.Mode, ContDiffAt ℝ ∞ (fun x => (W x ^ i).part s) 0 := by
      induction i with
      | zero => intro s; simp_rw [pow_zero]; exact contDiffAt_const
      | succ i ih =>
         intro s; simp_rw [pow_succ, Poly.part_mul]
         apply ContDiffAt.sum; intro p _; apply ContDiffAt.sum; intro q _; split
         exact (ih _).mul (G.born q)
         exact contDiffAt_const
   apply ContDiffAt.sum; intro i _
   exact (contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.contDiffAt.comp (0:ℝ×E) contDiffAt_fst).pow _)).mul (ht i s)

variable [MeasurableSpace E][BorelSpace E]
lemma relay_meas (k : ℕ){W : ℝ× E→Poly B}(h : ∀ s,Measurable fun x => (W x).part s)(s : B.Mode) : Measurable (relay k W s) := by
   let _ := (inferInstance : NormedAddCommGroup E)
   let _ := (inferInstance : NormedSpace ℝ E)
   let _ := (inferInstance : FiniteDimensional ℝ E)
   let _ := (inferInstance : BorelSpace E)
   have ht (i : ℕ) : ∀ s : B.Mode, Measurable (fun x => (W x ^ i).part s) := by
      induction i with
      | zero => intro s; simp_rw [pow_zero]; exact measurable_const
      | succ i ih =>
         intro s; simp_rw [pow_succ,Poly.part_mul]
         apply Finset.measurable_fun_sum; intro p _; apply Finset.measurable_fun_sum; intro q _; split
         exact (ih _).mul (h _)
         exact measurable_const
   apply Finset.measurable_fun_sum; intro i _; refine Measurable.mul ?_ (ht i s)
   fun_prop (disch:=exact measurable_id)

variable {k : ℕ}{W : ℝ×E → Poly B}
-- a separate driver can be split into quiet and marked orders; log graph accounting already matches.
private lemma mode_exp (x:Script B)(f : PowerSeries ℂ)(H : basepoint x=0)(h : coeff 0 f=0)(s : B.Mode):
    onMode (Grade.exponential (x+scalar B f)) s=onMode (Grade.exponential x) s * ex f := by
   have hh : basepoint (scalar B f)=0 := by rw [← hasDen,den_scalar,← PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact h
   rw [exponential_add H hh, ← full_scalar_exp _ h]
   ext1 i
   simp_rw [mode_coeff,PowerSeries.coeff_mul,Poly.part_sum]; apply Finset.sum_congr rfl; intro j _
   rw [scalar,coeff_map,mul_comm _ (Poly.bead _ _),Poly.product_bead,Poly.part_smul, mul_comm,mode_coeff]

omit [MeasurableSpace E] [BorelSpace E] in
lemma picked (G : Loads k W)(u b : E) (f : ℝ× E→ℝ)(s : B.Mode) :
    ribbon (relay k W s) (bend b u)* ex (driven f (bend b u)) =
      X^count V k * onMode (Grade.exponential (board f k W b u)) s := by
   have h := (G.unscale (u+b)).exponential_read (Filter.Eventually.of_forall fun i => by
      rw [pins, Poly.part_smul,G.quiet,mul_zero])
   unfold board; rw [mode_exp _ _ (G.zeroBase _) (driver_vac ..),← mul_assoc]; apply congr_arg (fun v => v * ex _)
   apply Near.unique' (ribbon_test (relay_smooth G s) (bend b u))
   apply Near.same (Near.promote (h s) (count V k)); filter_upwards [Tested.eventually_pos] with t ht
   change t^_ • _=relay k W s (t • ((1:ℝ),u+b))
   rw [Prod.smul_mk]; simp only [smul_eq_mul,mul_one, relay_score k W s _ ht, Complex.real_smul,Complex.ofReal_pow]

variable (μ : Measure E) [μ.HasTemperateGrowth][μ.IsAddRightInvariant][NeZero μ]
include μ

lemma identified {f : ℝ × E→ℝ}(Γ : Law E)(b:E)(G : Loads k W)(s : B.Mode) :
    shuttle Γ f (relay k W s) b= X^count V k * onMode (Wick.made Γ fun x => Grade.exponential (board f k W b x)) s := by
   ext1 i; rw [shuttle,PowerSeries.coeff_mk, coeff_X_pow_mul']; split
   next he =>
     rw [mode_coeff,Wick.made_part]; congr 1
     funext u; unfold pulsed; rw [picked G,coeff_X_pow_mul',if_pos he,mode_coeff]
   next hn =>
     exact Wick.fixed Γ μ _ 0 (funext fun x => by unfold pulsed; rw [picked G, coeff_X_pow_mul',if_neg hn])

lemma casts {f:ℝ× E→ℝ} {Γ : Law E}{r:ℝ}{b : E}(H : Steer Γ f r b)(hf : Measurable f)(G : Loads k W)
    (hm : ∀ s,Measurable fun x => (W x).part s)(s : B.Mode) :
    ∃ u>0,∀ S : ℝ→Set E, Collars u S →
        (∀ᶠ t in Tested.germ, IntegrableOn (lit f k W s t) (S t) μ) ∧
      Near (fun t=>∫ x in S t,lit f k W s t x ∂μ)
        (C (Complex.ofReal (leading Γ μ r)) * onMode (Wick.made Γ fun x=> Grade.exponential (board f k W b x)) s) := by
   obtain ⟨u,hu,H⟩ := transmission H μ hf (relay_smooth G s) (relay_meas k hm s)
   refine ⟨u,hu,fun S he=>?_⟩
   have hq t (ht : 0<t) (x:E) : sheet f (relay k W s) t x = (t:ℂ)^(count V k)*lit f k W s t x := by unfold sheet; rw [relay_score _ _ _ x ht,mul_assoc]; rfl
   obtain ⟨hh,hP⟩ := H S he
   rw [identified μ Γ b G, mul_left_comm] at hP
   constructor
   · filter_upwards [Tested.eventually_pos,hh] with t ht h
     have hi : sheet f (relay k W s) t=(fun x:E=>(t:ℂ)^(count V k)*lit f k W s t x) := funext (hq t ht)
     have hn := pow_ne_zero (count V k) (Complex.ofReal_ne_zero.mpr ht.ne')
     rw [hi] at h; exact (integrable_fun_smul_iff hn _).mp h
   apply Near.priced; apply Near.same hP
   filter_upwards [Tested.eventually_pos] with t ht
   change _ = t^_ • (∫ x in S t, lit f k W s t x ∂μ)
   simp_rw [hq t ht, Complex.real_smul, Complex.ofReal_pow, integral_const_mul]

end
end YM.RG02.Therm
