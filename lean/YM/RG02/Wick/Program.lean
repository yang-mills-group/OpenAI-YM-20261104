import YM.RG02.Wick.Drivers
import YM.RG02.Wick.Board

/-!
# Arbitrary connected order

From one integrated script state to joint cumulants exactly. A script is of
actual LOG integrand-polynomials on centered fields, after extracting common
stationary/background constants (before log or division), with coupling grade
nonnegative. Tags are averaged **after exponentiating**.

`models`: through order r, each exponent driver carries its mixed-mode
indices (mark roots, leg support/coordinates). Need only wires on unbounded
fields; valuation/readouts to verify from actual germs. Input of vacuum zero is essential here. Different tag Hessian spaces allowed. A common leg
alphabet (e.g. all link positions, including inactive) in `program_log`
makes each connected driver & Wick line on the tag law. Tag by tag normalization
may differ; absorb the weights by including all constant costs in `ν`. Require
unit after averaging these same weights. Not a log of mean covariance, nor
the extensive vacuum scalar; see `subtract_vacuum`. Estimates from
re-expression of analytic representations are separate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Wick
open Marker Multi Finset Marks Extra.Trajectories Grade PowerSeries
open Next.Rank Next.Rank.Normal PertExtension GaussianScore
open MeasureTheory Filter
open scoped BigOperators Classical

variable {V T W : Type}[DecidableEq V]{R : Census V}

/-- Sum at a common field. Tag *law* includes any prefactors still
retained on this background. -/
def mix (ν : (T → ℂ) →ₗ[ℂ] ℂ)(x : T→ Script R) : Script R := PowerSeries.mk fun n =>
    Poly.inject fun s => ν fun i => (coeff n (x i)).part s

lemma mix_part (ν : (T → ℂ) →ₗ[ℂ] ℂ)(x : T→ Script R)(n : ℕ)(s : R.Mode) :
    (coeff n (mix ν x)).part s = ν fun i => (coeff n (x i)).part s := by rw [mix,PowerSeries.coeff_mk]; rfl

lemma mix_encode (ν : (T → ℂ) →ₗ[ℂ] ℂ)(x : T→ Script R)(r : ℕ)(s : (mixed r R).Mode) :
    (encode r (mix ν x)).part s = ν fun i => (encode r (x i)).part s := by
  simp_rw [encode_part]; rw [mix_part]; exact (ν.map_smul _ _).symm

variable {E : T→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,FiniteDimensional ℝ (E i)]
variable [Fintype V]

/-- SCRIPT Step. Contract vertices polynomially then average on
stochastic tags. Integral used only to prove this algorithm, not
in the coefficient definition. -/
def script (ν : (T → ℂ)→ₗ[ℂ]ℂ)(Γ : (i:T)→ Law (E i))(f : (i:T)→E i → Script R) :=
    mix ν fun i => made (Γ i) fun x => Grade.exponential (f i x)

lemma script_part (ν : (T → ℂ)→ₗ[ℂ]ℂ)(Γ : (i:T)→ Law (E i))(f : (i:T)→E i → Script R)(n : ℕ)(s : R.Mode) :
    (coeff n (script ν Γ f)).part s = ν fun i => weigh (Γ i) fun x => (coeff n (Grade.exponential (f i x))).part s := by
   rw [script,mix_part]; simp_rw [made_part]

section
variable [∀ i,MeasurableSpace (E i)][∀ i,BorelSpace (E i)]
variable {ν : (T → ℂ)→ₗ[ℂ]ℂ}{Γ : (i:T)→ Law (E i)}{f : (i:T)→E i→Script R}
variable (μ : (i:T)→Measure (E i))[∀ i,(μ i).HasTemperateGrowth][∀ i,(μ i).IsAddRightInvariant][∀ i,NeZero (μ i)]
include μ

lemma program_base (hv : ν 1=1)(hf : ∀ i x, Grade.basepoint (f i x)=0) : basepoint (script ν Γ f)=1 := by
   rw [basepoint_read,script_part]
   calc
      _ = ν 1 := by
         apply congr_arg; funext i; change weigh (Γ i) _= 1
         apply fixed _ (μ i); funext x; rw [← basepoint_read, base_exponential (hf ..)]
      _ = _ := hv

variable (hv : ν 1=1) (hf : ∀ i, Edged (f i))(hz : ∀ i x,basepoint (f i x)=0)

/-- Leg representation NEEDS all allowed modes. Defines on pointed drivers;
each driver at grade(s) includes its `card!` polarization weight. Polynomial
Gaussian amplitudes in `φ(i)` centered. Use `coloring` inverse precision on
this same relative Hessian. -/
def models (r : ℕ)(ℓ : (i:T)→ W → Module.Dual ℝ (E i))(f : (i:T)→ E i → Script R)
    (G : Multi.Hot (mixed r R) → T → poly W) := ∀ i (b : Multi.Hot (mixed r R)),
      paint (ℓ i) (G b i)=fun x => (encode r (f i x)).part b.val
include hz hf

lemma unmerged (r : ℕ)(ℓ : (i:T)→ W → Module.Dual ℝ (E i)){G : Multi.Hot (mixed r R) → T → poly W}(H : models r ℓ f G) :
   encode r (script ν Γ f) = Multi.substitute _ (stellar ν (fun t => coloring (Γ t) (ℓ t)) G) := by
   let S := mixed r R
   ext b
   rw [script,mix_encode, substituted]
   let a (p:(parts S).Mode)(t:T) := charge (Γ t) (ℓ t) ((∏ u∈p.val, G u) t)
   have he (p:(parts S).Mode) : (stellar ν (fun t => coloring (Γ t) (ℓ t)) G).part p = ν (a p) := by rfl
   simp_rw [he]; rw [← map_sum]; apply congr_arg
   funext t
   rw [on_mode (Γ t) (μ t) ((hf t).pass)]
   let Y (x:E t) := (encode r (Grade.exponential (f t x))).part b
   have ht : Wires Y := Edged.encodes ((hf t).pass) r b
   let d : poly W :=∑ p∈shards S b,(∏ u∈p.val, G u) t
   have hd : paint (ℓ t) d= Y:= by
      funext x; unfold Y
      rw [encode_exponential (hz ..), Marks.pass_partition ((encode_quiet ..).trans (hz ..))]
      unfold paint d; rw [map_sum]; apply sum_congr rfl; intro p _
      rw [Finset.prod_apply,map_prod]
      exact prod_congr rfl fun i _ => congr_fun (H t i) x
   change weigh (Γ t) Y = _
   rw [binds _ (μ t) _ _ ht hd]; unfold d; rw [map_sum,Finset.sum_apply]

include hv
/-- All orders. The connected part at every mode reduces to joint ordinary
tag/covariance cumulants of labeled drivers only. *Then* subtract the
normalized vacuum for insertions. -/
theorem program_log (r : ℕ)(ℓ : (i:T)→ W → Module.Dual ℝ (E i)){G : Multi.Hot (mixed r R) → T → poly W}(H : models r ℓ f G) :
    encode r (Grade.logarithm (script ν Γ f)) = Multi.substitute (mixed r R)
       (connected (stellar ν (fun t => coloring (Γ t) (ℓ t)) G)) := by
   rw [encode_logarithm (program_base μ hv hz), unmerged μ hf hz r ℓ H]
   let y : Poly (parts (mixed r R)) := stellar ν (fun t => coloring (Γ t) (ℓ t)) G
   let X:= mixed r R
   change connected (Multi.substitute X y) = Multi.substitute X (connected y)
   have hy : y.part (parts X).quiet=1 := stellar_quiet hv _ _
   have hc : (Multi.substitute X y).part X.quiet=1 := by rw [substituted, shards_quiet,sum_singleton]; exact hy
   have ht : (Multi.substitute X (connected y)).part X.quiet=0 := by rw [substituted,shards_quiet,sum_singleton]; exact connected_quiet hy
   apply pass_inj (connected_quiet hc) ht
   rw [pass_connected hc, ← pass_map _ _ (connected_quiet hy) ht,pass_connected hy]

/-- Formal conditional marked connected SCRIPT.
QUIET part pure vacuum vanishes INCLUDING copies of g with no markers; i.e.
project only after full cumulant. -/
theorem subtract_vacuum (r : ℕ)(ℓ : (i:T)→ W → Module.Dual ℝ (E i)){G : Multi.Hot (mixed r R) → T → poly W}(H : models r ℓ f G) :
    encode r (Grade.logarithm (Grade.quotient (script ν Γ f))) = Multi.substitute (mixed r R)
       (connected (stellar ν (fun t => coloring (Γ t) (ℓ t)) G)) -
         encode r (Grade.logarithm (Grade.scalar R (Grade.den (script ν Γ f)))) := by
   rw [vacuum_graphs (program_base μ hv hz), encode_sub, program_log μ hv hf hz r ℓ H]

-- no finite-alphabet restriction in statement; degree/moments not guaranteed.
omit μ hv hz [∀ (i : T), FiniteDimensional ℝ (E i)] [Fintype V] [∀ i,MeasurableSpace (E i)] [∀ (i : T), BorelSpace (E i)] in
theorem exist_polys (r : ℕ) : let Q := (i : T) × Module.Dual ℝ (E i); ∃ (l : (i:T) → Q → Module.Dual ℝ (E i))(g : Multi.Hot (mixed r R)→ T → poly Q), models r l f g := by
  intro Q
  let l (i:T) : Q → Module.Dual ℝ (E i) := fun x => if h : x.1=i then h ▸ x.2 else 0
  let v (y : Multi.Hot (mixed r R))(t:T)(x:E t) := (encode r (f t x)).part y.val
  let g (t : T) : Module.Dual ℝ (E t) → Q := Sigma.mk (β:=fun i:T => Module.Dual ℝ (E i)) t
  let P (b : Multi.Hot (mixed r R))(t:T) := MvPolynomial.rename (g t) (stroke (v b t))
  refine ⟨l,P,fun t b=>?_⟩
  change paint _ _=v b t
  nth_rw 1 [← painted (show Wires (v b t) from (hf t).encodes r b.val)]
  funext x; unfold paint P; rw [MvPolynomial.aeval_rename]
  congr 1
  ext i; simp [l,g]
end

end YM.RG02.Wick
