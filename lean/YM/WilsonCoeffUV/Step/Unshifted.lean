import YM.WilsonCoeffUV.Step.Scalar
/-!
# Unshifted bulk R-operation on the torus

`casePW`: values are in g-expansion after scaling both log sets by g,
including dormant tree variables prior to Wick. `winter`: raw accounting in
that coupling (kinetic reset later), Haar for the coarse mesh not yet added.
Scalar tax includes the per-coarse-edge NoiseZ normalizer of the conditional (Markov) kernel, over
same unperturbed cutoff/penalty and J. See Step/Source for the other conditional denominator (fixed output conditioning of the fine).
Unperturbed g-independent Gaussian constants and common power
constant discarded; never multiply these scalars through whole history. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Wilson Lattice Laurent Exterior Bloch Matrix Precision RG Blue
open Next.Free FreeResolvent Tree Filter Metric Function
open PowerSeries
open scoped Topology ContDiff BigOperators
variable {G:Gauge} {c f:Side}

abbrev PChart (G:Gauge)(n:Side):= Pal ℝ (Woods G n)

section
variable {U R:Type*}[AddCommGroup R]
lemma shell_sum {p q:Pal R U}{d}(h:shellK d p)(t:shellK d q) : shellK d (p+q) := by intro i j h'; simp_rw [Pi.add_apply,h _ _ h',t _ _ h',zero_add]
lemma shell_sub {p q:Pal R U}{d}(h:shellK d p)(t:shellK d q) : shellK d (p-q) := by intro i j h'; simp_rw [Pi.sub_apply,h _ _ h',t _ _ h',sub_zero]
lemma shell_scrub {p:Pal R U}{d}(h:shellK d p): shellK d (scrub p) := by
  intro i j h'; rw [scrub]; split; · rfl
  exact h _ _ h'
lemma pure_scrub {p: Pal ℝ U}(h:∀ i,Pure (p i)) (i): Pure (scrub p i) := by
  rw [scrub]; split; · exact Pure.zero
  exact h i
lemma fade_zero [Module ℝ R] [Fintype U] {V:Type*}(K:Matrix U V ℝ) : fade K (0:Gen R U)=0:= funext fun i=>funext fun j=>by unfold fade; simp
lemma pure_sum {I:Type*}{s:Finset I}{F:I→Gen ℝ U}(h:∀ i∈s,Pure (F i)) : Pure (∑ i∈s,F i) := by intro k; simp_rw [Finset.sum_apply]; exact Blue.Smooth.sum (fun i hi=>h i hi k)
end
section
variable (S:StepData c f)

def plugζ (Ñ:ChartRatio G) := (Fintype.card (Edge (Site c))) • logOf (ζ Ñ S.kernel.penalty)

def casePW (Ñ:ChartRatio G)(M:Matrix (Woods G f) (Woods G c) ℝ)(P:PChart G f) : Pal ℝ (Joint G f c) :=
    (fun e=> fade (camber G M) (sprig (unhaar Ñ) 0 e))-
    (fun e=> fade (groundM G M) (scrub (sprig (jointPen G S) 2) e))-
    fun e=> fade (camber G M) (scrub P e)

variable (F:Forest S.ratio) (H Y:FreeResolvent.FaceRow) (Q:Matrix (Body 1 f) (Body 1 c) ℝ)

def xray (Ñ:ChartRatio G) (P:PChart G f) := abr (fillSlots (Woods G c) (covariance G S F H)) (casePW S Ñ (extractV G S F Q) P)
def summer (Ñ:ChartRatio G) (P:PChart G f) : PChart G c:= fun i=>
    fade plug (∑ j∈Finset.range (3+3*i), xray S F H Q Ñ P j i)
def winter (Ñ:ChartRatio G)(P:PChart G f):PChart G c := flatPal (precisionC G c Y)-summer S F H Q Ñ P + uband (plugζ S Ñ)

section design
variable {M : Matrix (Woods G f) (Woods G c) ℝ}{Ñ:ChartRatio G}{P:PChart G f}

lemma pack_band
  (h : shellK 2 P): shellK 2 (casePW S Ñ M P) := by
  have hp : shellK 2 (sprig (unhaar (n:=f) Ñ) 0):= fun i j h=> sprig_count (unhaar (n:=f) Ñ) 0 i j (by omega)
  exact shell_sub (shell_sub (fade_shell _ hp) (fade_shell _ (shell_scrub (sprig_count _ _)))) (fade_shell _ (shell_scrub h))
lemma pack_pure (h:LocalRatio Ñ)(e:S.patch.Branches S.kernel G)(p:∀ i,Pure (P i))(i): Pure (casePW S Ñ M P i) :=
  ((fade_pure (sprig_pure (unhaar (n:=f) Ñ) (unhaar_green h) _ _) _).sub (fade_pure (pure_scrub (sprig_pure _ (penSmooth G S e) 2) _) _)).sub (fade_pure (pure_scrub p _) _)
lemma pack_zero (h:LocalRatio Ñ) : casePW S Ñ M P 0=0 := by
  have hx : sprig (unhaar (n:=f) Ñ) 0 0=0 := by
    unfold sprig; ext1 j; by_cases hv:0=j
    · subst j; rw [shine_lit]; ext x; simp [rye,unhaar_zero h]
    exact shine_dark hv
  simp_rw [casePW,Pi.sub_apply, scrub]; rw [hx]; simp [fade_zero]
lemma uband_cost (U:Type*) (u:PowerSeries ℝ)(i): Pure (uband (U:=U) u i) := shine_pure (fun _ _=>rfl)
lemma uband_length (U:Type*) (u:PowerSeries ℝ)(k:ℕ): shellK k (uband (U:=U) u):= fun i j h=> shine_dark (by omega)
lemma uband_zero (h:LocalRatio Ñ): uband (U:=Woods G c) (plugζ S Ñ) 0=0 := by
  have he : constantCoeff (plugζ S Ñ)=0:=by rw [plugζ,map_nsmul, constantCoeff_logOf (ζ_one _ h),smul_zero]
  ext i j; by_cases h:i=0 <;> simp [*,uband,shine,PowerSeries.coeff_zero_eq_constantCoeff_apply,eq_comm]
lemma summer_pure (h:LocalRatio Ñ)(e:S.patch.Branches S.kernel G)(p:∀ i,Pure (P i))(i) : Pure (summer S F H Q Ñ P i) := fade_pure (pure_sum fun j _=>pure_abr (fillSlots _ _) (pack_pure S h e p) j i) _
lemma summer_band (h:LocalRatio Ñ)(p:shellK 2 P) : shellK 2 (summer S F H Q Ñ P) := by
  have hv :=stops_abr (fillSlots (Woods G c) (covariance G S F H)) (pack_band (M:=extractV G S F Q) (Ñ:=Ñ) S p) (pack_zero S h)
  refine fade_shell plug ?_
  intro i r hi; change (∑ j∈Finset.range _, xray S F H Q Ñ P j i) r=0; rw [Finset.sum_apply]; exact Finset.sum_eq_zero fun j _=> hv j i r (Or.inl hi)
lemma winter_band (h:LocalRatio Ñ)(p:shellK 2 P) : shellK 2 (winter S F H Y Q Ñ P) := shell_sum (shell_sub (flat_count _) (summer_band S F H Q h p)) (uband_length _ _ 2)
lemma winter_pure (h:LocalRatio Ñ)(e:S.patch.Branches S.kernel G)(p:∀ i,Pure (P i))(g:(Y.acts c).transpose=Y.acts c)(i) : Pure (winter S F H Y Q Ñ P i) :=
    ((flat_sym _ (kinetic_sym g) i).sub (summer_pure S F H Q h e p i)).add (uband_cost _ _ i)
lemma winter_calm (h:LocalRatio Ñ): winter S F H Y Q Ñ P 0=shine (orbQ (precisionC G c Y)) := by
  have hx : summer S F H Q Ñ P 0=0 := by
    unfold summer; rw [Finset.sum_eq_zero, fade_zero]; intro i _; exact bare_abr _ (pack_zero S h) _
  simp_rw [winter, Pi.add_apply, Pi.sub_apply,hx,uband_zero S h]; simp [flatPal]
end design
end
end YM.WilsonCoeffUV
