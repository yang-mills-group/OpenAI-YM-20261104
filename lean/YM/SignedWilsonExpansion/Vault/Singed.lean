import YM.SignedWilsonExpansion.Vault.Liquor
/-!
 F6 variant using backward tilt *on all arms together*, retain gradients and
 remainders after normalization and composition. Argument in finite tilt, not
 assigning orders in physical thermometer to the regular action. Keep exterior
 and older identities (with their respective conditioning variables). `First` applies
 even to smaller foreground doors if wanted, same exterior marginal for all masks.
-/
set_option autoImplicit false
set_option maxHeartbeats 510000
noncomputable section
namespace YM.Integration.Logwood
open Function Filter Finset Lattice RG Wilson MeasureTheory
open OPE.Therm
open scoped Topology ENNReal BigOperators Classical
open FVA1Physical.Exchange FVA1Physical.Exchange.F6Regular
open private normalized_entry from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6MeasuredExterior
open private fillPatch_meas tilted_probability from YM.Integration.FVA1Physical.Exchange.CovarianceExpansionF6OriginalExterior
variable {G:Gauge}{d i j N p:ℕ}{n: Side}{ε b:ℝ}{H:History G}
variable (U:Finset (Edge (Site n))) (R:Rep G n) (F:Config G n→ℂ)
abbrev additiveR := R.activities.additive R.p
variable {σ C Λ ξ:ℝ} (w:R.Lawful σ C Λ ε ξ) (pos:∀u,0<R.eval u)
/-- `remitS` is a true conditional regular-action covariance WITH the
 tilting base normalizations, not on the original conditional law before extracting
 the vacuum ratio. Reference displacement cancels in the covariance.
-/
def radiant (F):= leaner U (fun g=> baseOne R U (g* additiveR R) ) F
abbrev cabin := {b:Edge (Site n) // b∉ U}
local notation "Q" => (fun p : Config G n→ℝ => baseOne R U p)
local notation "lights" => (remitC U R F - remitS U R F)
include w pos
lemma slope (he:Envelope F)(o: cabin U → G.El): remitS U R F o= radiant U R F o - (baseOne R U (additiveR R) o) • remitC U R F o:=by
    let ν:= tiltedPatch R U o;let J:=fillPatch U o; let _ : IsProbabilityMeasure ν:= tilted_probability R w pos U o; have i0:Envelope ( additiveR R ):=⟨R.activities.E_measurable w.labels.regular,(Activities.ESeries w.labels).bound⟩; have pull {g:Config G n→ℝ}(v:Envelope g): Envelope (g∘J):= ⟨v.meas.comp (fillPatch_meas U o), v.cost.choose, fun x=> v.cost.choose_spec _⟩
    have hi g (e:Envelope g): patchInsertion R U (additiveR R) g o= Q ( g * additiveR R ) o-Q g o*Q ( additiveR R ) o:= first_is_covariance ν (g∘J) (additiveR R∘J) (pull e) (pull i0) ((additiveR R) (J 1)) -- identifier token additiveR R ok
    apply Complex.ext
    · rw [Complex.sub_re,Complex.real_smul]; simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; rw [mul_comm]; exact hi _ (splitRe he)
    rw [Complex.sub_im, Complex.real_smul]; simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]; rw [mul_comm]; exact hi _ (splitIm he)
lemma radiant_env (v:Envelope F): Envelope ( remitC U R F ) ∧ Envelope ( remitS U R F ):=by
    have i0:Envelope ( additiveR R ):=⟨R.activities.E_measurable w.labels.regular,(Activities.ESeries w.labels).bound⟩; let a (g)(v:Envelope g):Envelope (patchInsertion R U (additiveR R) g):=borel_first_insertion R w pos U g _ v i0; exact ⟨env_join (normalized_entry R w pos U _ ( splitRe v )) ( normalized_entry R w pos U _ ( splitIm v ) ), env_join ( a _ ( splitRe v ) ) ( a _ ( splitIm v ))⟩
local notation "fare₀" => (ticketA U R.p ε)
lemma fare_first (v:Envelope F)(hv:1≤R.p.supportExponent)(h:fare₀≤1/4) (hp:∀u,‖F u‖≤ b) (o:cabin U→ G.El) : ‖remitG U R F o-lights o‖ ≤24*b*fare₀^2:=by
    let e:=12*b*fare₀^2; let x:=remitG U R F o-lights o; have hi: |x.re|≤ e:= ( original_first_thermal R w pos U hv (Complex.re∘F) (splitRe v) b ( fun u=>( Complex.abs_re_le_norm _ ).trans ( hp u ) ) o h ).2.2; have he:|x.im|≤ e:= ( original_first_thermal R w pos U hv (Complex.im∘F) (splitIm v) b ( fun u=>( Complex.abs_im_le_norm _ ).trans ( hp u ) ) o h ).2.2; exact ( Complex.norm_le_abs_re_add_abs_im x ).trans (( add_le_add hi he ).trans_eq (by unfold e; ring ))
open HeartT HeartT.Spritz
variable (A:Family G){k N p:ℕ}(J:Finset (Edge (Site (A.side k p))))(f:Config G (A.side k p)→ℂ)
omit w pos
namespace First
local notation "r₀" => (A.path.rep N p k)
local notation "ω₀" => (allot A k N p J)
local notation "Δ0" => (16*b*ω₀^(d+1))
local notation "μ0" => (originalExterior A.path N p k J)
local notation "z0" => (remitC J r₀ f)
local notation "t0" => (remitS J r₀ f)
abbrev glob (N:ℕ) := Slate (originalExterior A.path N p k J) -- local notation μ0 hazardous implicit N
abbrev globB (N:ℕ) := glob A J N ( remitC J (A.path.rep N p k) f )
abbrev globS (N:ℕ) := glob A J N ( remitS J (A.path.rep N p k) f )
abbrev costs (N:ℕ)(d:ℕ):= glob A J N ( remit J (A.path.rep N p k) f d )
abbrev residue (N:ℕ)(d:ℕ):= glob A J N ( remit J (A.path.rep N p k) f d - (remitC J (A.path.rep N p k) f-remitS J (A.path.rep N p k) f ))
-- Full actual retained cumulant computation includes this first signed correction and pays
-- for ALL further terms e.g. at positive e via the finite normalized Taylor quotient;
-- secondOrder is an absolute bound BEFORE Θ^n.T.Use universal crop for all masks.
structure Burn (A:Family G) (J:Finset (Edge (Site (A.side k p)))) (f:Config G (A.side k p)→ℂ) (N:ℕ) (b:ℝ) : Prop extends Tilted A f J N b where -- notation issue with parent local r₀ maybe unfolds implicit A etc: avoid macro for implicit binder
    fibre : ∀o, IsProbabilityMeasure ( tiltedPatch (A.path.rep N p k) J o )
    receives : ∀o, remitS J (A.path.rep N p k) f o = radiant J (A.path.rep N p k) f o - (baseOne (A.path.rep N p k) J (additiveR (A.path.rep N p k)) o) • remitC J (A.path.rep N p k) f o
    kept : Envelope ( remitC J (A.path.rep N p k) f ) ∧ Envelope (remitS J (A.path.rep N p k) f)
    holds : ∀o, ‖remitG J (A.path.rep N p k) f o-(remitC J (A.path.rep N p k) f-remitS J (A.path.rep N p k) f) o‖≤ 24*b*(allot A k N p J)^2
    computes : ∀d, costs A J f N d=globB A J f N-globS A J f N + residue A J f N d
    prices : ∀d:ℕ,0<d→‖residue A J f N d‖ ≤ 40*b*(allot A k N p J)^2
lemma fused (Y:A.Makes) (u:k≤ N)(X:Tilted A f J N b)(z:1≤(A.path.rep N p k).p.supportExponent) (x:Envelope f): Burn A J f N b:=by
    let V:= (Y.wilson.represents N p k u).good; let l:= SectorNext.Vacuum.strictly _ Y.wilson N p k u; let e:=radiant_env J r₀ f V l x; have h0:= fare_first J r₀ f V l x z X.tally X.consumes; let _ : IsProbabilityMeasure μ0:= X.problemX
    refine { X with fibre:=tilted_probability r₀ V l J, receives:= slope J r₀ f V l x, kept:=e, holds:=h0, computes:= ?_, prices:=?_ }; swap
    · intro d hd; apply le_trans (norm_integral_le_of_norm_le_const (μ:=μ0) (C:=40*b*ω₀^2) (?_)) (by simp); filter_upwards with o; let x:= remit J r₀ f d o; let a:= remitG J r₀ f o; change ‖x-(z0-t0) o‖≤_; refine ( norm_sub_le_norm_sub_add_norm_sub x a _ ).trans ((add_le_add ( (X.curve d).2.2 o ) ( h0 o ) ).trans ?_)
      have hb: 0≤b:= le_trans (norm_nonneg ( f 1 )) ( X.consumes _ ); have hw:0≤ω₀:= HeatS.σfund (r₀).p _ _ _ ( Real.rpow_nonneg ( inv_nonneg.mpr ( Real.sqrt_nonneg _ ) ) _ ) -- find
      have hle:ω₀^(d+1)≤ω₀^2:= pow_le_pow_of_le_one hw ( X.tally.trans (by norm_num) ) (show 2≤d+1 by omega); nlinarith only [mul_le_mul_of_nonneg_left hle hb]
    intro d
    have m {f g}(w:Envelope f)(v:Envelope g):glob A J N ( f-g )= glob A J N f-glob A J N g:=integral_sub ( intE w μ0 ) ( intE v μ0 )
    unfold costs globB globS residue; rw [ m ((X.curve d).1) (envN e.1 e.2), m e.1 e.2 ]; abel
end First
end YM.Integration.Logwood
