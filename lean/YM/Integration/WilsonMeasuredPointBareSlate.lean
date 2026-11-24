import YM.Integration.WilsonMeasuredPointBareWords
import YM.Integration.WilsonOlderFreshGraphSlate

/-! A pre-period, registered Wilson word catalogue for the literal upper source. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPointBareSlate
open Function Finset Lattice Wilson RG Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PertExtension ActualRunCurvaturePackets NativeCurvatureTensor
open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Poetry
open WilsonMeasuredPointBareWords WilsonOlderFreshGraphSlate
open scoped Classical BigOperators

variable {G:Gauge}{k:ℕ}
def scaled (t:ℝ)(A:Atom G k):Atom G k:=⟨A.leg,fun j=>t*A.coeff j⟩

theorem poly (t:ℝ)(A:Atom G k)(x:Fin k → G.Color):(scaled t A).poly x=t*A.poly x:=by
  unfold Atom.poly scaled
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro j _;dsimp only;ring

theorem lawful (t:ℝ)(A:Atom G k)(h:A.Invariant):(scaled t A).Invariant:=by
  intro g x
  rw [poly,poly,h]

variable (R:Run G)(d:ℕ)
local notation "F₀"=>R.family.labels.level d
abbrev Row (j:(F₀).Index)(e:ℕ):=
  {m:Term R d j // WilsonMeasuredPointBareWords.rank R d j m=e+ActualRunGradedKernels.rank R d j}

def lamp (j:(F₀).Index)(f:ℝ)(m:Term R d j):Lantern G Unit:=
  ⟨WilsonMeasuredPointBareWords.rank R d j m,scaled (f*weight R d j m) (atom R d j m),[(0,())]⟩

def roll (j:(F₀).Index)(f:ℝ)(e:ℕ):Poetry.Roll G Unit:=
  ⟨Row R d j e,fun m=>lamp R d j f m.val⟩

def wage (j:(F₀).Index)(f:ℝ)(e:ℕ)(σ:ℝ):ℝ:=
  ∑m:Row R d j e,(lamp R d j f m.val).money σ

theorem paid (j:(F₀).Index)(f:ℝ)(e:ℕ)(σ:ℝ):
    (roll R d j f e).Faith {()} () (e+d+2) σ (wage R d j f e σ):=by
  constructor
  · intro m
    change (lamp R d j f m.val).Bears {()} () (e+d+2)
    constructor
    · have h:=m.property
      have q:(ActualRunGradedKernels.rank R d j) ≤ d:=WardBin.basis_degree j
      change WilsonMeasuredPointBareWords.rank R d j m.val + 1 ≤ e+d+2
      omega
    · intro j
      cases j
      simp [lamp,swallow,Focus.tally,Focus.calls]
    · simp [lamp]
  · refine ⟨fun z=> (lamp R d j f z.val).fee_nn σ,?_,?_⟩
    · change Summable (fun m:Row R d j e=>(lamp R d j f m.val).money σ)
      exact (hasSum_fintype _).summable
    · change ∑'m:Row R d j e,(lamp R d j f m.val).money σ ≤ _
      rw [tsum_fintype];exact le_rfl

def book (j:(F₀).Index)(f:ℝ)(Q:ℕ)(σ:ℝ)(positive:0<d):Copy G d Q σ where
  roll l:=roll R d j f l.val
  fare l:=wage R d j f l.val (2*σ)
  paid l:=paid R d j f l.val (2*σ)
  legal _ i:=lawful (f*weight R d j i.val) _ (invariant R d j i.val)
  positive:=positive

theorem uncut (j:(F₀).Index)(f:ℝ)(e:ℕ)(m:Row R d j e){n:Side}(z:Site n)(U:Config G n):
    ((roll R d j f e).leg m).atom.unmasked U z=
      f*weight R d j m.val*(atom R d j m.val).unmasked U z:=by apply poly

end YM.Integration.WilsonMeasuredPointBareSlate
