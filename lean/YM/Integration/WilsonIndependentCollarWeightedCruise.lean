import YM.Integration.WilsonIndependentCollarSubmittedStop

/-! A finite real combination of authenticated ordinary fields continues with
its original coefficients on the fixed quiet Wilson history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentCollarWeightedCruise
open Filter Function Finset Lattice Wilson RG Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Winding
open WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseRegister
open WilsonThermometerDeclaredSeeds WilsonReceivedCanonicalVerseBasis
open WilsonReceivedFixedDigitCanonical (fixed)
open WilsonIndependentCollarOrdinaryCruise (address)
open scoped BigOperators Classical
variable {G:Gauge}{E U:Type} [NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
  {k N b m:ℕ}

theorem original (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (older:b ≤ m)(cut:m ≤ N)(basis:Finset U)(cash:U→ℝ)(field:U→Era G E)
    (hired:∀u∈basis,Auth k (field u)):
    cruises L O N k m b (∑u∈basis,cash u • field u)=
      ∑u∈basis,cash u • cruises L O N k m b (field u):=by
  induction older using Nat.decreasingInduction with
  | self=>simp only [cruises_top]
  | of_succ a before ih=>
    rw [cruises_sub L O N k _ before,ih,
      verse_sum L simple (before.trans_le cut) ratio (fun u mem=>cruising L simple ratio before cut (hired u mem)) cash]
    apply Finset.sum_congr rfl
    intro u hu
    rw [cruises_sub L O N k (field u) before]

variable {n K i c:ℕ}{d h:Fin n→ℕ}

theorem registered (R:Run G)(simple:G.Simple)(vi:i≤c)(ck:c≤K)(kn:K≤N)
    (cells:Digits R.family.path.levels (Fin n))(κ:(j:Fin n)→Knob (h j))(pt:Fin n→Chamber)
    (basis:Finset U)(cash:U→ℝ)(seed:(u:U)→(j:Fin n)→Choice R d j)
    (S:Finset (Fin n))(f:Pen h S→L[ℝ] ℝ)(z:Fin n → Cover):
    let read (j:ℕ)(y:Fin n → Cover)(u:U):=tuftV f (levelsO ((fixed R d κ pt N K j cells (seed u)) y) S)
    cruises R.family.path.levels R.metals.O N (mass d S) c i
      (∑u∈basis,cash u • read c (address R.family.path.levels cells (c-i) i z) u)=
      ∑u∈basis,cash u • read i z u:=by
  intro read
  let L:=R.family.path.levels
  let O:=R.metals.O
  let y:=address L cells (c-i) i z
  obtain ⟨_,_,sale⟩:=WilsonReceivedCanonicalVerseRegister.original R d κ pt 0 (s:=1) zero_lt_one
  have authentic (u:U):Auth (mass d S) (read c y u):=by
    have funded:=sound L O d N cells simple R.alloy.B.ratio (start R d κ pt (seed u)) (sale (seed u)).1
      (K-c) c (by omega)
    exact (placedO _ (funded.level' y) S).tuft f
  rw [original L O simple R.alloy.B.ratio vi (ck.trans kn) basis cash (read c y) (fun u _=>authentic u)]
  apply Finset.sum_congr rfl
  intro u hu
  exact congrArg (fun v=>cash u • v)
    (WilsonIndependentCollarSubmittedStop.continued κ pt cells (seed u) simple vi ck kn S f z).symm

end YM.Integration.WilsonIndependentCollarWeightedCruise
end

