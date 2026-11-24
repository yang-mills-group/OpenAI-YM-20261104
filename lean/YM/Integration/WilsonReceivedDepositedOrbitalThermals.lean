import YM.Integration.WilsonReceivedDepositedOrbitalSlice

/-! The real thermal board stays in the state when the temporary connected sources are
folded into their original marked subsets. The empty marked face is the full old
vacuum at every retained coupling order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalThermals
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open RG05Readout.Many
open WilsonReceivedDepositedOrbitalSlice
open scoped Classical BigOperators
variable {V W:Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W]
  {A:Census V}{J:Census W}{r:ℕ}

theorem vacant (F:Poly A →ₐ[ℂ] Poly J)(preserve:∀a,(F a).part J.quiet=a.part A.quiet)(x:Grade A r):
    (hom F r x).part (Board J r).quiet=x.part (Board A r).quiet:=by
  rw [←Join.pair_quiet (R:=J) (S:=indices r),←Join.pair_quiet (R:=A) (S:=indices r)]
  exact (at_pair F x _ _).trans (preserve _)

theorem slice_vacuum (x:Grade A r)(t:Index r):slice (Order.denominator x) t=blanked A (slice x t):=by
  apply Marker.Poly.ext
  intro s
  rw [pure_marks]
  exact bottom_value x s t

theorem vacuum (F:Poly A →ₐ[ℂ] Poly J)(preserve:∀a,(F a).part J.quiet=a.part A.quiet)(x:Grade A r):
    hom F r (Order.denominator x)=Order.denominator (hom F r x):=by
  apply Join.both_parts
  intro s t
  change (slice (lift F (Order.denominator x)) t).part s=(slice (Order.denominator (lift F x)) t).part s
  rw [at_slice,slice_vacuum,slice_vacuum,at_slice]
  change (F (algebraMap ℂ (Poly A) ((slice x t).part A.quiet))).part s=
    (algebraMap ℂ (Poly J) ((F (slice x t)).part J.quiet)).part s
  rw [F.commutes,preserve]

theorem ratio (F:Poly A →ₐ[ℂ] Poly J)(preserve:∀a,(F a).part J.quiet=a.part A.quiet)
    (x:Grade A r)(one:UnitLeading x):hom F r (Order.ratio x)=Order.ratio (hom F r x):=by
  apply Order.ratio_unique ((vacant F preserve x).trans one)
  rw [←vacuum F preserve,←map_mul,Order.recovers one]

theorem marked (F:Poly A →ₐ[ℂ] Poly J)(preserve:∀a,(F a).part J.quiet=a.part A.quiet)
    (x:Grade A r)(one:UnitLeading x):hom F r (Order.logMarked x)=Order.logMarked (hom F r x):=by
  unfold Order.logMarked
  rw [log_map (hom F r) (vacant F preserve) (Order.ratio_quiet one),ratio F preserve x one]

variable {Z:Type}[Fintype Z][DecidableEq Z] (J:Census V)(name:Z→Hot J)

omit [Fintype V] in
theorem original_quiet (x:Poly (Stock.census Z)):
    (WilsonReceivedDepositedAlias.fold J name x).part J.quiet=x.part (Stock.census Z).quiet:=by
  rw [WilsonReceivedDepositedAlias.fold,AlgHom.comp_apply,substitute_quiet]
  exact feed_quiet ..

/-- The same thermal order, including its original factorial, before and after all
fixed marked labels are re-expressed. -/
theorem original (x:Grade (Stock.census Z) r)(one:UnitLeading x)(j:ℕ):
    let φ:=WilsonReceivedDepositedAlias.fold J name
    let joint:=hom φ r x
    Order.observe J r (Order.ratio joint) j=φ (Order.observe (Stock.census Z) r (Order.ratio x) j) ∧
    Order.observe J r (Order.logMarked joint) j=φ (Order.observe (Stock.census Z) r (Order.logMarked x) j):=by
  intro φ joint
  constructor
  · exact congrArg (fun z=>Order.observe J r z j) (ratio φ (original_quiet J name) x one).symm |>.trans
      (WilsonReceivedDepositedOrbitalSlice.observe φ _ j)
  · exact congrArg (fun z=>Order.observe J r z j) (marked φ (original_quiet J name) x one).symm |>.trans
      (WilsonReceivedDepositedOrbitalSlice.observe φ _ j)

end YM.Integration.WilsonReceivedDepositedOrbitalThermals
end
