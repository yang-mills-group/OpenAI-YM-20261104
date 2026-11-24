import YM.Integration.WilsonThermometerPositionFilmBank
/-! Actual first chronological marked coefficient at the moving source's original position. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionFilmOpening
open Function Filter Finset Lattice Wilson Exterior Precision Tree Marker Multi
open Comparison.RG02 Comparison.RG02.Bulk Comparison.RG02.Adjacent Comparison.RG02.Symmetry
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Binding RegulatorIR.Geometry
open PertExtension.Series PertExtension.Series.Tested Booth Pipeline Period.Field RG
open WilsonThermometerOriginalCoveredRows YM.Primitives.GCC.Anchor
open scoped Classical Topology BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] [Fintype I] {X:Type} {j:X→ℕ} {n:Page j→Side}
  {Q:KernelChoices} {Γ:RG.History G} {E:Circuit j n} (K:Bulk.Chain Γ) (P:SeriesT E Q Γ)
  (S:Census I) (u:I) {m:ℕ} (B:X→Boot.Scout (G:=G) m) (L:Page j→Binding.Scale) (per r:ℕ) (T:See.Times L r)
  (Z:See.Agenda P S per) (law:See.Setup K P S u B (p:=per) L r T Z)
  (v:X) (moves:0<j v)

def flap := (⟨v,0,moves⟩ : Flap j)
local notation "k" => flap v moves
local notation "ker" => P.readyKin E Γ K per k
local notation "tree" => Halo.bios (P.stepData E Γ per k)
local notation "draw" => directive (P.stepData E Γ per k)
local notation "record" => Γ.S.side (P.vol (k).next) per
local notation "U" => Boot.ink S u Γ (P.vol (k).next+1) per (B v)

omit [Fintype I] in
private theorem castInk (a b:ℕ) (t:a=b) (B₀:Boot.Scout (G:=G) m) :
    See.castF (X:=fun i=>Colors S G (Γ.S.side i per)) t (Boot.ink S u Γ a per B₀)=Boot.ink S u Γ b per B₀ := by
  subst b
  rfl

include law in
theorem before : See.before P k (Z (k).prev)=U := by
  have h:Z (k).prev=Boot.ink S u Γ (P.vol (k).prev) per (B v) := law.top v
  change See.castF (X:=fun i=>Colors S G (Γ.S.side i per)) (P.links k) (Z (k).prev)=_
  rw [h]
  exact castInk S u per _ _ (P.links k) (B v)

variable (live : 0 < r) (D:BudgetPoint)

include law live D in
theorem original (x:fieldDir G record 1) :
    (∀ b:Fin 2, See.noseC S u (T.cloth (k).next) (Z (k).next) b.val x=
       Orbit.words ker tree draw U r (S.fire u) b.val x) := by
  have post:=WilsonThermometerOriginalFilmStep.marked K P S u L per r T k (Z (k).prev) (Z (k).next)
    (law.walks k) live D (law.allows (k).prev).1 x
  have clock:T.cloth (k).prev=Boot.dormant := T.top v
  have zero:deriv (T.cloth (k).prev).rating 0=0 := by rw [clock]; exact deriv_const ..
  rw [zero,neg_zero,zero_smul,map_zero,add_zero] at post
  unfold WilsonThermometerOriginalFilmStep.old WilsonThermometerOriginalFilmStep.slope at post
  rw [before K P S u B L per r T Z law v moves] at post
  have values:=WilsonThermometerOriginalFilmRows.occupied ker tree draw U r live (S.fire u) x
  intro b
  fin_cases b
  · exact post.1.trans values.1.symm
  · exact post.2.trans values.2.symm

private theorem sameDate (N N' i per:ℕ) (fine:i<N) (fine':i<N') (eq:N=N')
    (Y:Colors S G (Γ.S.side (i+1) per)) (r l:ℕ) (x:fieldDir G (Γ.S.side i per) 1) :
    Orbit.words (K.step N i per fine) (Halo.bios (Γ.levels.clock.op i per)) (directive (Γ.levels.clock.op i per))
      Y r (S.fire u) l x=Orbit.words (K.step N' i per fine') (Halo.bios (Γ.levels.clock.op i per))
      (directive (Γ.levels.clock.op i per)) Y r (S.fire u) l x := by
  subst N'
  rfl

include law live D in
theorem dated (x:fieldDir G record 1) (b:Fin 2) :
    See.noseC S u (T.cloth (k).next) (Z (k).next) b.val x =
       Orbit.words (K.step (P.vol (k).next+1) (P.vol (k).next) per (Nat.lt_succ_self _)) tree draw U r (S.fire u) b.val x := by
  refine (original K P S u B L per r T Z law v moves live D x b).trans ?_
  have changed:P.start E Γ v=P.vol (k).next+1:=P.links k
  exact sameDate K S u _ _ _ per (P.fresh E Γ k) (Nat.lt_succ_self _) changed U r b.val x

end YM.Integration.WilsonThermometerPositionFilmOpening
