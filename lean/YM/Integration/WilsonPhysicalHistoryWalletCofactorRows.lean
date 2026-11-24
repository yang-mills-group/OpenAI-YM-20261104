import YM.Integration.WilsonPhysicalHistoryWalletSum
import YM.Integration.WilsonOffsetPhysicalPairWick

/-! Each actual two-word complex source in the physical terminal expansion
is reconstructed from the two measured quadratures on the same path. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletCofactorRows
open Function Filter Finset MeasureTheory Lattice RG Wilson Source Labels Next.Foundations
open OPE OPE.Therm WilsonCoeffUV PhysicalNext.Repeat.Legato RGComparison.Core16.Spool
open WilsonReportForwardTransfer WilsonConditionalTaylorLabels WilsonOffsetJointRoster
open WilsonOffsetPhysicalPair WilsonOffsetPhysicalPairWick WilsonPhysicalHistoryWalletSignedPair
open scoped BigOperators Classical
variable {G : Gauge} {d h : ℕ}

def word {f : Side} (t : Index G d h) (x z e : Site f) (U : Config G f) : ℂ :=
  planted t.1 t.2 x z U - planted t.1 t.2 x e U

private theorem located {f : Side} (t : Index G d h) (x z e : Site f) :
    Function.update (seats t.1 t.2 x e) (slot t) z = seats t.1 t.2 x z := by
  funext l
  fin_cases l <;> simp [seats,slot,Function.update]

theorem placed {f : Side} (t : Index G d h) (x z e : Site f) (U : Config G f) :
    field (two t.1 t.2) (univ.erase (slot t)) (seats t.1 t.2 x e) U *
      (one (two t.1 t.2) (slot t) z U-one (two t.1 t.2) (slot t) e U) =
    word t x z e U := by
  have E:=paired (two t.1 t.2) univ (slot t) (mem_univ _) (seats t.1 t.2 x e) z e U
  rw [located t x z e,located t x e e] at E
  exact E.symm

theorem shore {f : Side} (t : Index G d h) (x z e : Site f) : Continuous (word t x z e) := by
  have one (y : Site f) : Continuous (planted t.1 t.2 x y) :=
    tally_cont (packet ⟨two t.1 t.2,univ⟩) (fun i=>seats t.1 t.2 x y i.val)
  exact (one z).sub (one e)

def component (R : Run G) {N per j u : ℕ} (ju : j ≤ u)
    (t : Index G d h) (x z e : Site (R.family.side (u+1) per)) (part : Bool) : Config G (R.family.side j per)→ℂ :=
  response R (N:=N) ju (two t.1 t.2) univ (seats t.1 t.2 x e) (slot t) z e part

theorem recovered (R : Run G) {N per j u : ℕ} (live : u<N) (ju : j ≤ u)
    (t : Index G d h) (x z e : Site (R.family.side (u+1) per)) :
    exterior (C:=R.family) (N:=N) (ju.trans u.le_succ) (word t x z e) =
      fun V=>component R (N:=N) ju t x z e false V + Complex.I*component R (N:=N) ju t x z e true V := by
  let plane := fun part U=>(↑(look part (word t x z e U)):ℂ)
  have split : word t x z e = fun U=>plane false U+Complex.I*plane true U := by
    funext U
    change word t x z e U = (↑((word t x z e U).re):ℂ) + Complex.I*(↑((word t x z e U).im):ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im _).symm
  letI : IsProbabilityMeasure (scene R.family.path N per (u+1)) := probability R.makes.wilson live
  have fin (part : Bool) : Integrable (plane part) (scene R.family.path N per (u+1)) :=
    (Complex.continuous_ofReal.comp ((look part).continuous.comp (shore t x z e))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have eval (part : Bool) : exterior (C:=R.family) (N:=N) (ju.trans u.le_succ) (plane part) =
      component R (N:=N) ju t x z e part := by
    unfold component response
    apply congrArg (fun f=>exterior (C:=R.family) (N:=N) (ju.trans u.le_succ) f)
    funext U
    rw [placed t x z e U]
  rw [split,WilsonPhysicalHistoryWalletSum.added R (ju.trans u.le_succ) live _ _ (fin false) ((fin true).const_mul _),
    WilsonPhysicalHistoryWalletSum.scaled R (ju.trans u.le_succ) live Complex.I (plane true),eval false,eval true]

end YM.Integration.WilsonPhysicalHistoryWalletCofactorRows

