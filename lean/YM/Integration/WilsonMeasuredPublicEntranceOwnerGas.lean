import YM.Integration.WilsonSeparatedPrefixCanonicalDifference
import YM.Integration.WilsonMeasuredPublicEntranceOwner
import YM.MergeProof.Grant

/-! Regroup the genuine canonically forced singleton into the undoubled
finite physical gallery. Every original quiet key and exclusion is kept. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOwnerGas
open Function Finset Lattice Wilson RG Source Labels Marker Extra.Histories Push.Local
open MergeProof MergeProof.Accent Push.GridApprox.Nil
open WilsonMeasuredCoefficientTransport
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{d:ℕ}{F:Labels.Frame G d}{V:Type}[Fintype V][DecidableEq V]{J:Census V}
variable (P:Rep G n)(q:Coefficient F n)(v:V)

def selected (i:V)(b:Box n)(U:Config G n):ℂ:=
  if i=v then profile P.activities q.forced b U else 0

theorem named (b:Box n)(U:Config G n):Mach J (fun i=>selected P q v i b U)=
    Poly.send (J.fire v) (profile P.activities q.forced b U):=by
  classical
  unfold Mach
  rw [Finset.sum_eq_single v]
  · simp [selected]
  · intro i _ hi
    simp [selected,hi]
  · simp

theorem original {a b κ B:ℝ}(valid:P.activities.Valid P.p a b){o:Site n}
    (fee:q.remBound o P κ B)(U:Config G n):
    field (fun t=>bar P.activities J U t+Mach J (fun i=>selected P q v i t U)) (flags P.p.threshold U)=
      Poly.bead J (P.activities.gas P.p U)+Poly.send (J.fire v) (∑'i,q.marked P i U):=by
  classical
  let gas(t:Box n):Poly J:=bar P.activities J U t+Mach J (fun i=>selected P q v i t U)
  have row(t):gas t=Poly.send J.quiet (profile P.activities (fun i=>Complex.ofReal ∘ P.activities.K i) t U)+
      Poly.send (J.fire v) (profile P.activities q.forced t U):=by unfold gas;rw [named];rfl
  have quiet(t):(gas t).part J.quiet=profile P.activities (fun i=>Complex.ofReal ∘ P.activities.K i) t U:=by
    rw [row];simp [Poly.part_plus,Poly.part_send,(J.fire_hot v).symm]
  have hit(t):(gas t).part (J.fire v)=cram (barcode P.activities) (fun i=>q.forced i U) t:=by
    rw [row];simp [Poly.part_plus,Poly.part_send,J.fire_hot,profile]
  have eligible:=mass_crest P.activities valid U
  have zero:=stage₀ P.activities P.p U eligible quiet
  have hot:=stageR P.activities P.p U eligible quiet ((rem_dominated fee).summable U) hit
  have scope₁(t):Scoped ({v}:Set V) (gas t):=by
    rw [row]
    exact scope_plus (scope_send _ _ _ (by simp [Census.quiet])) (scope_send _ _ _ (by simp [Census.fire]))
  have range:Scoped ({v}:Set V) (field gas (flags P.p.threshold U)):=by
    intro s outside
    unfold field
    rw [Poly.part_sum]
    apply sum_eq_zero
    intro t _
    unfold grid
    split
    · exact scope_prod t gas (fun k _=>scope₁ k) s outside
    · rfl
  change field gas (flags P.p.threshold U)=_
  ext1 s
  change _=(Poly.send J.quiet _+Poly.send (J.fire v) _).part s
  rw [Poly.part_plus,Poly.part_send,Poly.part_send]
  by_cases ez:s=J.quiet
  · subst s;simpa only [if_pos rfl,if_true,if_neg (J.fire_hot v).symm,add_zero] using zero
  by_cases ef:s=J.fire v
  · subst s;simpa only [if_neg (J.fire_hot v),if_pos rfl,if_true,zero_add,nickel,Coefficient.marked] using hot
  rw [if_neg ez,if_neg ef,zero_add]
  apply range
  intro bad
  have sub:s.val⊆{v}:=by
    intro i hi
    exact Finset.mem_singleton.mpr (by simpa only [Set.mem_singleton_iff] using bad hi)
  rcases subset_singleton_iff.mp sub with eq|eq
  · exact ez (Subtype.ext eq)
  · exact ef (Subtype.ext eq)

end YM.Integration.WilsonMeasuredPublicEntranceOwnerGas
end
