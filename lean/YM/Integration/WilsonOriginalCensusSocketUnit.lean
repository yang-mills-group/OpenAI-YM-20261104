import YM.Integration.WilsonOriginalCensusPhysicalUnits
import YM.Integration.WilsonIndependentCollarStationEntrance

/-! In the original signed physical basis every nonunit socket of a grade-zero field has zero dose. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusSocketUnit
open Function Finset Lattice Wilson RG Source Extraction Labels Marker
open Next.Foundations WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer WilsonCoeffUV.Embroider
open WilsonReceivedCanonicalVerseBasis WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open OriginalMarkedSourceComet WilsonIndependentCollarPaidWindingPanel PhysicalNext.Repeat.Legato
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open WilsonIndependentCollarOriginalDose (weight)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G)(simple:G.Simple)

include simple in
theorem core (d:ℕ)(small:d<4)(x:R.family.label d):(R.family.labels.level d).core x=0:=by
  let F:=R.family.labels.level d
  have unit:F.core F.e0=0:=by
    funext u
    by_cases hit:u=0
    · subst u
      simp [Frame.core]
    · simp [Frame.core,Function.update,Frame.e0,hit]
  obtain ⟨c,ray⟩:=RG12.unit_spans simple R.family d (R.family.ref d) small x
  rw [ray,map_smul]
  simp [unitVec,map_smul,unit,F]

variable {n:ℕ}(k:Fin n→ℕ)(N per K:ℕ)(v:(j:Fin n)→R.family.label (k j))

include simple in
theorem socket (j:Fin n)(small:k j<4)(s:WilsonOriginalStarLaurentWallet.Socket R (k j)):
    dose R k N per K v j (.inr s)=0:=by
  change WilsonOriginalStarLaurentWallet.coefficient R (k j) _ _ ((R.family.labels.level (k j)).core (v j)) s=0
  rw [core R simple _ small (v j)]
  simp [WilsonOriginalStarLaurentWallet.coefficient]

include simple in
theorem billed (j:Fin n)(small:k j<4)(s:WilsonOriginalStarLaurentWallet.Socket R (k j))(g size:ℝ):
    weight R k N per K v j (.inr s) g size=0:=by
  simp [WilsonIndependentCollarOriginalDose.weight,socket R simple k N per K v j small s]

/-- The remaining unmasked raw choice is the unit at every site and on every held field. -/
theorem bare {side:Side}(j:Fin n)(U:Config G side)(z:Site side):
    dose R k N per K v j (.inl ())=v j 0 ∧
    (raw R k (entry R k j (.inl ()))).unmasked U z=1:=by
  refine ⟨rfl,?_⟩
  simp [WilsonThermometerDeclaredSeeds.entry,raw,RG.Atom.unmasked,RG.Atom.poly,WilsonOriginalStarSceneWords.rank]

variable (m:ℕ)(T:Finset (Fin n))

def retained (a:Choices R k T):Prop:=∀j:T,k j<4 → a j=.inl ()

include simple in
theorem supported (a:Choices R k T)(off:¬retained R k T a):signed R k N per K m v T a=0:=by
  classical
  simp only [retained,not_forall] at off
  obtain ⟨j,small,nonunit⟩:=off
  cases arm:a j with
  | inl u => cases u;exact (nonunit arm).elim
  | inr s =>
    unfold signed
    apply prod_eq_zero (mem_univ j)
    rw [arm,socket R simple k N per K v _ small s,zero_mul]

include simple in
theorem original (read:Choices R k T→ℂ):
    (∑a:Choices R k T,signed R k N per K m v T a*read a)=
      ∑a:Choices R k T with retained R k T a,signed R k N per K m v T a*read a:=by
  classical
  apply (sum_subset (filter_subset _ _) ?_).symm
  intro a _ off
  rw [supported R simple k N per K v m T a (by simpa using off),zero_mul]

end YM.Integration.WilsonOriginalCensusSocketUnit
end
