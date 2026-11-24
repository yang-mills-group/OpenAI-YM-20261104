import YM.Integration.WilsonMovingForkProbeDates
import YM.Integration.WilsonAddressedPublicHomeCard

/-! The measured far field is the same microscopic input of the full and
all reflected observations, on its own real-radius book. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkExactHomes
open RG Wilson Source Maxwell Maxwell.Free RG05Readout Climb GapsContact.Seams
open Function Filter Set Lattice Extraction Table Spec PhysMS Trace Trace.Pilot
open GapsContact GapsContact.Ascent OPE RG16 RG16.Literal RG17 FVA2 FVA2.Register MS MS.Land
open PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourSquare
open WilsonMovingForkProbeMaster WilsonMovingForkProbeDates WilsonMovingForkLocalReceipt
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonMovingForkPositionIntegrals (nearTags twoTags)
open WilsonOriginalTwoFlatPublicBooks (Book)
open private whole_right from YM.Integration.WilsonMovingForkProbeMaster
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  (J:ℝ→tower S)(Z:WilsonPrescription G){n h:ℕ}{P:Type}
  {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{z:Trace.Terrace.Arch R.family}
  (d:Fin n→ℕ){δ:ℝ}{T:ℕ}
  (books:(s:{σ:ℝ //0<σ ∧ σ<δ})→Book F (l:=l) H z (cap h d) T s.val)
  (r t:{σ:ℝ //0<σ ∧ σ<δ})(v:∀i,Free R.family (d i))(a:P→Free R.family h)

abbrev far (j:P):Seat G n h P:=some (.inr (.inr j))

def enrolled (weak:Seat G n h P→Bool)(i:Seat G n h P):=
  ((books (dates r t i)).rows (bound (P:=P) d i)).arm (weak i)
    (homogeneous F J Z (dates r t i).val (grade d i) (dose d v a i))

abbrev outer (weak:Seat G n h P→Bool)(j:P):=
  ((books t).rows (bound (G:=G) (h:=h) (P:=P) d (far (G:=G) (h:=h) (n:=n) j))).arm (weak (far (G:=G) (h:=h) (n:=n) j)) (homogeneous F J Z t.val h (a j))

theorem registered (weak:Seat G n h P→Bool)(j:P)(k:Dframe.Toon G h):
    (books t).W.wheel.r=t.val ∧
    let E:=outer F J Z d books t a weak j
    Tendsto E.source (l:Filter (ℕ×ℕ)) (𝓝 E.label) ∧ S.project h E.label=homogeneous F J Z t.val h (a j) ∧
    HEq (enrolled F J Z d books r t v a weak (WilsonMovingForkProbeMaster.whole j (Fin.natAdd n 0))) E ∧
    HEq (enrolled F J Z d books r t v a weak (pair k j 1)) E ∧
    physical F J Z (bound (P:=P) d) (dose d v a) (dates r t) (WilsonMovingForkProbeMaster.whole j)=
        nearTags F J d h Z (r:=r.val) (t:=t.val) v (a j) ∧
    physical F J Z (bound (P:=P) d) (dose d v a) (dates r t) (pair k j)=
        twoTags F J h Z r.val t.val (a j) k:=by
  refine ⟨(books t).active,?_⟩
  intro E
  refine ⟨E.approaches,E.represents,?_,?_,WilsonMovingForkProbeDates.whole F J Z r t d v a j,
    WilsonMovingForkProbeDates.gram F J Z r t d v a k j⟩
  · rw [whole_right]
    rfl
  · rfl

theorem shared {A:Seat G n h P→Sort*}(entry:∀i,A i)(j:P)(k:Dframe.Toon G h):
    HEq (entry (WilsonMovingForkProbeMaster.whole j (Fin.natAdd n 0))) (entry (far (G:=G) (h:=h) (n:=n) j)) ∧
    HEq (entry (pair k j 1)) (entry (far (G:=G) (h:=h) (n:=n) j)):=by
  rw [whole_right]
  exact ⟨HEq.rfl,HEq.rfl⟩

end YM.Integration.WilsonMovingForkExactHomes
end
