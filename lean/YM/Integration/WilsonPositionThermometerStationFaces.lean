import YM.Integration.WilsonPositionThermometerStationUnit

/-! The same three corrected physical fields and the literal unit on all
seven cutoff faces of the original position thermometer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationFaces
open Function Filter Set Finset Table Climb Trace Trace.Pilot Next.UVStress PhysMS
open MergeProof.East Maxwell XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerOrientedStation WilsonPositionThermometerReading
open scoped Topology Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    {Y : Ultrafilter (ℕ × ℕ)} {H : (Bel C.book).Hierarchy}

theorem original_leg (s : Badge) (i : Fin 3) : leg C s i =
    if i ∈ s then leg C univ i else (Bel C.book).unit 6 := by
  split_ifs with hi
  · apply Maxwell.Free.address_inj C.labels 6
    rw [literal,occupied]
    simp [Rose.missing,hi]
  · apply Maxwell.Free.address_inj C.labels 6
    rw [literal,Maxwell.Free.unit_address]
    simp [Rose.missing,hi]
    rfl

variable {d : ℕ} (A : Filing C d (Fin 3))

def masked (v : Fin 3 → (Bel C.book).Field d) (i : Badge × Fin 3) : (Bel C.book).Field d :=
  if i.2 ∈ i.1 then v i.2 else (Bel C.book).unit d

def roster : Filing C d (Badge × Fin 3) :=
  ⟨A.horizon,A.level,A.grade,A.station,A.lift,masked A.vector⟩

private theorem limit_unit {k : ℕ} (V : Vane C k) (j : Fin (k+1)) (L : Lifts C k)
    (cal : C.Makes) (prior : (Y : Filter _) ≤ f.fuse) (checked : V.checked f H k)
    (limit : Tendsto V.wheel.atCut (Y : Filter _) (𝓝 L)) :
    L j ((Bel C.book).unit j)=C.book.scalar j := by
  have cut := (WilsonPositionThermometerStationUnit.original V j cal checked).filter_mono prior
  have fn : Continuous (fun T : Lifts C k => T j ((Bel C.book).unit j)) :=
    (continuous_apply j).clm_apply continuous_const
  exact tendsto_nhds_unique (fn.continuousAt.tendsto.comp limit)
    (tendsto_const_nhds.congr' (cut.mono fun _ K => K.1.symm))

theorem filed (cal : C.Makes) (prior : (Y : Filter _) ≤ f.fuse)
    {u : Fin 3 → (Bel C.book).Field d} {P : tower S} {m : ℕ} {r : ℝ}
    (h : Filed (f:=f) (Y:=Y) H u r P m A)
    (unit : P d ((Bel C.book).unit d)=S.unit d) :
    Filed (f:=f) (Y:=Y) H (masked u) r P m (roster A) := by
  obtain ⟨k,j,eq,V,L,v⟩ := A
  subst d
  have exact_unit := limit_unit V j L cal prior h.2.1 h.2.2.2.1
  refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
  rintro ⟨s,i⟩
  change P j (masked u (s,i))=S.project j (L j (masked v (s,i))) ∧
    ‖masked v (s,i)-masked u (s,i)‖ ≤ costHint m
  by_cases hi : i ∈ s
  · simpa only [masked,if_pos hi] using h.2.2.2.2 i
  · simp only [masked,if_neg hi,unit,exact_unit,sub_self,norm_zero]
    exact ⟨rfl,(cost_pos m).le⟩

end YM.Integration.WilsonPositionThermometerStationFaces
end
