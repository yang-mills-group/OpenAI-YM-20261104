import YM.Integration.WilsonCenteredCaptureSlots

/-! Reindex the isolated signed coefficient as the real one-source
`pointValue` of the full native hard array. This retains the original
complement and all disconnected old vacuum factors at the given field. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCapturePush
open Finset Function Lattice RG Wilson Push.Local Planned.GuardedAtom
open WilsonCenteredOriginalCaptureOwner WilsonCenteredCaptureSlots
open WilsonCenteredCaptureCensus
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {ι : Type} (P : Rep G n) (K : Guard.Keeper P.p P.activities)
    (T : ι → Support n) (I : ι → Finset ℕ) (serial : ι × Finset ℕ ↪ ℕ) (U : Config G n)

abbrev Arrived := (z : ι) × Leave P K (T z) (I z) U (fun C => serial (z,C))
abbrev Born := (z : ι) × Enter P (T z) (I z) U

def mark (w : Arrived P K T I serial U) : Key P T I :=
  ⟨(w.1,w.2.val.1),w.2.property.live,w.2.property.kept,w.2.property.hits,w.2.property.split⟩

theorem markedSlot (w : Arrived P K T I serial U) :
    host P K (T w.1) (fun C => serial (w.1,C)) w.2.val.1 =
      slot P K T I serial (mark P K T I serial U w) := dif_pos w.2.property.live

def note (w : Arrived P K T I serial U) : Push.Local.Pointed :=
  let h := slot P K T I serial (mark P K T I serial U w)
  ⟨insert h w.2.val.2,⟨h,mem_insert_self ..⟩⟩

theorem unique : Injective (note P K T I serial U) := by
  rintro ⟨i,⟨⟨C,E⟩,t⟩⟩ ⟨j,⟨⟨B,J⟩,u⟩⟩ eq
  have hk := congrArg (fun x : Push.Local.Pointed => x.2.val) eq
  have same := congrArg Subtype.val ((slot P K T I serial).injective hk)
  change (i,C) = (j,B) at same
  cases same
  have hE := congrArg (fun x : Push.Local.Pointed=> x.1.erase x.2.val) eq
  have freshC := t.fresh
  have freshB := u.fresh
  rw [markedSlot P K T I serial U (⟨i,⟨(C,E),t⟩⟩)] at freshC
  rw [markedSlot P K T I serial U (⟨i,⟨(C,J),u⟩⟩)] at freshB
  simp only [note,Finset.erase_insert freshC,Finset.erase_insert freshB] at hE
  cases hE
  rfl

private theorem entry_eq {x y : Push.Local.Pointed} (h : x.1 = y.1) (j : x.2.val = y.2.val) : x = y := by
  obtain ⟨B,k⟩ := x
  obtain ⟨D,l⟩ := y
  change B = D at h
  cases h
  have eql : k=l := Subtype.ext j
  cases eql
  rfl

theorem zeroOutside (f : ι → Config G n → ℂ) (x : Push.Local.Pointed)
    (no : x ∉ Set.range (note P K T I serial U)) :
    pointValue P.p P.activities (entered P K T I serial f) U x = 0 := by
  by_contra h
  unfold pointValue at h
  split at h
  next adm =>
    by_cases entry : ∃ q,slot P K T I serial q=x.2.val
    · obtain ⟨q,hq⟩ := entry
      let C := q.val.2
      let E := x.1.erase x.2.val
      let z := q.val.1
      have k : host P K (T z) (fun B=>serial (z,B)) C = x.2.val := by
        rw [host,dif_pos q.property.live]
        exact hq
      have tr : Ticket P K (T z) (I z) U (fun B=>serial (z,B)) C E := by
        refine ⟨q.property.live,q.property.kept,q.property.hits,q.property.apart,?_,?_⟩
        · rw [k];exact notMem_erase _ _
        rw [k,Finset.insert_erase x.2.property]
        exact adm
      let w : Arrived P K T I serial U := ⟨z,⟨(C,E),tr⟩⟩
      apply no
      refine ⟨w,?_⟩
      have eq1 : (note P K T I serial U w).1 = x.1 := by
        change insert (slot P K T I serial (mark P K T I serial U w)) E = x.1
        rw [←markedSlot P K T I serial U w]
        change insert (host P K (T z) (fun B=>serial (z,B)) C) E = x.1
        rw [k,Finset.insert_erase x.2.property]
      apply entry_eq eq1
      exact (markedSlot P K T I serial U w).symm.trans k
    rw [outside P K T I serial f x.2.val entry] at h
    exact h (zero_mul _)
  exact h rfl

theorem value (f : ι → Config G n → ℂ) (w : Arrived P K T I serial U) :
    pointValue P.p P.activities (entered P K T I serial f) U (note P K T I serial U w) =
      f w.1 U * ∏ j ∈ (w.2.val.1 ∪ w.2.val.2) \ I w.1, (P.activities.K j U : ℂ) := by
  let q := mark P K T I serial U w
  have key := markedSlot P K T I serial U w
  have paid := w.2.property.admit
  have fresh := w.2.property.fresh
  rw [key] at paid fresh
  unfold pointValue note
  simp only [if_pos paid,Finset.erase_insert fresh]
  rw [registered,payload,←key]
  have t := w.2.property
  have old := WilsonCenteredCaptureReconstruction.emitted P K (T w.1) (I w.1) w.2.val.1 w.2.val.2 U
    (serial (w.1,w.2.val.1)) t.live t.kept t.hits t.split
  rw [host,dif_pos t.live]
  have use := t.fresh; have yes := t.admit
  rw [host,dif_pos t.live] at use yes
  simpa [mark] using old use yes (fun _=>1) (f w.1 U)

/-- The coefficient in the original hard gas is the same single signed
sum over actual before-collection configurations, even at rough fields. -/
theorem whole (f : ι → Config G n → ℂ) :
    (∑' x : Push.Local.Pointed,pointValue P.p P.activities (entered P K T I serial f) U x) =
      ∑' v : Born P T I U, f v.1 U * ∏ j ∈ v.2.val \ I v.1, (P.activities.K j U : ℂ) := by
  let e : Born P T I U ≃ Arrived P K T I serial U := Equiv.sigmaCongrRight
    (fun z=>equivalence P K (T z) (I z) U (fun C=>serial (z,C)))
  rw [←(unique P K T I serial U).tsum_eq (f:=pointValue P.p P.activities (entered P K T I serial f) U)
      (fun x hx=>by by_contra no; exact hx (zeroOutside P K T I serial U f x no))]
  rw [←e.symm.tsum_eq (fun v : Born P T I U=>f v.1 U * ∏ j ∈ v.2.val \ I v.1, (P.activities.K j U : ℂ))]
  apply tsum_congr
  intro w
  exact value P K T I serial U f w

end YM.Integration.WilsonCenteredCapturePush
