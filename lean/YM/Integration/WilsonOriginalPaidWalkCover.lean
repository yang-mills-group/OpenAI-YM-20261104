import YM.Integration.WilsonOriginalCarriedDeckForms

/-! Lift the paid original named walk from its specified copy of the center. -/
set_option autoImplicit false
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonOriginalPaidWalkCover
open Function Finset Lattice Laurent RG Wilson Marker Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Earn
open Further.PhysicalPeriodLimitF933 Macrame Shingle FVA1Physical TwoReset
open scoped BigOperators Classical
variable {G:Gauge} {n N:Side} {V α:Type} [DecidableEq V] {J:Census V} {o:Passport n V}
  (h:n.val∣N.val) (A:Row o J G α) (p:Fin (Pages n N))

theorem projects (x:Site N) (W:Walk) :
    splitter h (stop x W)=stop (splitter h x) W := by
  rw [← wrap_lift x,← wrap_stop_cover,branch,wrap_stop_cover,branch]

def anchor : Site N := (page h A.center p).val

theorem below (x:Site n) : splitter h (page h x p).val=x := by
  simpa only [Shingle.parcel,Finset.mem_filter,Finset.mem_univ,true_and] using (page h x p).property

def site (v:V) : Site N :=
  if v=A.binder.front then anchor h A p else
  if v∈A.mode.val then stop (anchor h A p) (A.binder.path v) else (page h (o.origin v) p).val

theorem at_front : site h A p A.binder.front=anchor h A p := by simp [site]

theorem filed (v:V) : splitter h (site h A p v)=o.origin v := by
  unfold site
  split_ifs with front active
  · subst v
    exact below h p A.center
  · rw [projects,anchor,below]
    exact A.binder.span v active
  · exact below h p _

def index (v:V) : Fin (Pages n N) :=
  (page h (o.origin v)).symm ⟨site h A p v, by simpa only [Shingle.parcel,Finset.mem_filter,Finset.mem_univ,true_and] using filed h A p v⟩

theorem active_page (v:V) : (page h (o.origin v) (index h A p v)).val=site h A p v := by
  unfold index
  simp

def passport : Passport N V where
  origin:=site h A p
  support v:=(Paths.native (site h A p v) (o.wire v)).filter (fun z=>splitter h z∈o.support v)
  wire:=o.wire
  height:=o.height
  born v:=Finset.mem_filter.mpr ⟨Cable.Native.first ..,(filed h A p v) ▸ o.born v⟩
  visits _:=Finset.filter_subset ..
  room:=o.room

def leg (v:V) : Walk := if v=A.binder.front then [] else A.binder.path v

theorem travel (v:V) (member:v∈A.mode.val) :
    stop (anchor h A p) (leg A v)=site h A p v := by
  by_cases front:v=A.binder.front <;> simp [leg,site,front,member,stop]

def row : Row (passport h A p) J G α :=
  { A with binder :=
      { mode:=A.mode
        front:=A.binder.front
        east:=A.binder.east
        path:=leg A
        span:=fun v hv=>by
          change stop (site h A p A.binder.front) (leg A v)=site h A p v
          rw [at_front]
          exact travel h A p v hv
        extra:=A.binder.extra } }

theorem centered : (row h A p).center=anchor h A p:=at_front h A p

theorem length : (row h A p).length ≤ A.length := by
  unfold Row.length Binder.length
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro v _
  change (leg A v).length+o.height v ≤ (A.binder.path v).length+o.height v
  apply Nat.add_le_add_right
  by_cases front:v=A.binder.front <;> simp [leg,front]

theorem letter (g:ℝ) (U:Config G N) :
    Loan.letter (row h A p).lamp (row h A p).atom (row h A p).center g U=
      Loan.letter (TwoReset.copy h A p).lamp (TwoReset.copy h A p).atom (TwoReset.copy h A p).center g U := by
  rw [centered]
  rfl

end YM.Integration.WilsonOriginalPaidWalkCover
