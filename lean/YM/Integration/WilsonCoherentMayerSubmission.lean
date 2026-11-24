import YM.Integration.WilsonCoherentMayerEntry

/-! A finite family of independently registered Wilson sections, on the same
original physical representation as their prior signed partners. The entered
addresses distinguish occurrences when physical sites or bonds coincide. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSubmission
open Function Finset Lattice Wilson RG PhysicalNext.Repeat Legato Lotus
open scoped Classical BigOperators
variable {G:Gauge} {r:Run G} {f:Side} {A:Rep G f} {I:Type} [Fintype I]

structure Submitted (r:Run G) (A:Rep G f) (I:Type) where
  grade:I→ℕ
  site:I→Site f
  label:∀i,r.family.label (grade i)
  phase:I→ℂ →L[ℝ] ℝ
  key:I→ℕ
  separated:Injective key
  covers:∀i,(r.family.localSection (grade i)).footprint (site i)⊆(A.activities.reg (key i)).support
  vacant:∀i,A.activities.E (key i)=0

variable (s:Submitted r A I)
def row (i:I):Leaf A := WilsonCoherentMayerEntry.entered r A (s.key i) (s.site i)
  (s.label i) (s.phase i) (s.covers i) (s.vacant i)
def occupied:Finset (Leaf A):=univ.image (row s)
def read (v:Leaf A) (U:Config G f):ℝ:=
  if h:∃i,row s i=v then let i:=h.choose
    WilsonCoherentMayerEntry.raw r (s.label i) (s.site i) A.p.threshold (s.phase i) U else 0

omit [Fintype I] in
theorem numbered:Injective (row s):=by
  intro i j eq
  apply s.separated
  exact Wing.logKey.inj (congrArg Leaf.turn eq)

theorem at_row (i:I) (U:Config G f) : read s (row s i) U=
    WilsonCoherentMayerEntry.raw r (s.label i) (s.site i) A.p.threshold (s.phase i) U:=by
  have found:∃j,row s j=row s i:=⟨i,rfl⟩
  rw [read,dif_pos found,(numbered s) found.choose_spec]

theorem regular (m:Leaf A) (hm:m∈occupied s) : ∃k,m.turn=.logKey k :=by
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hm
  exact ⟨s.key i,rfl⟩

theorem qualifies (m:Leaf A) (hm:m∈occupied s) (U:Config G f) (h:m.turn.qualifies A U):
    m.ingredient U=read s m U:=by
  obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hm
  rw [at_row]
  exact ((WilsonCoherentMayerEntry.original r A (s.key i) (s.site i) (s.label i) (s.phase i)
    (s.covers i) (s.vacant i) U).2.2 h).1

theorem full (U:Config G f) : (∏m∈occupied s,read s m U)=
    ∏i, s.phase i (Push.Local.presented (r.family.localSection (s.grade i)) (s.site i)
      A.p.threshold (s.label i) U) :=by
  rw [occupied,Finset.prod_image (numbered s).injOn]
  exact Finset.prod_congr rfl fun i _=>at_row s i U

theorem prices : (∏m∈occupied s,m.weight)=∏i,
    WilsonCoherentMayerEntry.wallet r (s.label i) A.p.threshold (s.phase i) :=by
  rw [occupied,Finset.prod_image (numbered s).injOn]
  rfl

def together (old:Team A) (fresh:∀m∈old.own,∀i,m.turn≠(row s i).turn):Team A where
  own := old.own ∪ occupied s
  alone := by
    intro v hv w hw same
    rcases Finset.mem_union.mp hv with hv|hv <;> rcases Finset.mem_union.mp hw with hw|hw
    · exact old.alone hv hw same
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hw
      exact (fresh v hv i same).elim
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
      exact (fresh w hw i same.symm).elim
    · obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hw
      exact congrArg (row s) (s.separated (Wing.logKey.inj same))

theorem registered (old:Team A) (fresh:∀m∈old.own,∀i,m.turn≠(row s i).turn) :
    occupied s⊆(together s old fresh).own ∧ (together s old fresh).own\occupied s=old.own :=by
  constructor
  · exact Finset.subset_union_right
  · ext m
    simp only [together,Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨hm,no⟩;exact hm.resolve_right no
    · intro hm; refine ⟨Or.inl hm,?_⟩
      intro hit;obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hit
      exact fresh _ hm i rfl

end YM.Integration.WilsonCoherentMayerSubmission
