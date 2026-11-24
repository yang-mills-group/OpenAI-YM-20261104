import YM.Integration.WilsonMaxwellThermometerWardReflection

open scoped Classical
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMaxwellThermometerWardClear
open Function Set Filter MeasureTheory Lattice Wilson Push.Mark PertExtension.Orb
open WilsonMaxwellThermometerWardConditional WilsonMaxwellThermometerWardReflection
variable {n:Side}

private theorem step_one (z:Site n) (i:Axis):separation z (z+step i)≤1:=by
  rw [separation_comm,separation,add_comm,add_sub_cancel_right]
  exact pdist_step i

private theorem negate (x y:Site n):separation (-x) y=separation x (-y):=by
  rw [separation,separation,show -x-y= -(x- -y) by abel,pdist_neg]

theorem reflected (r:ℕ) (o:Site n) (e:Edge (Site n)) : far r o (reflect e) ↔ far r (-o) e := by
  change (r<separation (-e.1-step e.2) o ∧ r<separation ((-e.1-step e.2)+step e.2) o) ↔ _
  rw [sub_add_cancel,show -e.1-step e.2= -(e.1+step e.2) by abel,negate,negate,and_comm]
  rfl

private theorem close (r:ℕ) (o:Site n) (e:Edge (Site n)) (bad:¬far r o e):
    separation e.1 o≤r+1:=by
  change ¬(r<separation e.1 o ∧ r<separation (e.1+step e.2) o) at bad
  have h:=separation_triangle e.1 (e.1+step e.2) o
  have s:=step_one e.1 e.2
  omega

private theorem first (p:Face (Per n)) (e:Edge (Site n)) (use:e∈rim p) :
    separation p.1 e.1≤1 := by
  simp only [rim,Finset.mem_insert,Finset.mem_singleton] at use
  rcases use with rfl|rfl|rfl|rfl
  · simp
  · exact step_one _ _
  · exact step_one _ _
  · simp

private theorem conflict (r:ℕ) {o x:Site n} (span:2*r+4<separation o (-o))
    (a:separation x o≤r+2) (b:separation x (-o)≤r+2):False:=by
  have h:=separation_triangle o x (-o)
  rw [separation_comm o x] at h
  omega

theorem original (r:ℕ) (o:Site n) (span:2*r+4<separation o (-o)) :
    Clear r o ∧ (∀e,¬far r o e→far r o (reflect e)):=by
  have around (p:Face (Per n)) (c:Site n)
      (h:¬∀e∈rim p,far r c e):separation p.1 c≤r+2:=by
    push Not at h
    obtain ⟨e,he,bad⟩:=h
    have d:=first p e he
    have t:=close r c e bad
    have tri:=separation_triangle p.1 e.1 c
    omega
  constructor
  · intro p
    by_cases left:∀ e∈rim p,far r o e
    · exact Or.inl left
    refine Or.inr (fun e he=>?_); rw [reflected]
    by_contra bad
    exact conflict r span (around p o left) (around p (-o) fun h=>bad (h e he))
  · intro e bad
    rw [reflected]
    by_contra h
    have a:=close r o e bad
    have b:=close r (-o) e h
    exact conflict r (x:=e.1) span (by omega) (by omega)

end YM.Integration.WilsonMaxwellThermometerWardClear
