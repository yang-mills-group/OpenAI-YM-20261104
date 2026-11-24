import YM.Integration.WilsonMaxwellThermometerHeard
import YM.Integration.WilsonMaxwellThermometerMonochiral
import YM.Integration.WilsonMaxwellThermometerJetSpan

/-! All physical two-curvature words of engineering cap at most six,
in the seven-face thermometer with two cap-four polar squares. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerQuadratic
open Set Maxwell Maxwell.Free XSpace XSpace.Rose XSpace.Chiral
open WilsonMaxwellThermometerChiralSlots WilsonMaxwellThermometerDifferentiated
open WilsonMaxwellThermometerChiralReading WilsonMaxwellThermometerMonochiral
open WilsonMaxwellThermometerProfile WilsonMaxwellThermometerJetSpan
open scoped BigOperators
variable {G : Gauge} {V : Normalize.Store G} (K : Pick V) (c d : Bool)

private theorem mono {j l : ℕ} (s : Bool) (p : Flavor j) (q : Flavor l)
    (hp : Silent G s p) (hq : Silent G s q) :
    read K (polar G c) (polar G d) (team G p q)=0 :=
  WilsonMaxwellThermometerHeard.of_profile _ _ _ _ (coupled s c d p q hp hq)

private theorem zero_zero' (s t : Bool) (a b : P) :
    read K (polar G c) (polar G d) (team G (slot s a) (slot t b))=0 := by
  by_cases e : t=s
  · subst t; exact mono K c d s _ _ (initial s a) (initial s b)
  exact undifferentiated K c d s t e a b

private theorem one_zero' (s t : Bool) (i : Axis) (a b : P) :
    read K (polar G c) (polar G d) (team G (firstSlot s i a) (slot t b))=0 := by
  by_cases e : t=s
  · subst t; exact mono K c d s _ _ (next (initial s a) _) (initial s b)
  exact first K c d s t e i a b

private theorem one_one' (s t : Bool) (i j : Axis) (a b : P) :
    read K (polar G c) (polar G d) (team G (firstSlot s i a) (firstSlot t j b))=0 := by
  by_cases e : t=s
  · subst t; exact mono K c d s _ _ (next (initial s a) _) (next (initial s b) _)
  exact split K c d s t e i j a b

private theorem two_zero' (s t : Bool) (u : E4) (i : Axis) (a b : P) :
    read K (polar G c) (polar G d) (team G (feed u 1 (firstSlot s i a)) (slot t b))=0 := by
  by_cases e : t=s
  · subst t; exact mono K c d s _ _ (next (next (initial s a) _) _) (initial s b)
  exact second K c d s t e u i a b

private theorem filed {j l : ℕ} (h : j+l≤2) (p : Flavor j) (q : Flavor l)
    (hp : p∈rows j) (hq : q∈rows l) : read K (polar G c) (polar G d) (team G p q)=0 := by
  obtain (rfl|rfl|rfl) : j=0 ∨ j=1 ∨ j=2 := by omega
  all_goals obtain (rfl|rfl|rfl) : l=0 ∨ l=1 ∨ l=2 := by omega
  · obtain ⟨s,a,rfl⟩:=hp; obtain ⟨t,b,rfl⟩:=hq; exact zero_zero' K c d s t a b
  · obtain ⟨s,a,rfl⟩:=hp; obtain ⟨t,i,b,rfl⟩:=hq
    rw [team_swap]; exact one_zero' K c d t s i b a
  · obtain ⟨s,a,rfl⟩:=hp; obtain ⟨t,u,i,b,rfl⟩:=hq
    rw [team_swap]; exact two_zero' K c d t s u i b a
  · obtain ⟨s,i,a,rfl⟩:=hp; obtain ⟨t,b,rfl⟩:=hq; exact one_zero' K c d s t i a b
  · obtain ⟨s,i,a,rfl⟩:=hp; obtain ⟨t,j,b,rfl⟩:=hq; exact one_one' K c d s t i j a b
  · omega
  · obtain ⟨s,u,i,a,rfl⟩:=hp; obtain ⟨t,b,rfl⟩:=hq; exact two_zero' K c d s t u i a b
  · omega
  · omega

theorem complete {j l : ℕ} (h : j+l≤2) (p : Flavor j) (q : Flavor l) :
    read K (polar G c) (polar G d) (team G p q)=0 := by
  let B:=paired K (polar G c) (polar G d) j l
  have H (a : Flavor j) (ha : a∈rows j) : B a=0 := by
    apply LinearMap.ker_eq_top.mp; apply top_unique; rw [← full l (by omega)]
    exact Submodule.span_le.mpr fun b hb => filed K c d h a b ha hb
  have HB : B=0 := by
    apply LinearMap.ker_eq_top.mp; apply top_unique; rw [← full j (by omega)]
    exact Submodule.span_le.mpr H
  change B p q=0; rw [HB]; rfl

end YM.Integration.WilsonMaxwellThermometerQuadratic
