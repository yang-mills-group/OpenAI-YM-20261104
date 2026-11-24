import YM.Integration.WilsonMaxwellThermometerWardSampler
import YM.Integration.WilsonMaxwellThermometerWardClear
import YM.PertExtension.Normalized

/-! Resample the original (unfixed) inversion edge orbits by the literal
ordinary Wilson links on the source collar. Both reflected copies share the
same interior variable and all complementary orbit fields remain fixed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerWardPair
open Function Set Filter MeasureTheory Lattice Wilson PertExtension.Orb
open WilsonMaxwellThermometerWardConditional WilsonMaxwellThermometerWardReflection
open WilsonMaxwellThermometerWardSampler
open scoped Classical Topology
variable {G:Gauge} {n:Side}

def supplied (r:ℕ) (o:Site n) (y:Held G r o) (v:Free G r o):Config G n:=
  liftLinks (emit r o ((chamber r o).symm (y,v)))

def base (r:ℕ) (o:Site n) (y:Held G r o):Config G n:=supplied r o y 1

theorem reflected (he:Even n.val) (q:OEdge n→G.El):mirror (liftLinks q)=liftLinks q:=by
  funext e
  change (liftLinks q (reflect e))⁻¹=liftLinks q e
  rw [lift_flip he,inv_inv]

private theorem choice (r:ℕ) (o:Site n) (e:Edge (Site n)):
    pick r o (index e)=e ∨ pick r o (index e)=reflect e:=by
  by_cases k:turn r o (index e)
  · rw [pick,if_pos k]
    change reflect (eR e)=e ∨ reflect (eR e)=reflect e
    rcases eR_spec e with h|h
    · exact Or.inr (congrArg reflect h)
    · exact Or.inl ((congrArg reflect h).trans (reflect_reflect e))
  · rw [pick,if_neg k]
    exact eR_spec e

theorem fixed (r:ℕ) (o:Site n) (he:Even n.val) (away:∀e,¬far r o e→far r o (reflect e))
    (y:Held G r o) (v:Free G r o): supplied r o y v=twins r o (base r o y) v:=by
  let B:=base r o y
  let Z:=supplied r o y v
  have near (e:Edge (Site n)) (h:¬far r o e): Z e=v ⟨e,h⟩:=by
    rw [show Z e= ((chamber r o).symm (y,v)) e from received r o away _ e h]
    change (if k:far r o e then y ⟨e,k⟩ else v ⟨e,k⟩)=_
    rw [dif_neg h]
  have center (e:Edge (Site n)) (h:¬far r o e): single r o B v e=v ⟨e,h⟩:=by
    change (if k:far r o e then B e else v ⟨e,k⟩)=_
    rw [dif_neg h]
  have outside (e:Edge (Site n)) (h:far r o e) (ht:far r o (reflect e)): Z e=B e:=by
    have touch:far r o (pick r o (index e)) := (choice r o e).elim (fun h' =>h'.symm ▸h) (fun h'=>h'.symm ▸ht)
    let a:=pick r o (index e)
    have keep : (chamber (G:=G) r o).symm (y,v) a = (chamber (G:=G) r o).symm (y,1) a:=by
      change (if h:far r o a then y ⟨a,h⟩ else v ⟨a,h⟩)=(if h:far r o a then y ⟨a,h⟩ else 1)
      rw [dif_pos touch,dif_pos touch]
    change liftLinks (emit r o ((chamber r o).symm (y,v))) e = liftLinks (emit r o ((chamber r o).symm (y,1))) e
    simp only [liftLinks,emit,orient,←show a=pick r o (index e) from rfl,keep]
  funext e
  change Z e=if far r o e then mirror (single r o B v) e else single r o B v e
  by_cases h:far r o e
  · rw [if_pos h]
    by_cases ht:far r o (reflect e)
    · exact (outside e h ht).trans ((congrFun (reflected he _) e).symm.trans
        (congrArg Inv.inv (held r o B v _ ht)).symm)
    · have flip : Z e=(Z (reflect e))⁻¹:=(congrFun (reflected he _) e).symm
      exact flip.trans (congrArg Inv.inv ((near _ ht).trans (center _ ht).symm))
  · rw [if_neg h,near e h,center e h]

theorem density (r:ℕ) (o:Site n) (even:Even n.val) (span:2*r+4<separation o (-o))
    (y:Held G r o) (v:Free G r o) (s:ℝ):
    preDensity s (supplied r o y v)=Real.exp ((s^2)⁻¹/2*energy (base r o y))*
      bare ((s^2)⁻¹) (single r o (base r o y) v):=by
  obtain ⟨clear,away⟩:=WilsonMaxwellThermometerWardClear.original r o span
  rw [fixed r o even away]
  convert! weight r o clear (base r o y) (reflected even _) v ((s^2)⁻¹) using 1
  unfold preDensity bare
  congr 1
  ring

end YM.Integration.WilsonMaxwellThermometerWardPair
