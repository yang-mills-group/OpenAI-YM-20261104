import YM.Integration.WilsonIndependentCollarOpticalTrial
import YM.Integration.WilsonOriginalOpticalMint

/-! The covered, fixed-child, finite trial on the elected original Wilson run. -/
set_option autoImplicit false
set_option maxHeartbeats 260000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarOpticalElected
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonCoeffUV.Embroider
open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords
open scoped Classical BigOperators
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {T:Campaign R} {W:Campaign.Pillars R T}

theorem top_width (A:Levels G)(m:ℕ)(live:5≤A.clock.J (m+1)):crestM A m live≤1:=by
  let j:=A.clock.J (m+1)
  let i:=A.clock.J m
  let K:=A.clock.kernel
  have halved:(cue G K i j (A.clock.adm m) live).outlet≤1:=by
    unfold Tokenizer.outlet;linarith [cue_unit (G:=G) (K:=K) (A.clock.adm m) live]
  change saffron G K i j (A.clock.adm m) live / 2≤1
  have smaller:saffron G K i j (A.clock.adm m) live≤(cue G K i j (A.clock.adm m) live).outlet:=min_le_left .. 
  linarith

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(k D:Fin n→ℕ)(hk:∀x,k x<D x)(κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)
    (e b h:ℕ):
    ∃ P:Credit,∃ B:ℝ,1≤B ∧ ∀ᶠ first:ℕ in atTop,∃ V:Realm G (e+1) Credit.leanC,
      V.draws=R.family.path.levels ∧ V.paid=R.metals.O ∧ V.y=zz R.family.path.levels ∧
      V.anchor=first ∧ Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧
      (∀j (hj:V.anchor≤j),let U:=V.mint j hj
        ∀d z,d≤R.family.path.levels.clock.J (j+1) → z≤R.family.path.levels.clock.J (j+1) →
          let j':=R.family.path.levels.clock.J (j+1)
          let shelves:=widths (teacher (prepared s)) j'
          let out:=WilsonIndependentCollarPrintIncome.issue shelves d z U.gear
          out.fee≤V.y j ∧ out.strip⁻¹≤V.y j ∧
            (∀t, t=R.family.path.levels.clock.J j ∨ t=j' →
              teacherWidth (teacher (prepared s)) R.metals.p.kernel t≤out.strip)) ∧
      ∀(N:ℕ)(cell:Digits V.draws (Fin n)) (q:(j:Fin n)→Choice R k j) (m days:ℕ) (hm:V.anchor ≤ m),
      m+days≤N → ∀Z:ℝ,PadRank V m (m+days) Z →
      Uniform V (itinerary V.draws V.paid k N cell days m (WilsonReceivedCanonicalVerseRegister.start R k κ pt q))
        m hm (P.buy Z*B):=by
  obtain ⟨P,B,one,spend⟩:=WilsonIndependentCollarOpticalTrial.original R D k κ pt e
  refine ⟨P,B,one,?_⟩
  filter_upwards [WilsonOriginalOpticalMint.original paid n k D hk e b h (mass k univ)] with first data
  obtain ⟨V,draw,quiet,age,anchor,school,sale,_,dorm,openings⟩:=data
  refine ⟨V,draw,quiet,age,anchor,school,sale,?_,?_⟩
  · intro j hj U d z hd hz
    obtain ⟨_,_,_,_,_,_,_,plant⟩:=openings j hj
    obtain ⟨cost,allow,_,_,rates⟩:=plant d z hd hz
    rw [age];exact ⟨cost,allow,rates⟩
  · intro N cell q m days hm cut Z room
    obtain ⟨live,top,_,_,_,_,_,_⟩:=openings (m+days) (by omega)
    refine spend V school (fun S=>dorm (mass k S) 0 ?_ (Nat.zero_le _)) N cell q m days hm cut
      (top.le.trans (top_width _ _ live)) Z room (fun j hj _ _=>(openings j hj).choose_spec.2.2.1)
    rw [stairK k (Finset.subset_univ S)];exact Nat.le_add_right ..

end YM.Integration.WilsonIndependentCollarOpticalElected
end
