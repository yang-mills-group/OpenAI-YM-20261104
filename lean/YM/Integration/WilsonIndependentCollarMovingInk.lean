import YM.Integration.WilsonIndependentCollarPaidInk

/-! The moving preselected original trial and the sum of its actual printed
ink. The physical exponent is arbitrary and independent of the Taylor order. -/
set_option autoImplicit false
set_option maxHeartbeats 360000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMovingInk
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar WilsonCoeffUV.Embroider
open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
open WilsonReceivedFixedDigitHistory WilsonReceivedCanonicalVerseBasis
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds WilsonOriginalStarSceneWords
open WilsonIndependentCollarRootedWidth WilsonIndependentCollarPaidInk
open scoped Classical BigOperators Topology
universe u
variable {G:Gauge} {a:Axis} {simple:G.Simple} {ε:ℝ}
variable {s:WilsonOriginalAllOrderCourse.Schedule G} {R:Run G} {T:Campaign R} {W:Campaign.Pillars R T}

theorem original (paid:WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n:ℕ)(k D:Fin n→ℕ)(hk:∀x,k x<D x)(κ:(j:Fin n)→Knob (D j))(pt:Fin n→Chamber)(e b h:ℕ):
    let L:=R.family.path.levels
    ∃B:ℝ,1≤B ∧ ∀ᶠ first:ℕ in atTop,∃V:Realm G (e+1) Credit.leanC,
      V.draws=L ∧ V.paid=R.metals.O ∧ V.y=zz L ∧ V.anchor=first ∧
      Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧
      ∀(S:Finset (Fin n))(v:Fin n),v∈S → ∀(A δ:ℝ),0≤A → 0<δ →
        ∀ᶠ m:ℕ in atTop,∀(hm:V.anchor ≤ m)(days N:ℕ)(β:ℝ),
          m+days≤N → L.clock.hatBeta (m+1)/2≤β →
          L.S.scale (m+days)-L.S.scale m≤A*(1+Real.log (L.clock.hatBeta (m+1))) →
          let U:=V.mint m hm
          let j':=L.clock.J (m+1)
          let w:=widths (teacher (prepared s)) j'
          let out:=WilsonIndependentCollarPrintIncome.issue w (e+1) (mass k S) U.gear
          let t:=rooted S.card out.strip
          0<t ∧ t⁻¹≤(S.card+1)*V.y m ∧
          (∀j,j=L.clock.J m ∨ j=j' → teacherWidth (teacher (prepared s)) R.metals.p.kernel j≤out.strip) ∧
          ∀ (cell:Digits V.draws (Fin n))(q:(j:Fin n)→Choice R k j),
            Income U.gear w (e+1) (mass k S) S v
              (itinerary V.draws V.paid k N cell days m (WilsonReceivedCanonicalVerseRegister.start R k κ pt q))
              ((Real.sqrt β)^δ*B^S.card):=by
  intro L
  obtain ⟨P,B,one,finance⟩:=WilsonIndependentCollarOpticalTrial.original R D k κ pt e
  refine ⟨B,one,?_⟩
  filter_upwards [WilsonOriginalOpticalMint.original paid n k D hk e b h (mass k univ)] with first data
  obtain ⟨V,draw,chart,clock,anchor,school,sale,_,dorm,opens⟩:=data
  refine ⟨V,draw,chart,clock,anchor,school,sale,?_⟩
  intro S v front A δ Apos δpos
  let F:=WilsonIndependentCollarInkPrice.cost G P (mass k S) (e+1) S.card (Fintype.card (S.erase v))
  have fit:= (L.fits.deep.comp (tendsto_add_atTop_nat 1)).eventually_ge_atTop (max (e+1) (mass k S))
  filter_upwards [WilsonIndependentCollarOpticalSpan.original R simple F A Apos δ δpos,fit] with m quote stage
  intro hm days N β cut thermal span U j' w out t
  obtain ⟨Z,room,fee⟩:=quote e V hm draw clock days β thermal span
  have live: max (e+1) (mass k S)≤j':=stage
  obtain ⟨opening,mark,twice,radial,_,_,_,compiled⟩:=opens m hm
  obtain ⟨cost,strip,_,_,teacherP⟩:=compiled (e+1) (mass k S) ((le_max_left ..).trans live) ((le_max_right ..).trans live)
  have head:U.σ≤1:=mark.le.trans (WilsonIndependentCollarOpticalElected.top_width _ _ opening)
  have own:out.fee≤V.y m:=by rw [clock];exact cost
  have wage:out.strip⁻¹≤V.y m:=by rw [clock];exact strip
  have gather:=WilsonIndependentCollarRootedWidth.original w U.gear U.σ U.width twice (e+1) (mass k S) S.card
  refine ⟨gather.1,gather.2.2.2.trans (mul_le_mul_of_nonneg_left wage (by positivity)),teacherP,?_⟩
  intro cell q
  let Y:=WilsonReceivedCanonicalVerseRegister.start R k κ pt q
  let X:=itinerary V.draws V.paid k N cell days m Y
  obtain ⟨liveTop,top,_,_,_,_,_,_⟩:=opens (m+days) (by omega)
  have upper:Uniform V X m hm (P.buy Z*B):=by
    apply finance V school (fun s=>dorm (mass k s) 0 ?_ (Nat.zero_le _)) N cell q m days hm cut
      (top.le.trans (WilsonIndependentCollarOpticalElected.top_width _ _ liveTop)) Z room
      (fun j hj _ _=>(opens j hj).choose_spec.2.2.1)
    rw [stairK k (Finset.subset_univ s)];exact Nat.le_add_right ..
  have seed:Wellness k Y:=((WilsonReceivedCanonicalVerseRegister.original R k κ pt e (s:=1) zero_lt_one).choose_spec.2 q).1
  have planted:Wellness k X:=sound V.draws V.paid k N cell V.hG V.green Y seed days m cut
  have yr:V.y m≤Z:=room.year m le_rfl (by omega)
  have filed:=WilsonIndependentCollarPaidInk.dated V w m hm k S v front X
    (fun y=>planted.level' y S) P B Z (zero_le_one.trans one) ((V.depth m hm).trans yr)
    yr upper twice head own wage
  intro o j hj r word z
  obtain ⟨M,atoms,sum⟩:=filed.2.2 o j hj r
  exact ⟨M,atoms,sum.1,sum.2.1,sum.2.2.trans (mul_le_mul_of_nonneg_right fee (pow_nonneg (zero_le_one.trans one) _))⟩

end YM.Integration.WilsonIndependentCollarMovingInk
end
