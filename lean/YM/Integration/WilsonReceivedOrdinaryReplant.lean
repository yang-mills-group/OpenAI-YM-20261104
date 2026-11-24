import YM.Integration.WilsonReceivedCoverReplant
import YM.Integration.WilsonMarkedOrdinaryCaptureGap

/-! On each genuine receiving date print the entire previously issued independent table.
Every intermediate scalar and connected proper subword enters the next ordinary Wick program. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedOrdinaryReplant
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Tree Exterior Stationary
open PowerSeries Next.Free FormalBulk08 Flat Reef Jets Series Shore Gorge Lotus Mesa City Cork
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Mosaic.Near
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue WilsonCoeffUV.Soil WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos WilsonPointChildPlacedFamily
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open PhysicalNext.Repeat.Legato Next.Foundations Pose Dawn Kemp Rift
open WilsonMarkedIndependentPhysicalIntake WilsonPointChildFiledPress
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Realm
open WilsonOlderFreshConnectedRobe
open scoped Classical BigOperators


open WilsonReceivedDatedVerseReprint (Issued printed)
open WilsonMarkedIndependentEnrolledPeriod (registered)

open WilsonReceivedCompactVerseEntrance (CoverBill submit)
open WilsonReceivedMicroscopicVerseWallet (gross)

open WilsonReceivedReplantedVerseCourse (lower)
open WilsonReceivedReplantedVersePeriod (Charge)
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{h k:I → ℕ}{e:ℕ}
variable (R:Run G)

open WilsonReceivedReplantedVerseTrail (path Paid)
open WilsonReceivedCoverGrade (Same)
open WilsonReceivedCoverFaces (step self ordinary)

open WilsonReceivedCoverTrail (declared)
open WilsonMarkedOrdinaryCaptureGap (Within tariff)
open WilsonCoeffUV.Wheel.Flooring

variable {Y T:Outerm G h}{n:Side}{σ A:ℝ}
omit [Fintype I] in
theorem compact (s:Finset I)(e r:ℕ)(hs:0 ≤ σ)(hA:0 ≤ A)(modes:PairedAt e Y n σ A)(y:I → Cover)
    (c:Cover)(D:ℕ)(positions:∀a∈s,terrain.gap c (y a) ≤ D)(fits:8*D < n.val):
    Within n (fun X=>terrain.gap c X.1 ≤ D) e r (catchW σ n.val)
      (tariff h e r s*A^s.card) (levelsO (Y y) s):=by
  apply WilsonMarkedOrdinaryCaptureGap.ordinary n _ s (Y y) e r _ A (catch_hot ..) hA
  intro J sub i hi k _ x hit
  have dist:Syn terrain y J x ≤ 2*D:=league_cash (d:=terrain) (a:=c) (x:=foyer y J x) (fun u=>by
    cases u with
    | inl a=>exact positions _ (sub a.property)
    | inr a=>exact hit a)
  exact (modes y J i hi k).pore hs x (by omega)

def Angular (Y T:Outerm G h)(e:ℕ)(n:Side)(σ t A B:ℝ):Prop:=
  ∀(y:I → Cover)(S:Finset I)(a:ℕ),a ≤ e → ∀(r:ℕ)(x:Fin r → YForest G)(c:Cover)(D:ℕ),
  (∀j∈S,terrain.gap c (y j) ≤ D) → (∀i,terrain.gap c (x i).1 ≤ D) → 8*D < n.val →
  ‖(levelsO (Y y) S).1 n a r (slideC n x)-(levelsO (T y) S).1 n a r (slideC n x)‖ ≤
    (tariff h e r S*A^S.card)*catchW σ n.val+(tariff h e r S*B^S.card)*catchW t n.val

omit [Fintype I] in
theorem between {t B:ℝ}{e:ℕ}(hs:0≤σ)(hA:0≤A)(ht:0≤t)(hB:0≤B)
    (left:PairedAt e Y n σ A)(right:PairedAt e T n t B)(same:∀y J,Same e (Y y J) (T y J)):
    Angular Y T e n σ t A B:=by
  intro y S a ha r x c D pos enc fits
  have u:=(compact S e r hs hA left y c D pos fits a ha r le_rfl x enc).gap
  have v:=(compact S e r ht hB right y c D pos fits a ha r le_rfl x enc).gap
  change ‖(levelsO (Y y) S).1 n a r (slideC n x)-(levelsO (Y y) S).2 a r x‖ ≤ _ at u
  change ‖(levelsO (T y) S).1 n a r (slideC n x)-(levelsO (T y) S).2 a r x‖ ≤ _ at v
  have eq:=WilsonReceivedCoverFaces.ordinary (same y) S a ha
  rw [eq] at u
  exact (norm_sub_le_norm_sub_add_norm_sub _ ((levelsO (T y) S).2 a r x) _).trans (add_le_add u (by
    simpa only [norm_sub_rev ((levelsO (T y) S).2 a r x)] using v))

theorem original (simple:G.Simple)(quiet:WilsonReceivedCloseFundedHeat.Quiet R)
    (price:ℕ → Gear G → ℝ)(funded:FundedMarkedCoverRows.prices price R.kit)(K k:I → ℕ)(e:ℕ):
    ∀ᶠm:ℕ in atTop,∀b,m ≤ b → ∀s:ℝ,0<s → ∃σ t C B:ℝ,0<σ ∧ 0<t ∧ 1 ≤ C ∧ 1 ≤ B ∧
      ∀N,b ≤ N → ∀p (Y:Outerm G h),Wellness k Y → ∀A:ℝ,1 ≤ A → PairedAt e Y (R.family.side b p) s A →
      let U:=Gears R.family.path.levels R.metals.O K k N b m Y
      let Z:=WilsonReceivedReplantedVerseTrail.path R K k e N (b-m) m Y
      Angular U (submit Z k e) e (R.family.side m p) σ t (C*A) (B*A):=by
  filter_upwards [WilsonReceivedCoverTrail.original (h:=h) R simple quiet price funded K k e,
    WilsonReceivedReplantedVerseTrail.original (h:=h) R simple quiet price funded K k e,
    WilsonReceivedDirectVersePeriod.original (h:=h) R simple quiet price funded K k e] with m covered road sheet
  intro b geo s hs
  obtain ⟨σ,C,hσ,hC,raw⟩:=sheet b geo s hs
  obtain ⟨t,V,ht,hV,previous⟩:=road (b-m) m le_rfl s hs
  let G₀:=gross G (mass k univ+e) t 1
  have hG:1 ≤ G₀:=WilsonReceivedMicroscopicVerseWallet.one ..
  refine ⟨σ,t/32,C,G₀*V,hσ,by positivity,hC,one_le_mul_of_one_le_of_one_le hG hV,?_⟩
  intro N high p Y lawful A hA rent U Z
  have native:PairedAt e U (R.family.side m p) σ (C*A):=raw N high p Y lawful A hA rent
  have fiscal:CoverBill Y e s A:=fun y J a ha r=>(rent y J a ha r).access
  have stamped:Paid R k e (b-m) m Z t (V*A):=previous N (by omega) Y lawful A hA fiscal
  have files:=WilsonReceivedCompactVerseEntrance.original Z stamped.1 ht
    (one_le_mul_of_one_le_of_one_le hV hA) stamped.2.1
  have right:PairedAt e (submit Z k e) (R.family.side m p) (t/32) ((G₀*V)*A):=by
    simpa only [mul_assoc,G₀] using files.2.2.2 (R.family.side m p)
  have common (y:I → Cover)(J:Finset I):Same e (Z y J) (U y J):=by
    simpa only [Z,U,declared,show m+(b-m)=b by omega] using covered (b-m) m le_rfl N (by omega) Y lawful s A hs hA fiscal y J
  exact between hσ.le (by positivity) (by positivity) (by positivity) native right
    (fun y J i hi=>(common y J i hi).symm.trans (files.2.2.1 y J i hi).1.symm)

end YM.Integration.WilsonReceivedOrdinaryReplant
