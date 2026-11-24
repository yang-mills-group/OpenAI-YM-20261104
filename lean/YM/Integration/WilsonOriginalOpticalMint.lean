import YM.Integration.WilsonOriginalOpticalSchedule
import YM.Integration.WilsonOriginalAllOrderActualMint

/-! A true pre-block contraction and the covered compiler at the very same Wilson mint. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalOpticalMint
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonOriginalCollarTeacher WilsonOriginalAllOrderCalendar
open scoped Classical BigOperators
universe u
open WilsonOriginalAllOrderCourse WilsonOriginalOpticalSchedule
variable {G : Gauge} {a : Axis} {simple : G.Simple} {ε : ℝ}
variable {s : WilsonOriginalAllOrderCourse.Schedule G} {R : Run G} {T : Campaign R} {W : Campaign.Pillars R T}

private theorem gear_at {A B : Levels G} (path : A = B) {m : ℕ}
    (hA : 5 ≤ A.clock.J (m+1)) (hB : 5 ≤ B.clock.J (m+1)) :
    crestM A m hA = crestM B m hB ∧
      (raySmall G A.clock.kernel _ _ (A.clock.adm m) hA).s =
        (raySmall G B.clock.kernel _ _ (B.clock.adm m) hB).s ∧
      (raySmall G A.clock.kernel _ _ (A.clock.adm m) hA).preB =
        (raySmall G B.clock.kernel _ _ (B.clock.adm m) hB).preB := by
  subst B
  exact ⟨rfl,rfl,rfl⟩

/-- For the chosen finite degrees and any finite mass ceiling, all required
bulk certificates and all preannounced compiler requests use the identical
quiet history, actual tokenizer, wages, and physical teacher. -/
theorem original (paid : WilsonOriginalAllOrderCourse.Paid.{u} a simple ε (prepared s) R T W)
    (n : ℕ) (k D : Fin n → ℕ) (hk : ∀ x, k x < D x) (e b h ceiling : ℕ) :
    ∀ᶠ first : ℕ in atTop,
    ∃ V : Realm G (e+1) Credit.leanC, V.draws = R.family.path.levels ∧ V.paid = R.metals.O ∧
      V.y = zz R.family.path.levels ∧ V.anchor = first ∧
      Cloze D k V Credit.leanC ∧ Insure b h V Credit.leanC ∧
      Nonempty (Tribe V (hol G) Credit.leanC Credit.leanC (counter (hol G) (primes G) k D hk)) ∧
      (∀ k' u, k' ≤ ceiling → u ≤ ceiling → Dormitory V k' u Credit.leanC) ∧
      ∀ m, ∀ hm : V.anchor ≤ m, let A := R.family.path.levels
        let j := A.clock.J (m+1)
        let z := Borough.ageZ (A.clock.hatBeta m)
        let U := V.mint m hm
        ∃ live : 5 ≤ j, U.σ = crestM A m live ∧ U.gear.s = 2*U.σ ∧ 2*elixir U.gear = 3*U.σ ∧ nimbus U.gear ≤ z ∧
          (∀ j₀, j₀ ≤ j → (events (prepared s) j j₀).price U.gear ≤ z) ∧
          (∀ a (ha : a ≤ e+1) k r, WilsonOriginalCompoundVertex.Income R m a k r U.σ
            ((WilsonOriginalCompoundVertex.tariff G e a k r ha).buy z)) ∧
          ∀ p k, p ≤ j → k ≤ j →
            let tariffs := widths (teacher (prepared s)) j
            let out := WilsonIndependentCollarPrintIncome.issue tariffs p k U.gear
            out.fee ≤ z ∧ out.strip⁻¹ ≤ z ∧
            (p = e → out.strip ≤ (holt V m hm (tariffs.requested p k U.gear) (tariffs.admitted p k U.gear)).s) ∧
            (∀ t H, t ≤ j+1 → H ≤ j+1 → WilsonIndependentCollarPrintIncome.strip tariffs p k U.gear ≤
              WilsonThermometerUnitFilingWeakStrip.trial (teacher (prepared s)) R.metals.p.kernel t H) ∧
            (∀ x, x = A.clock.J m ∨ x = j → teacherWidth (teacher (prepared s)) R.metals.p.kernel x ≤ out.strip) := by
  obtain ⟨start,stage⟩ := eventually_atTop.mp
    (R.family.path.levels.fits.deep.eventually_ge_atTop (max e ceiling))
  filter_upwards [WilsonOriginalOpticalSpot.realm R simple (total s) paid.billsPaid.2 n k D hk e b h,
    eventually_ge_atTop start] with first invoice ready
  obtain ⟨V,levels,chart,clock,anchor,declared,covered,school,dates⟩ := invoice
  refine ⟨V,levels,chart,clock,anchor,declared,covered,school,?_,?_⟩
  · intro k' u head moment m hm
    let A := R.family.path.levels
    let j := A.clock.J (m+1)
    let U := V.mint m hm
    have visit : max e ceiling ≤ j := stage (m+1) (ready.trans ((anchor ▸ hm).trans m.le_succ))
    obtain ⟨live,_,shape,pre,_,wage⟩ := dates m (anchor ▸ hm) hm
    have fit : max k' (max e u) ≤ j := max_le (head.trans ((le_max_right ..).trans visit))
      (max_le ((le_max_left ..).trans visit) (moment.trans ((le_max_right ..).trans visit)))
    have active : 5 ≤ V.draws.clock.J (m+1) := by rw [levels]; exact live
    obtain ⟨_,actualWidth,actualPre⟩ := gear_at levels active live
    have pins := WilsonOriginalOpticalTariffs.pin U active
      (by simpa only [levels] using opening s R paid.neutral m)
      (by simpa only [levels] using fit) (shape.trans actualWidth.symm) (pre.trans actualPre.symm)
    exact WilsonOriginalOpticalTariffs.spent U.gear k' e u j _ fit
      ((le_max_right ..).trans ((pay s j U.gear).trans wage)) pins
  intro m hm A j z U
  obtain ⟨live,stamp,shape,_,past,wage⟩ := dates m (anchor ▸ hm) hm
  have kernel : U.gear.kernel = A.clock.kernel := by change V.draws.clock.kernel = _; rw [levels]
  have genuine : A.clock.kernel = R.metals.p.kernel := R.alloy.B.valid.kernel
  have invoice : combined (rows (prepared s)) (events (prepared s)) j U.gear ≤ z := by
    simpa only [A,j,z,U,Realm.cash,Credit.lean_cost,clock,zz,Borough.ageZ] using ((le_max_left ..).trans ((pay s j U.gear).trans wage))
  obtain ⟨cost,event⟩ := earn invoice
  have active : 5 ≤ V.draws.clock.J (m+1) := by rw [levels]; exact live
  obtain ⟨actualStamp,actualWidth,_⟩ := gear_at levels active live
  have twice : U.gear.s = 2*U.σ :=
    (WilsonOriginalOpticalTariffs.gain U active (stamp.trans actualStamp.symm) (shape.trans actualWidth.symm)).1
  have radial : 2*elixir U.gear = 3*U.σ := by
    rw [elixir,twice]
    change 2*((2*U.σ+U.σ)/2) = 3*U.σ
    ring
  refine ⟨live,stamp,twice,radial,(le_max_left ..).trans cost,event,?_,?_⟩
  · intro a ha k r N M date lifted θ
    obtain ⟨action,limit,trunk,shelf⟩ :=
      ((Fk.export_domain G Credit.leanC (e+1) a k r ha).choose_spec.money V m hm).2 N M date lifted
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using action
    · simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using limit
    · simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ] using trunk
    intro pastDate
    have cell := shelf pastDate
    simpa only [U,z,A,θ,WilsonOriginalCompoundVertex.tariff,clock,levels,chart,zz,Borough.ageZ]
      using And.intro cell.1 cell.2.1
  · intro p k hp hk tariffs out
    have charge := charged (teacher (prepared s)) j p k U.gear hp hk cost
    refine ⟨charge.2.1,charge.2.2,?_,?_,?_⟩
    · rintro rfl; exact out.narrow
    · intro t H ht hH
      have less : WilsonIndependentCollarPrintIncome.strip tariffs p k U.gear ≤ common (teacher (prepared s)) U.gear.kernel j /32 :=
        min_le_left ..
      exact (less.trans (div_le_self (positive ..).le (by norm_num))).trans
        (by rw [kernel,genuine]; exact paid_neutral (teacher (prepared s)) _ ht hH)
    · intro x hx
      have inc : A.clock.J (m+1) ≤ A.clock.J m + 1 := A.fits.stepSlow m
      have next : A.clock.J (m+2) ≤ A.clock.J (m+1) + 1 := A.fits.stepSlow (m+1)
      have mono : A.clock.J m ≤ A.clock.J (m+1) := A.fits.mono (Nat.le_succ m)
      rw [← genuine]
      rcases hx with rfl | rfl <;>
        apply at_mint (teacher (prepared s)) A m p k _ kernel live shape past <;> dsimp only [j] at * <;> omega
end YM.Integration.WilsonOriginalOpticalMint
end
