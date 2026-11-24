import YangMills.WilsonProof.NativeSupport.Commissioned309.AppointedPreCompact
import YM.GradedFar.Elected.Voters
import YM.SignedWilsonExpansion.Result.Orders

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 12000
noncomputable section
namespace YM.FVA2.GradedFar.Appointed1859PreAmple
open YM YM.Integration YM.Integration.Election YM.Answer.ContinuumLimit YM.Answer.ContinuumLimit.Vision
open YM.Spec YM.FVA2 YM.FVA2.Register YM.PhysMS YM.Trace.Pilot
open YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1 YM.XSpace.Cirrus YM.XSpace.Rose
open YM.MS YM.MS.Native YM.MS.Book YM.MS.Menus YM.MS.Tide YM.MS.Theater YM.MS.Fleet YM.MS.Land
open YM.PhysicalNext.Repeat.Legato YM.RG17 YM.Climb YM.Maxwell
open YM.SignedWilsonExpansion YM.SignedWilsonExpansion.Dancer YM.SignedWilsonExpansion.Kane YM.SignedWilsonExpansion.Kane.Tilted
open YM.SignedWilsonExpansion.Belfry YM.SignedWilsonExpansion.Belfry.Classroom YM.SignedWilsonExpansion.Belfry.ScaleFits
open YM.SignedWilsonExpansion.Belle YM.SignedWilsonExpansion.Belle.Path YM.SignedWilsonExpansion.Belle.Buffet
open FVA2.Scale FVA2.Reg FVA2.Dframe O O.Score O.Enh O.Canon Jury Facets Growth Pose Moving Matrix
open MS.Book.Program Dancer Commission Belle Belle.Path Belle.Buffet Future Generator Generator.Drive
open Function Filter Set Asymptotics PowerSeries
open scoped Topology BigOperators Classical ContDiff
universe u
variable {G : Gauge} {H : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}
  {E : Construction.{u} H ε e O} {f : Extraction.Order}
  (V : Vision E f) (Z : YM.FVA2.Register.WilsonPrescription G) (Q : Perspective H Z true)
local notation "W" => Elected.Wframe Z V.pupil.last V.pupil.J
local notation "Θ" => V.T Z
local notation "U" => V.pupil.last

def clockAt (i : Books.DataPoint) : ℝ := i.1
def shift (j : Fin 2) (i : Books.DataPoint) : ℝ := if j=0 then -i.2.val else 0

theorem clockAtTends : Tendsto clockAt Moving.filed trail := tendsto_comap

private instance filedNonempty : Nonempty (↥Growth.Small) :=
  ⟨⟨0,⟨le_rfl,Growth.doubling_pos.le⟩⟩⟩
private instance filedNeBot : Moving.filed.NeBot := by infer_instance

theorem boundedShift (j : Fin 2) : _root_.YM.SignedWilsonExpansion.Belfry.ScaleFits.FO Moving.filed (shift j) := by
  apply Tilted.by_abs (C := Real.log 2)
  apply Filter.Eventually.of_forall
  intro i
  by_cases h : j=0
  · simpa only [shift,h,if_true,abs_neg,abs_of_nonneg i.2.property.1] using i.2.property.2
  · simpa only [shift,h,if_false,abs_zero] using Growth.doubling_pos.le

variable {d : ℕ}

def base (u v : Toon G d) : Tags G d 2 := Books.arms (theory u) (Read.prism (theory v))

def tilted (u v : Toon G d) (i : Books.DataPoint) (j : Fin 2) : Sec G d :=
  Level.Dial d (-(shift j i)) (base u v j)

theorem tiltedSalary (u v : Toon G d) (j : Fin 2) :
    SeatsW.Salary ℂ Moving.filed 1 (fun i => tilted u v i j) := by
  intro L
  have h := YM.SignedWilsonExpansion.Belfry.ScaleFits.boundD (G:=G)
    (θ:=-(shift j)) (boundedShift j).neg_left d (L ∘ₗ LinearMap.applyₗ (base u v j))
  exact h

def hand (ν : ℝ) (j : Fin 2) (i : Books.DataPoint) : FieldEnd G d :=
  tab Q V clockAt false d (shift j) ν 2 i * Level.Dial d (-(shift j i))

theorem handIncome (ν : ℝ) (j : Fin 2) :
    Admits Moving.filed (fun z => hand V Z Q (d := d) ν j z) := by
  let X := Q.matching.details.toServed.toPosted.toQuoted
  let Y := fun z : Books.DataPoint =>
    young 2 (V.T Z (clockAt z)) (_root_.YM.FVA2.Scale.GroupS.gaugeB Z.criterion Q.MS ν (shift j z) d)
  let left := fun z : Books.DataPoint => Level.Dial (G := G) d (shift j z)
  let right := fun z : Books.DataPoint => Level.Dial (G := G) d (-(shift j z))
  have ht : Tendsto (fun z => V.T Z (clockAt z)) Moving.filed (𝓝 0) :=
    ((Vision.marks_the_data Z V Q).clock.conforms H).comp clockAtTends
  have budget := checked Z.scheme Z.criterion X H ν (boundedShift j) d
  obtain ⟨w, s, k⟩ := X.toContract.toMission.born
  have youngIncome : Admits Moving.filed Y := cropAdm ht budget
    (fun z => _root_.YM.FVA2.Scale.GroupS.true_B ν Z.scheme Z.criterion Q.MS Q.p H w s k (shift j z)) 2
  have difference : By ℂ Moving.filed (fun z => Y z - 1) 0 := by
    simpa only [sub_self] using _root_.YM.SignedWilsonExpansion.Dancer.SeatsW.subY youngIncome.dawn (_root_.YM.SignedWilsonExpansion.Dancer.SeatsW.constant (1 : FieldEnd G d))
  have first : SeatsW.Discount ℂ Moving.filed 1 (fun z => left z * (Y z - 1)) :=
    dueRight (shine.mpr difference) (boundD (boundedShift j) d)
  have both : SeatsW.Discount ℂ Moving.filed 1 (fun z => (left z * (Y z - 1)) * right z) :=
    dueLeft first (boundD (θ := -(shift j)) (boundedShift j).neg_left d)
  have whole : By ℂ Moving.filed (fun z => (left z * (Y z - 1)) * right z + 1) 1 := by
    simpa only [zero_add] using _root_.YM.SignedWilsonExpansion.Dancer.SeatsW.addY (shine.mp both) (_root_.YM.SignedWilsonExpansion.Dancer.SeatsW.constant (1 : FieldEnd G d))
  refine ⟨_root_.YM.SignedWilsonExpansion.Dancer.SeatsW.viaY whole (Filter.Eventually.of_forall ?_), ?_⟩
  · intro z
    change (Level.Dial d (shift j z) * (Y z - 1)) * Level.Dial d (-(shift j z)) + 1 =
      (Level.Dial d (shift j z) * Y z) * Level.Dial d (-(shift j z))
    change (left z * (Y z - (1 : FieldEnd G d))) * right z + 1 =
      (left z * Y z) * right z
    have inverse : left z * right z = 1 := by
      change Level.Dial d (shift j z) * Level.Dial d (-(shift j z)) = 1
      apply Level.autumn
    calc
      _ = (left z * Y z) * right z - (left z * right z) + 1 := by
        rw [mul_sub (left z) (Y z) (1 : FieldEnd G d), mul_one, sub_mul]
      _ = _ := by
        rw [inverse]
        exact sub_add_cancel (left z * Y z * right z) (1 : FieldEnd G d)
  · filter_upwards [youngIncome.fits] with z hz
    exact ((adm.Dial (shift j z) d).mul hz).mul (adm.Dial (-(shift j z)) d)

theorem smallHands (ν : ℝ) :
    ∃ χ : Fin 2 → Books.DataPoint → Change G d,
      (∀ j, ∀ᶠ z in Moving.filed, stand (χ j z) = hand V Z Q ν j z) ∧
      ∀ j, Tendsto (guide G d ∘ χ j) Moving.filed (𝓝 0) := by
  have h (j : Fin 2) := handIncome V Z Q (d := d) ν j
  choose χ hχ using fun j : Fin 2 => numeral (h j).fits
  exact ⟨χ, hχ, fun j => guideT (_root_.YM.SignedWilsonExpansion.Dancer.SeatsW.viaY (h j).dawn ((hχ j).mono fun _ hz => hz.symm))⟩


theorem twoPhysical (u v : Toon G d) (i : Books.DataPoint) :
    Books.mix (Physical.familyPoint U W d) (Physical.next W d) i.1 i.2.val v u =
      lifeMany shift Z V false clockAt (tilted u v) none i Books.rootPoints := by
  rw [Physical.earlier_op]
  change V.pupil.S.classMoment (_root_.YM.OPE.spectator U none) _ _ _ = V.pupil.S.classMoment (_root_.YM.OPE.spectator U none) _ _ _
  congr 1
  funext j
  fin_cases j <;> simp [clockAt,shift,tilted,base,Books.arms,jump,Moving.resize,
    Level.flat,Elected.Wframe,Elected.named] <;> rfl

theorem rawCrop {n : ℕ} (u : Tags G d n) (x : Points n) (t : ℝ) (b : ℕ) :
    mote (Lamplight Z false d) b x t u = GradedFar.crop b t (Pose.line Z x u) := by
  simp [mote, Lamplight, GradedFar.crop, Pose.line, Pose.Bbook, PowerSeries.coeff_mk]

include Q in
theorem offered (u v : Toon G d) :
    Books.Offered Z (Physical.familyPoint U W d) (Physical.next W d) u v := by
  have region : Roi ({Books.rootPoints} : Set (Points 2)) :=
    ⟨isCompact_singleton,Set.singleton_subset_iff.mpr ok_wall⟩
  obtain ⟨C,hC,hp⟩ := (V.pricedLines Q).manyHomes 2 Moving.filed clockAt clockAtTends
    {Books.rootPoints} region 0 shift (tilted u v) (tiltedSalary u v) boundedShift false
  obtain ⟨χ,hχ,hg⟩ := smallHands V Z Q (d:=d) 0
  refine ⟨2,2,χ 0,χ 1,(fun i => Θ i.1),by decide,le_rfl,hg 0,hg 1,
    (heater V Z Q).comp clockAtTends,?_⟩
  apply IsBigO.trans ?_ ((heaterPower V Z Q 2).comp_tendsto clockAtTends)
  apply IsBigO.of_bound C
  filter_upwards [hp,hχ 0,hχ 1] with i hi h0 h1
  have hfields :
      Books.arms (stand (χ 0 i) (theory u)) (stand (χ 1 i) (Read.prism (theory v))) =
        fun j => tab Q V clockAt false d (shift j) 0 2 i (tilted u v i j) := by
    funext j
    fin_cases j
    · exact congrArg (fun A : FieldEnd G d => A (theory u)) h0
    · exact congrArg (fun A : FieldEnd G d => A (Read.prism (theory v))) h1
  have sale := hi none Books.rootPoints (Set.mem_singleton _)
  rw [twoPhysical, hfields, ← rawCrop] 
  exact sale

include Q in
theorem ample : Physical.Ample Z U W :=
  ⟨latest V Z Q, fun _ u v => offered V Z Q u v⟩

end YM.FVA2.GradedFar.Appointed1859PreAmple

