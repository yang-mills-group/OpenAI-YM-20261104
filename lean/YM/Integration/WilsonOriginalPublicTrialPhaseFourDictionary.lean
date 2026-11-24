import YM.Integration.WilsonMaxwellThermometerChargedHeads
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
import YM.FrontierTrace.Primary.HorizonFour
import YM.WilsonCoeffUV.RootLaw

/-! Retained degree-four native coordinates and their signed Maxwell basis. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseFourDictionary
open Function Finset Labels Maxwell WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Embroider
open MS MS.Menus MS.Local.Physical MS.Theater
open scoped Classical BigOperators
variable {G:Gauge} (F:Labels.Frame G 4)

abbrev Kept := {i:Alma F // ¬(sheet F i=0 ∧ 0<rankS (notar F i))}

def seat (j:F.Index):Kept F:=
  ⟨⟨(j,⟨0,by simp⟩),by simpa [rankS] using F.bound j⟩, by simp [notar,rankS]⟩

theorem weight (simple:G.Simple)(i:F.Index)(nonunit:i≠0):F.grades i=(4,2):=by
  have positive:=F.factors_pos i nonunit
  have ar:=WilsonMaxwellThermometerWardColors.arity simple F i
  have debt:=WilsonMaxwellThermometerChargedHeads.graded F i
  have cap:=F.bound i
  exact Prod.ext (by omega) (by omega)

theorem rank_zero (simple:G.Simple)(i:Kept F):rankS (notar F i.val)=0:=by
  by_cases h:sheet F i.val=0
  · by_contra nz
    exact i.property ⟨h,Nat.pos_of_ne_zero nz⟩
  · have full:=congrArg Prod.fst (weight F simple _ h)
    change (F.grades (sheet F i.val)).1=4 at full
    have cap: (F.grades (sheet F i.val)).1+rankS (notar F i.val)≤4:=i.val.property
    omega

theorem seat_sheet (simple:G.Simple)(i:Kept F):seat F (sheet F i.val)=i:=by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    exact (Multiset.card_eq_zero.mp (rank_zero F simple i)).symm

def restored (simple:G.Simple):(Kept F→ℂ)≃ₗ[ℂ]F.Coeff where
  toFun b j:=b (seat F j)
  invFun b i:=b (sheet F i.val)
  left_inv b:=funext fun i=>congrArg b (seat_sheet F simple i)
  right_inv _:=rfl
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def onsite (simple:G.Simple):Label G 4 ≃ₗ[ℂ] LinearMap.range (observable G 4):=
  LinearEquiv.ofBijective (observable G 4).rangeRestrict (by
    constructor
    · intro x y h
      exact (LinearMap.ker_eq_bot.mp (FrontierTrace.Primary.ideal0 simple (d:=4) le_rfl)) (congrArg Subtype.val h)
    · rintro ⟨_,x,rfl⟩
      exact ⟨x,rfl⟩)

def read (simple:G.Simple)(B:Deck G):(Kept F→ℂ)≃ₗ[ℂ](Glyph B 4→ℂ):=
  ((restored F simple).trans F.coords.symm).trans ((onsite simple).trans (Daylight B 4).equivFun)

theorem signed (simple:G.Simple)(B:Deck G)(z:Kept F→ℂ):
    ∑i:Glyph B 4, read F simple B z i • Daylight B 4 i =
      (observable G 4).rangeRestrict (F.coords.symm (fun j=>z (seat F j))):=
  (Daylight B 4).sum_repr _

theorem capital (simple:G.Simple)(B:Deck G):
    ∃C:ℝ,0≤C ∧ ∀z:Kept F→ℂ,∑i,‖z i‖≤C*‖read F simple B z‖:=by
  let e:=(read F simple B).symm.toContinuousLinearEquiv.toContinuousLinearMap
  refine ⟨(Fintype.card (Kept F):ℝ)*‖e‖,by positivity,?_⟩
  intro z
  have p : ‖z‖≤‖e‖*‖read F simple B z‖:=by
    simpa [e] using e.le_opNorm (read F simple B z)
  calc
    ∑i,‖z i‖ ≤ ∑_:Kept F,‖z‖:=Finset.sum_le_sum fun i _=>norm_le_pi_norm z i
    _ ≤ _:=by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left p (Nat.cast_nonneg _)

end YM.Integration.WilsonOriginalPublicTrialPhaseFourDictionary
