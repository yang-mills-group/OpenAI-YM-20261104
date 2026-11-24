import YM.Integration.WilsonPhysicalExteriorResolvedReadout

/-! An independently specified auxiliary finite Wilson/MS regulator: its
actual even side has logarithm within a fixed additive constant of Λ².
It has the same physical marks and clock as the deposited moving trial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorPrescribedSide
open Lattice Function Real Filter YM.MS YM.MS.Tide YM.MS.Fleet YM.MS.Orbit YM.MS.Dial
open YM.MS.Rake YM.MS.Vista YM.MS.Tone
open WilsonPhysicalExteriorResolvedReadout WilsonPhysicalExteriorResolvedCutoff WilsonPhysicalExteriorUVStory
open scoped Topology

def count (s:ℝ) : ℕ := ⌈exp (s^2)⌉₊
def site {I:Type} (Λ:I→ℝ) : I→Side := fun i=>walkway (count (Λ i))
def change {I W:Type} (T:Trial I W)(Λ:I→ℝ) : Trial I W :=
  {T with side:=site Λ,head:=fun i=>crane (count (Λ i))}

theorem exact_size {I:Type} (Λ:I→ℝ) (i:I) :
    (dimT (site Λ) i).val=4*(count (Λ i)+1) := fullC (count (Λ i))

theorem length {I:Type} (Λ:I→ℝ) (i:I) :
    (Λ i)^2≤log (tickA (site Λ) i) ∧ log (tickA (site Λ) i)≤(Λ i)^2+log 12 := by
  have hh: exp ((Λ i)^2)≤(count (Λ i):ℝ):=Nat.le_ceil _
  have he : (count (Λ i):ℝ)<exp ((Λ i)^2)+1:=Nat.ceil_lt_add_one (exp_pos _).le
  have h1 : 1≤exp ((Λ i)^2):=one_le_exp (sq_nonneg _)
  have hval : tickA (site Λ) i=4*((count (Λ i):ℝ)+1) := by
    unfold tickA
    rw [exact_size];push_cast;rfl
  constructor
  · calc (Λ i)^2=log (exp ((Λ i)^2)) := (log_exp _).symm
         _ ≤ log (tickA (site Λ) i) := log_le_log (exp_pos _) (by rw [hval];linarith)
  · calc log (tickA (site Λ) i) ≤ log (exp ((Λ i)^2)*12) :=
          log_le_log (δ_p _ i) (by rw [hval];linarith)
         _=(Λ i)^2 +log 12 := by rw [log_mul (exp_ne_zero _) (by norm_num),log_exp]

theorem room {I W:Type} (T:Trial I W) (Λ:I→ℝ) {l:Filter I} (hΛ:Tendsto Λ l atTop)
    {D c:ℝ} (hc:c<2) (hθ:∀ᶠ i in l,T.profile.θ i≤D*(Λ i)^c) :
    Super l (site Λ) T.profile.θ := by
  intro a
  have hv : Tendsto (fun i=>(Λ i)^(2-c)) l atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hc)).comp hΛ
  filter_upwards [hθ,hΛ.eventually_gt_atTop 0,hv.eventually_ge_atTop (max a 0*D)] with i hi hl hr
  calc a*T.profile.θ i ≤ max a 0*T.profile.θ i := mul_le_mul_of_nonneg_right (le_max_left ..) (T.profile.room i)
       _ ≤ max a 0*(D*(Λ i)^c) := mul_le_mul_of_nonneg_left hi (le_max_right ..)
       _ ≤ (Λ i)^(2-c)*(Λ i)^c := by rw [←mul_assoc];exact mul_le_mul_of_nonneg_right hr (rpow_pos_of_pos hl _).le
       _ = (Λ i)^2 := by rw [←rpow_add hl,sub_add_cancel];norm_num
       _ ≤ log (tickA (site Λ) i) := (length Λ i).1

theorem geometry {I W:Type} (T:Trial I W) (Λ:I→ℝ) {l:Filter I} {μ:ℝ}
    (hz:Reach T.profile T.off) (hm:Resolved T.profile (info T.off))
    (ha:∀i,T.profile.η i=μ-T.profile.θ i) (hh:Tendsto T.profile.θ l atTop)
    (hΛ:Tendsto Λ l atTop) {D c:ℝ} (hc:c<2)
    (hθ:∀ᶠ i in l,T.profile.θ i≤D*(Λ i)^c) : Domain (change T Λ) l μ := by
  refine ⟨hz,hm,ha,hh,room T Λ hΛ hc hθ,fun i=>Cleared _,?_⟩
  exact centered_size _ _ (fun i=>centerD (count (Λ i)))

end YM.Integration.WilsonPhysicalExteriorPrescribedSide
