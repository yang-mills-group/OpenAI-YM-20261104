import YM.Integration.FVA1Physical.Marked.QuayBirth
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Placement
import YM.Integration.FVA1Physical.Sources.Round2.StaticBarePrice

/-! The fresh source is the actual mixed stencil seen by FVA2 at the current
incoming RG scale. It can have independently chosen labels, placements, and
real or imaginary output projection. The local regularity, exact denominator,
and failed-mask source bill come from the purchased physical construction. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset MeasureTheory Lattice RG YM.Wilson Source Labels Precision RG.Supply Input Org Extra.Histories
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Bandage.Harmonics PhysicalNext.Repeat.Legato.Round2
open Next.Foundations Graces Roost Push Push.Local Push.AbsoluteSums
open YM.Integration.FVA1Physical.Round2.Curvature MSbar.Bulk
open RGComparison.Core16.Catkin RGComparison.Core16.Lam
open RGComparison.Core16.Spool
open scoped Classical BigOperators Topology

variable {G:Gauge} {I:Type} [Fintype I] {d:ℕ}
def freshLamps (a:I → CoverLabel G d) (i:I) : RGComparison.Core16.Spool.Lamp G :=
  investment (sound G (a i).1.val) (valuation G (a i).1.val) (a i).2

def localFieldTariff (B:BudgetPoint) (a:I → CoverLabel G d) (columns:ℝ) (radius:ℕ) : ℝ :=
  (((Fintype.card I+1:ℕ):ℝ)*(1+(radius:ℝ))^B.power)^B.order *
    ∏ j,columns*B.threshold^(((frames G).level (a j).1.val).grades (a j).2).2

def lampSupport {n:Side} (a:I → CoverLabel G d) (o:I → Site n) : Support n :=
  insert 0 (univ.biUnion (fun j=>(localSection G (a j).1.val).footprint (o j)))

theorem fresh_lamp_inputs {X:Metals G} {D:Rolls X.p} {A:Alloy X D} (P:Bolt A)
    {ref:ℕ → ℕ} {T:∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n}
    (physical : Family.Makes (Family.mk (Issue.trail P) (hol G) (frames G) (localSection G) ref T))
    (a:I → CoverLabel G d) {N n j:ℕ} (hj:j ≤ N) (ready:∀ z,ref (a z).1.val ≤ j)
    (o:I → Site ((Issue.trail P).S.side j n)) (part:Bool) (radius:ℕ) (spread:∀ z,separation (o z) 0 ≤ radius) :
    let B:=((Issue.trail P).rep N n j).p
    let f:=fun U=>(look part (tally (freshLamps a) o U):ℂ)
    B.Regular (lampSupport a o) f ∧ B.supBounds 0 (lampSupport a o) f
      (localFieldTariff B a (A.B.a.params j).columns radius) ∧
    ∀ U,‖f U-f 1‖ ≤ 2*stencilBound (freshLamps a) := by
  intro B f
  let g (z:I):=Light (freshLamps a z) ((Issue.trail P).S.side j n) (o z)
  let site (z:I):=(localSection G (a z).1.val).footprint (o z)
  let u (z:I):=(A.B.a.params j).columns*B.threshold^(((frames G).level (a z).1.val).grades (a z).2).2
  have individual (z:I) : B.Regular (site z) (g z) ∧ B.supBounds (o z) (site z) (g z) (u z) := by
    have h:=physical.priced (a z).1.val j n (ready z) (o z) (a z).2
    dsimp only [B,u]
    rw [(P.choice.represents N n j hj).vac]
    exact h
  have inside (z:I) : site z ⊆ lampSupport a o :=
    fun i hi=>mem_insert_of_mem (mem_biUnion.mpr ⟨z,mem_univ _,hi⟩)
  have pair:=price_product (B:=B) (univ:Finset I) g u (0:Site _) o radius (fun z _=>spread z)
    site (fun z _=>inside z) (fun z _=>(individual z).1) (fun z _=>(individual z).2)
  let Z:=tally (freshLamps a) o
  have regular : B.Regular (lampSupport a o) Z := by
    have eq : (∏ z,g z)=Z := by funext U; simp [Z,tally,g,Finset.prod_apply]
    exact eq ▸ pair.1
  have cost:B.supBounds 0 (lampSupport a o) Z (localFieldTariff B a (A.B.a.params j).columns radius) := by
    have eq : (∏ z,g z)=Z := by funext U; simp [Z,tally,g,Finset.prod_apply]
    simpa only [eq,card_univ,localFieldTariff] using pair.2
  let L:=Complex.ofRealCLM.comp (look part)
  have normL (u:ℂ) : ‖L u‖ ≤ ‖u‖ := by
    change ‖(look part u:ℂ)‖ ≤ ‖u‖
    rw [Complex.norm_real]
    cases part <;> first | exact Complex.abs_re_le_norm u | exact Complex.abs_im_le_norm u
  refine ⟨AnalyticBridge.VerifiedReset.regular_mapped L regular,⟨cost.1,?_⟩,?_⟩
  · intro U hu dirs length bounds
    change ‖leftDerivs (L ∘ Z) dirs U‖ ≤ _
    rw [left_linear L dirs (regular.smooth U hu) length]
    exact (normL _).trans (cost.2 U hu dirs length bounds)
  intro U
  have hb (V:Config G ((Issue.trail P).S.side j n)) : ‖f V‖ ≤ stencilBound (freshLamps a) := by
    change ‖((look part (tally (freshLamps a) o V):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact stencil_bounded (freshLamps a) o part V
  exact (norm_sub_le ..).trans ((add_le_add (hb U) (hb 1)).trans_eq (two_mul _).symm)

variable {X:Metals G} {D:Rolls X.p} {A:Alloy X D} {P:Bolt A} {R:Factor A}
    {rates:ℕ → ℝ} {W:Bid.Worth} {l:ℕ} (crew:Bandage.Harmonics R rates W P l)
    {ref:ℕ → ℕ} {T:∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n}
local notation "H" => Issue.trail P

include crew
/-- Exact normalized current insertion, including all derivatives locations and a
polynomial location weight. All prices are printed and independent of torus
volume for a fixed footprint diameter and placements within the given radius. -/
theorem current_lamp_spatial
    (physical : Family.Makes (Family.mk H (hol G) (frames G) (localSection G) ref T))
    (simple:G.Simple) {N n m:ℕ} (hm:m < N) (start:ref 0 ≤ m)
    (a:I → CoverLabel G d) (ready:∀ z,ref (a z).1.val ≤ m+1)
    (o:I → Site ((H).S.side (m+1) n)) (part:Bool) (radius:ℕ) (spread:∀ z,separation (o z) 0 ≤ radius)
    (q s:ℕ) (nq:0 < q) {α:ℝ} (a0:0 < α) (U:Config G ((H).S.side m n)) :
    let B:=((H).rep N n m).p
    let B':=((H).rep N n (m+1)).p
    let φ:=fun V=>look part (tally (freshLamps a) o V)
    let S:=(H).levels.clock.op m n
    let K:=PhysicalNext.Repeat.Legato.Spool.scaler (X.p.profile (A.B.a.clock.J m)) l (D.L (A.B.a.clock.J (m+1)))
    let bill:=birthCost B' (lampSupport a o) (A.B.a.clock.forcedAllowance (m+1))
      (localFieldTariff B' a (A.B.a.params (m+1)).columns radius+‖(φ 1:ℂ)‖) (2*stencilBound (freshLamps a))
    q ≤ B.order → ((s:ℝ)+1)*α*q*(6*B.B+2:ℝ) ≤ B.supportExponent → U∈Boulevard.sunny B → 
    (∑ v : Fin q → Operand G ((H).S.side m n), (1+(wordRadius 0 (List.ofFn v):ℝ))^s *
       ‖leftDerivs (fun V=>(expect S ((H).rep N n (m+1)) V φ:ℂ)) ((List.ofFn v).map compass) U‖) ≤ 
     (1+α⁻¹)^s*(4*Fintype.card G.ColorIndex*Push.Uniform.countCost α)^q*((B.threshold⁻¹)^q*(K*bill)) := by
  intro B B' φ S K bill hq room alive
  obtain ⟨regular,jets,osc⟩:=fresh_lamp_inputs P physical a hm ready o part radius spread
  have hd : 3 ≤ A.B.a.clock.J m := (physical.stages 0).1.trans (A.B.a.fits.mono start)
  exact fresh_reading_spatial crew hm simple hd (hd.trans (A.B.a.fits.mono (Nat.le_succ m)))
    (lampSupport a o) (mem_insert_self ..) φ regular jets osc q s nq hq a0 room U alive
end YM.Integration.FVA1Physical.Marked
