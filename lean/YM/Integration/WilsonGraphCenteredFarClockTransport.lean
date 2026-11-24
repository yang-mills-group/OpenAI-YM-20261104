import YM.Integration.WilsonGraphCenteredFarTransportReturn
import YM.Integration.WilsonGraphCenteredFarHeaterSubstitution

set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredTransport

open Filter Real PowerSeries Growth Continuation
open Register MS MS.Book MS.Land Scale
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Dframe Jury
open MS.Native MS.Menus MS.Tide MS.Book.Program
open YangMills YM.Answer.ContinuumLimit YM.Integration
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)

private abbrev farPick := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev farScheme := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev farPerspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev farHeat := ElectedMeasurement.clock (farPick.{u} g hg periods strict) (farScheme g hg)

private theorem heaterBill (m k : ℕ) {x F J t err : ℝ} (depth : m+2 ≤ k)
    (hx : 0 ≤ x) (small : x ≤ 1) (hF : 0 ≤ F) (hJ : 0 ≤ J) (ht : 0 ≤ t)
    (near : t ≤ 2*x) (distance : err ≤ x^(m+2)) (moment : F^k*x ≤ 1)
    (size : J*x ≤ 1) :
    J*((k:ℝ)*err) + ((k:ℝ)*F^k)*J*t^(k+1) ≤
      ((k:ℝ)+(k:ℝ)*2^(k+1))*x^(m+1) := by
  have first : J*((k:ℝ)*err) ≤ (k:ℝ)*x^(m+1) := by
    calc J*((k:ℝ)*err) ≤ J*((k:ℝ)*x^(m+2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left distance (by positivity)) hJ
         _ = ((k:ℝ)*x^(m+1))*(J*x) := by rw [pow_succ x (m+1)]; ring
         _ ≤ ((k:ℝ)*x^(m+1))*1 := mul_le_mul_of_nonneg_left size (by positivity)
         _ = _ := mul_one _
  have both : (F^k*x)*(J*x) ≤ 1 := by
    calc (F^k*x)*(J*x) ≤ 1*(J*x) := mul_le_mul_of_nonneg_right moment (mul_nonneg hJ hx)
         _ ≤ 1 := by simpa only [one_mul] using size
  have folded : x^(k+1) = x^(k-1)*x*x := by
    calc x^(k+1) = x^(k-1+1+1) := congrArg (fun n : ℕ => x^n) (by omega)
         _ = x^(k-1)*x*x := by rw [pow_succ x (k-1+1), pow_succ x (k-1)]
  have exponent : x^(k-1) ≤ x^(m+1) := pow_le_pow_of_le_one hx small (by omega)
  have second : ((k:ℝ)*F^k)*J*t^(k+1) ≤ ((k:ℝ)*2^(k+1))*x^(m+1) := by
    calc ((k:ℝ)*F^k)*J*t^(k+1) ≤ ((k:ℝ)*F^k)*J*(2*x)^(k+1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht near (k+1)) (by positivity)
         _ = ((k:ℝ)*2^(k+1))*(((F^k*x)*(J*x))*x^(k-1)) := by rw [mul_pow, folded]; ring
         _ ≤ ((k:ℝ)*2^(k+1))*(1*x^(k-1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right both (pow_nonneg hx _)) (by positivity)
         _ ≤ _ := by simpa only [one_mul] using
           (mul_le_mul_of_nonneg_left exponent (show 0 ≤ (k:ℝ)*2^(k+1) by positivity))
  calc _ ≤ (k:ℝ)*x^(m+1) + ((k:ℝ)*2^(k+1))*x^(m+1) := add_le_add first second
       _ = _ := by ring

/-- On the entire filed distance window, the reverse field is evaluated against its
positive-distance column at the actual far heater. The crop depth is fixed before the radius. -/
theorem atFarClock (h m : ℕ) {C B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    ∀ᶠ k : ℕ in atTop, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s ≥ 0,
      exp s ≤ C * (gYM g.core r)^(-B) →
      let f := r * exp s
      let L := chairs g.core h (AppointedCenteredReverse.transfer.{u} g hg periods strict h r f)
      let A := chairs g.core h (atColumn
        (Kseries (farScheme g hg) (farPerspective.{u} g hg).MS h s) k
        (farHeat.{u} g hg periods strict f))
      ‖L-A‖ ≤ D*(gYM g.core r)^(m+1) := by
  let N := farScheme g hg
  let M := (farPerspective.{u} g hg).MS
  let matchData := (farPerspective.{u} g hg).matching
  let law := (matchData.dilation (Teller.logNu 1)).check
  let simple := _root_.IssuedMaxwell.ElectedPrescription.simple g hg
  obtain ⟨K,hK⟩ := exists_nat_gt B
  have running : Tendsto (gYM g.core) (𝓝[>] (0:ℝ)) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨shrink simple, positive_g simple⟩
  have edges := running.eventually (G1.Wire.move C B hK hC)
  have heat := paid_reading simple (farHeat.{u} g hg periods strict)
    (AppointedPhysicalWindowAndPhase.electedClock.{u} g hg periods strict)
  filter_upwards [onWindow.{u} g hg periods strict h m hC hB,
    AppointedCenteredWindow.paid.{u} g hg periods strict h (m+1) hC hB,
    eventually_ge_atTop (m+2)] with k reverseFee paired depth
  obtain ⟨D,hD,reverse⟩ := reverseFee
  obtain ⟨J₀,hJ₀,a,price⟩ := AppointedFarHeater.size N M matchData h k
  have location := running.eventually (Appointed220.Zones.Budget.location law K k
    (δ:=1/2) (by norm_num))
  have moments := running.eventually (Appointed220.Zones.Budget.moments law K k k
    (δ:=1) zero_lt_one)
  have smallBill := running.eventually (G1.Wire.distills (a:=a) zero_lt_one hJ₀ K)
  refine ⟨D+((k:ℝ)+(k:ℝ)*2^(k+1)), by positivity, ?_⟩
  filter_upwards [reverse, paired, edges, heat, location, moments, smallBill,
    running.eventually (Ioc_mem_nhdsGT (by norm_num : (0:ℝ)<1/4))] with
    r reverseAt pairedAt edgeAt heatAt locationAt momentsAt sizeAt smallAt
  intro s hs upper f L A
  let x := gYM g.core r
  let t := farHeat.{u} g hg periods strict r
  let v := farHeat.{u} g hg periods strict f
  let w := bend N M s k (t:ℂ)
  let Uq := chairs g.core h (atColumn (AppointedCenteredReverse.reverseSeries N M h s) k t)
  let F := max 1 (Appointed220.Eval.mass k (GroupS.ψ N.criterion M (Teller.logNu 1) (-s)))
  let J := Appointed220.Eval.mass k (Appointed220.Zones.liftSeries
    (AppointedCenteredSeriesPrice.coordinateChart g.core h) (Kseries N M h s))
  have hx : 0 < x := smallAt.1
  have quarter : x ≤ 1/4 := smallAt.2
  have small : x ≤ 1 := by linarith
  have near : |t| ≤ 2*x := heatAt.2.2.2
  have unitT : |t| ≤ 1 := by linarith
  have edge := edgeAt (exp s) (Real.one_le_exp_iff.mpr hs) upper
  have located := locationAt (exp s) edge (t:ℂ)
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using near)
  rw [Appointed220.Zones.Budget.eta,Real.log_exp] at located
  have half : ‖w‖ ≤ 1/2 := located
  have powerSmall : x^(m+2) ≤ x := by
    simpa only [pow_one] using (pow_le_pow_of_le_one hx.le small (show 1 ≤ m+2 by omega))
  have distance : ‖(v:ℂ)-w‖ ≤ x^(m+2) :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (pairedAt s hs upper).1
  have unitV : |v| ≤ 1 := by
    calc |v| = ‖(v:ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]
         _ = ‖((v:ℂ)-w)+w‖ := by rw [sub_add_cancel]
         _ ≤ ‖(v:ℂ)-w‖+‖w‖ := norm_add_le _ _
         _ ≤ 1 := by linarith
  have moment := momentsAt (exp s) edge
  rw [Appointed220.Zones.Budget.eta,Real.log_exp] at moment
  have reserve : F^k*x ≤ 1 := moment
  have size : J*x ≤ 1 := (mul_le_mul_of_nonneg_right (price s hs) hx.le).trans
    (by simpa only [G1.Wire.tick,Real.log_exp] using sizeAt (exp s) edge)
  have hF : 0 ≤ F := zero_le_one.trans (le_max_left _ _)
  have hJ : 0 ≤ J := Appointed220.Eval.mass_nonneg ..
  have switched := AppointedFarHeater.crop N M matchData h k s t v unitT unitV
    (show ‖w‖ ≤ 1 by linarith)
  have paid : ‖A-Uq‖ ≤ ((k:ℝ)+(k:ℝ)*2^(k+1))*x^(m+1) :=
    switched.trans (heaterBill m k depth hx.le small hF hJ (abs_nonneg t) near distance reserve size)
  have previous : ‖L-Uq‖ ≤ D*x^(m+1) := reverseAt s hs upper
  calc ‖L-A‖ ≤ ‖L-Uq‖ + ‖Uq-A‖ := by
         have z : L-A = (L-Uq)+(Uq-A) := by abel
         rw [z]
         exact norm_add_le _ _
       _ = ‖L-Uq‖ + ‖A-Uq‖ := by rw [norm_sub_rev Uq A]
       _ ≤ D*x^(m+1) + ((k:ℝ)+(k:ℝ)*2^(k+1))*x^(m+1) := add_le_add previous paid
       _ = _ := (add_mul D ((k:ℝ)+(k:ℝ)*2^(k+1)) (x^(m+1))).symm

end YM.FVA2.GradedFar.AppointedCenteredTransport

