import YM.GradedFar.Pose.Number

/-!
# Keep the same receipts on the physical data; t upper bridge from PoseFit hypotheses

Pure execution; later apply with the actual arrays and t from this project.
-/
namespace YM.FVA2.GradedFar.Pose
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d : ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "ν"=> Teller.logNu 1
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=> gYM G
variable (F : Plans G 6) (proxy : ℝ → ℝ) (near : Tendsto (fun r=> proxy r / gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1))
variable {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
open XSpace.Rose

/-- Precisely receipts already hypothesized in the C5/PoseFit argument, on a
*finite* batch of requests. Can supply just these. Compare the unselected
`S`, at the length-r home; `Measure.start`, not `outlook`. Supplying this C5
estimate DOESN'T ask for either an OPE estimate of ANY kind or a pricing of
actual-vs-*measured* through-p predictions at theta(r). `Confirmed` is uniform
on the entire indicated compact. Receipt for all three fields at this common
cap, all faces. Use `k=M-1`, `q=Q_*`. Finitely many witness fields at once;
pay after the booking's hypothesis threshold, as specified there. -/
def RawCalibration (k q : ℕ) (cash : ℝ → Normalize.Change G 6) :=
    (∀ i:Fin (N.store.survey 6).n, let w := (N.store.survey 6).scope i;
       Confirmed N F q k proxy cash (tsupport w.t) w.p) ∧
    ∀ s:Badge, Confirmed N F q k proxy cash (tsupport (Rose.test N.criterion)) (missing (tag G) s)

abbrev total r := (Rose.test N.criterion).applyTo (fun x=>value (watchRose F r x))
abbrev kinetic r := (total N F r).re / Rose.cT N.criterion.cut G N.criterion.image
variable (Y : ℝ → Prediction G 6) (u : ℝ → Normalize.Change G 6)
variable (compP : ∀ n x, ∀ᶠ r in τ, ContinuousOn (fun p=> F r n p x) (conf n))
  (full : ∀ n (x:Tags G 6 n) (y:Test n), ∀ᶠ r in τ, Y r n y x=y.applyTo (fun p=> F r n p x))
  (fixed : ∀ᶠ r in τ,(N.store.measure 6).D (Y r)=(N.store.measure 6).D (reference G 6))
  (hc : Tendsto (fun i=> guide G 6 (u i)) τ (𝓝 0))
  (q k : ℕ) (hQ : 1 ≤ q) (hq : k ≤ q+1)
  (acts : RawCalibration N F proxy k q u)
include H
/-- The exact signed real part of the test, not its norm. -/
theorem denominator (hr : (fun r=>total N F r - (Rose.cT N.criterion.cut G N.criterion.image:ℂ)*(proxy r:ℂ))=O[τ] (fun r=>g r^k)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in τ, |kinetic N F r - proxy r| ≤ C * g r ^ k := by
  cases H
  obtain ⟨C,hC,hv⟩:= hr.exists_pos
  let m:=Rose.cT N.criterion.cut G N.criterion.image
  have hm : 0 < |m| := abs_pos.mpr N.criterion.fresh.ne; have hp : m ≠ 0 := abs_pos.mp hm
  refine ⟨C/|m|,by positivity,?_⟩; filter_upwards [hv.bound,positive_g simple] with r hr h
  have he := Complex.abs_re_le_norm (total N F r - (m:ℂ)*(proxy r:ℂ)) |>.trans hr
  rw [← Complex.ofReal_mul, Complex.sub_re, Complex.ofReal_re,
    show (total N F r).re-m*proxy r = (kinetic N F r-proxy r)*m from (by
      change (total N F r).re-m*proxy r=((total N F r).re /m-proxy r)*m; field_simp),
    Real.norm_of_nonneg (by positivity),abs_mul] at he
  exact ((le_div_iff₀ hm).mpr he).trans_eq (by ring)

include acts H hc near compP full fixed hQ hq
/-- The two F.3 receipts actually needed in the t-bridge; relative estimates at the exact signed
coupling. Derive them from C5 and the true hierarchy hypotheses, not vice versa. -/
theorem F3 : (fun r=>guide G 6 (u r))=O[τ] (fun r=>g r^k) ∧
    (fun r=>total N F r - (Rose.cT N.criterion.cut G N.criterion.image:ℂ)*(proxy r:ℂ))=O[τ] (fun r=>g r^k) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in τ, |kinetic N F r-proxy r| ≤ C*g r^k := by
  have hu := landed N M Y u proxy compP full fixed (N.store.survey 6) H (tainted N M proxy H near) hc q k acts.1
  have hr := test_price N M proxy near H q k hQ hq (F:=F) (fun i=>compP _ _) (fun s=>
    pinned N M (Rose.test N.criterion).hasCompactSupport (Rose.test N.criterion).tsupport_subset u proxy H _ q k near hu (acts.2 s))
  exact ⟨hu,hr,denominator N M F proxy H k hr⟩

/-- Key t-bound used in M.2 at this specific earlier hypothesis (see application). -/
theorem paid_kinetic (hk : 2 ≤ k) :
    Tendsto (fun r=>kinetic N F r/g r) τ (𝓝 1) ∧
    ∀ᶠ r in τ, 0 < g r ∧ 0 < kinetic N F r ∧ |kinetic N F r| ≤ 1 ∧ |kinetic N F r| ≤ 2*g r := by
  obtain ⟨C,hC,hv⟩:= (F3 N M F proxy near H Y u compP full fixed hc q k hQ hq acts).2.2
  have hh := relative_reading simple (kinetic N F) proxy near k hk C hv
  exact ⟨hh, paid_reading simple _ hh⟩

end
end YM.FVA2.GradedFar.Pose

