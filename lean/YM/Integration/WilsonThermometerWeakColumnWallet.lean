import YM.Integration.WilsonThermometerWeakGroupCoordinate
import YM.Integration.WilsonThermometerOffsetLedger

/-! Both parts of the aperture income of a true displaced field are subpower in
the monitor, before the microscopic cutoff and the physical period. The same
original readout salary also bounds its thermal column. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakColumnWallet
open Function Filter Set Lattice Wilson RG Source Labels RG12 Extra.Histories
open Push.PriceCompiler RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon Asymptotics
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G)
local notation "Rf" => R.family
local notation "Lev" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem log_wallet {a:ℝ} (ha:0<a):
    ∀ᶠ s:ℝ in atTop,1+Real.log (2+Real.log s)≤bill a s:=by
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 2,
    y_rate.eventually_ge_atTop (1+Real.log 2),y_rate.eventually_ge_atTop (2/a)] with s hs hf hy
  have hl:0<Real.log s:=by linarith only [hs]
  have h:Real.log (2+Real.log s)≤Real.log 2+y s:=by
    rw [y,←Real.log_mul (by norm_num) hl.ne'];apply Real.log_le_log (by positivity);linarith only [hs]
  have ht:2≤y s*a:=(div_le_iff₀ ha).1 hy
  have y0:0≤y s:=by exact (div_nonneg (by norm_num) ha.le).trans hy
  have hq:=mul_le_mul_of_nonneg_right ht y0
  calc
    _ ≤ 1+Real.log 2+y s :=by linarith only [h]
    _ ≤ (y s)^2*a+1:=by nlinarith only [hf,hq]
    _ ≤ _ := Real.add_one_le_exp _

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b)
    (d:ℕ) {a:ℝ} (ha:0<a):
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N) (X:Coefficient ((Rf).labels.level d) ((Rf).side k p)) (y:Palette Rf d),
    let P:=(Rf).path.rep N p k
    let F:=(Rf).labels.level d
    let cash:=B d k*size y
    X.Format 0 (Rf).params P → X.remBound 0 P (kappa (Rf).path k) cash →
    Germ.projection F (Rf).params P.p.threshold 0 X=y (primaryLetter d) →
    2*((Lev).params k).columns*F.coeffSize X.x+cash ≤bill a (clim (Lev) k)*size y :=by
  let c:=GermGraph.price (C:=Rf) d
  let D:=3+2*(abs c)
  have a4:0<a/4:=by positivity
  have a2:a/4+a/4<a:=by linarith only [ha]
  have rent:=hat_rate (Lev) simple
  filter_upwards [WilsonThermometerWeakTaylor.head (d:=d) R simple 0,
      WilsonThermometerOffsetLedger.original R simple shop d,
      rent.eventually (log_wallet a4),rent.eventually (transports a2 D)] with k head ledger small gate N p hk X y P F cash form paid rooted
  let v:F.Coeff:=y (primaryLetter d)
  let b:=B d k
  let u:=size y
  have u0:0≤u:=size_ge y
  have b1:1≤b:=ledger.2.1
  have b0:0≤b:=zero_le_one.trans b1
  have col:((Lev).params k).columns≤b:=by
    have eq:((Lev).params k).columns=(R.metals.p.profile (R.alloy.B.a.clock.J k)).columns:=congrArg Stage.columns (params_eq R.alloy.B.valid k)
    rw [eq];exact (Copper.cash_fill G d (R.alloy.B.a.clock.J k) R.metals.p.profile R.y).choose_spec.2.1
  have bbase:b≤bill (a/4) (clim (Lev) k):=ledger.2.2.trans small
  have yup:F.coeffSize v≤u:=by
    rw [show u=size y from rfl,bill_group]; exact Finset.single_le_sum
      (f:=fun i:Letter d=> ((Rf).labels.level (kept i)).coeffSize (y i))
      (fun i _=>Work.G08.size_nonneg _ _) (Finset.mem_univ (primaryLetter d))
  have diff:=head N p hk X v ⟨form,paid⟩ rooted
  have price:F.coeffSize (v-X.x)≤c*cash:=by simpa only [zero_mul,Real.exp_zero,mul_one] using diff
  have hD:F.coeffSize (v-X.x)≤(abs c)*(b*u):=price.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg b0 u0))
  have neg:F.coeffSize (-(v-X.x))=F.coeffSize (v-X.x):=by
    change ∑ i,‖-(v-X.x) i‖=∑ i,‖(v-X.x) i‖
    simp only [norm_neg]
  have hx:F.coeffSize X.x≤u+(abs c)*(b*u):=by
    have eq:X.x=-(v-X.x)+v:=by abel
    calc
      _ = F.coeffSize (-(v-X.x)+v):=congrArg _ eq
      _ ≤ F.coeffSize (-(v-X.x))+F.coeffSize v:=Size.add ..
      _ ≤ _:=by rw [neg];linarith only [yup,hD]
  have hgate:D*(bill (a/4) (clim (Lev) k))^2 ≤bill a (clim (Lev) k):=by rw [pow_two,overlap];exact gate
  have sq: D*b^2≤bill a (clim (Lev) k):=by
    apply le_trans _ hgate
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ b0 bbase 2) (by dsimp [D];positivity)
  have h₂:=mul_le_mul_of_nonneg_right b1 (mul_nonneg b0 u0)
  change 2*((Lev).params k).columns*F.coeffSize X.x+b*u≤_
  calc
    _ ≤2*b*(u+(abs c)*(b*u))+b*u:=add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left col (by norm_num : (0:ℝ)≤2)) hx (Work.G08.size_nonneg _ _) (mul_nonneg (by norm_num : (0:ℝ)≤2) b0)) le_rfl
    _ ≤ D*b^2*u:=by dsimp [D];nlinarith only [h₂]
    _ ≤ _ := mul_le_mul_of_nonneg_right sq u0

end YM.Integration.WilsonThermometerWeakColumnWallet
end
