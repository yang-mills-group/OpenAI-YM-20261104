import YM.QuadraticLocal.Aperture.Probe
import YM.QuadraticLocal.Aperture.Rotate
/-!
Glue between Mark, Loan, Mass and fitness. Actor enrollment on the actual auxiliary Name view
for multiple field horizons and arbitrary Φ charge. This is a REAL mass comparison (sole caller
uses this to interpolate marked representational discrepancies via unmatched Neck/Poem.Profile).
No posterior proof from Gram distributions.Integration remains against same Gaussian/tag and normalized
sales. Does not suppose any window projection costs affordable on true lattice.The Budget grants follow.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Aperture
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder PertExtension PertExtension.Series AllOrder.Laplace AllOrder.Laplace.SigmaP Response Laurent Stationary
open PositionX.Jet Extra.Iteration AllOrder.Floe AllOrder.Floe.Pace AllOrder.Floe.Aero AllOrder.Floe.StateE
open AllOrder.Catch AllOrder.Catch.Clock Sienna
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Ink Marker Sunrise Toggle Radial
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type*}{T:AllOrder.Catch.Clock ι} {W b D a B C Ω κ v:ℝ}{k p m x:ℕ} {V:Type}[Fintype V][DecidableEq V]
variable {P:Patch}{K:KernelChoices}{s:Teller G}{r:Stage}{q:ℝ→ℝ}{U:Push.Uniform.Before G r.width r.paths P.J K (k+3)}
open Metric ConnectedActivityE6.Coat
open Till Tilt Lantern Aux Aux.Name
variable (A:Aux.Name G P K q x r k U) (M: V→Loan)
structure Page (A:Aux.Name G P K q x r k U) (M: V→Loan) where
 mark : ∀ i,Atom G (M i).r
 path : V→ Site A.c→ Site A.f
 root : V→Site A.c
namespace Page
variable (Q : Page A M) {O:ChartRatio G}(hO:LocalRatio O)
local notation "Y"=> A.X
local notation "Z"=> Drawer.Knife V
local notation "u"=> (univ:Finset V)
local notation "E₀"=> Body (Precision.Key A.forest G)
local notation "Ω"=> A.forest.Slice G
set_option quotPrecheck false
local notation "d"=> A.Θ
local notation "α" i=> Q.path i (Q.root i)
local notation "Tx"=> A.shape
local notation "L"=> (Aux.scope x)
local notation "P₀"=> Focus.onto (univ:Finset V)
local notation "F₀"=> Focus.census V
local notation "Ξ"=> (A.enters O hO)
abbrev nozzle (t:V→ℝ): Phase A:= ⟨Bunch.beam M Q.mark Q.path Q.root t, Bunch.esteem M Q.mark Q.path Q.root t A.forest, fun t=> Bunch.cover ..⟩
local notation "K₁"=> Page.nozzle A M Q
abbrev portion (i:V)(y: Config G A.f):ℝ:= (A.Θ^((M i).power))⁻¹* (Loan.letter (M i) (Q.mark i) (α i) d y)
abbrev yardP (i:V)(y:A.forest.Slice G):= portion A M Q i (A.Fs.drape y)
local notation "µ"=> A.forest.order G
local notation "ζ"=> Page.yardP A M Q
local notation "₽"=> Page.portion A M Q
local notation "Χ"=> A.newZ
abbrev river (p:Y): Marker.Poly (Focus.census V):= Sage.draft (A.newZ p) (A.forest.order G) (Page.yardP A M Q)
variable (hm:∀ i,(M i).toll=m)(p:A.X)
include hm
lemma shift_amt (i:V)(y:Config G A.f): A.beta * Bunch.beamF M Q.mark Q.path Q.root i d y = A.Θ^m*Page.portion A M Q i y := by -- b syntax
 let f:= Loan.letter (M i) (Q.mark i) (α i) d; have he:A.Θ^2*A.beta=1:=Fare.gS _ A.bpos|>.2; have ht:Bunch.beamF M Q.mark Q.path Q.root i d y=A.Θ*f y:=by unfold f Loan.letter Bunch.beamF; rw [pow_succ']; ring
 rw [ht]; let a:=A.Θ; have hp:0<a:=A.Θp; unfold Page.portion; rw [show (M i).power=m+1 from congr_arg (·+1) (hm i),pow_succ',_root_.mul_inv_rev]; change A.beta*(a*f y)=a^m*(( (a^m)⁻¹*a⁻¹)*f y); field_simp; linear_combination f y * he
lemma transit (t:V→ℝ)(U:Config G A.f): Phase.shadeP A (K₁ t) U = A.Θ^m*Sage.member (portion A M Q) (t,U):= by
 unfold Phase.shadeP Page.nozzle; dsimp only; -- remove notation
 unfold Bunch.beam; rw [Finset.sum_apply]
 unfold Sage.member; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; let a:= Bunch.beamF M Q.mark Q.path Q.root i d U; -- remove
 change - A.beta * (- (t i) * a)= d^m *(t i* Page.portion A M Q i U); rw [mul_left_comm (d^m), ← shift_amt A M Q hm]; ring
omit hm
lemma account (i:V)(y:Config G A.f): portion A M Q i y=(A.Θ)^(M i|>.lag)*(Q.mark i).unmasked y (α i) := Loan.emission _ _ _ _ A.Θp.ne' _
lemma paid (i:V) : RG.Envelope (Page.portion A M Q i) := (Envelope.const _).mul (Loan.bound ..)
lemma valued (i:V): RG.Envelope (yardP A M Q i):= Env.along (paid A M Q i) (A.Fs.continuous_drape.measurable)
variable {s:Age→ℝ}(h:A.Civil s)
include h hm
lemma troupe (t:V→ℝ): Sage.nap (Χ p) µ (yardP A M Q) t (A.Θ^m)= Phase.aisle A (K₁ t) p/A.attends p:=by rw [(A.tilt_record h p).2.2.2]; apply congr_arg (·/ _); apply MeasureTheory.integral_congr_ae; filter_upwards with i; unfold Phase.phrase; rw [Page.transit A M Q hm t]
omit hm
lemma apted (i:A.X) {x:A.forest.Slice G} (hx:A.newZ i x≠0): flags A.price.threshold (A.Fs.drape x)=∅:= by
 contrapose hx; unfold Name.newZ; dsimp only; rw [Fare.total, Pane.sparkling,if_neg hx,mul_zero,zero_mul]
omit h
include hm hO
abbrev bookK (p:A.X):Book (V→ℝ):=fun j t=> Phase.callP A hO (K₁ t) j p-A.aster O hO j p
local notation "Φ"=> Page.bookK A M Q hO
lemma emptyR {i:ℕ}(p:A.X)(hc:Nonempty V): let g:= Bunch.styled M Q.mark Q.path Q.root A.Fs A.shape (Aux.scope x) (A.enters O hO) p; let P':= Response.connected (castle A.Ph A.Mh (A.enters O hO).pay.steer) volume g; alt (Φ p i)=alt (P' i) :=by
 intro g P'; let W j (p:A.X) (t:V→ℝ):= ratePlan (Phase.tallP A (Page.nozzle A M Q t) hO) j p; unfold Page.bookK; change alt (fun t:V→ℝ=> W i p t-A.intercept O i - A.aster O hO i p) = alt (P' i); rw [Turnstile.empties _ _ (A.aster O hO i p) hc,Turnstile.empties _ _ _ hc]; exact Bunch.installed M Q.mark Q.path Q.root A.Fs A.shape (Aux.scope x) A.legal (A.enters O hO) p i hc
lemma cheap_book (p:A.X)(ℓ:ℕ)(hv:ℓ < Fintype.card V * m)(hp :0< m)(hc:Nonempty V): alt (Φ p ℓ)=0:= by rw [emptyR A M Q hO hm p hc]; exact Bunch.censusCost M Q.mark Q.path Q.root A.Fs A.shape (Aux.scope x) (A.enters O hO) p hm hp ℓ (lt_of_lt_of_eq hv (Nat.mul_comm ..)) -- k conflict choose i
open Comparison.RG02 Order Bulk Focus
abbrev basisColor : Comparison.RG02.Bulk.Colors (Focus.census V) G A.f:= Balcony.displayC M Q.mark Q.path (A.shape) (Aux.scope x) (Bunch.mapC Q.root)
variable (VK:Bulk.Kernel A.data A.tube.high A.tube.up O)
local notation "Fr"=> Focus.census V
local notation "Xy"=> Bunch.meterTag M hm
lemma drives (p:A.X)(i j:ℕ) (h:i < m)(hi:i≤j)(ha:0 < m)(hc:Nonempty V): Complex.ofReal (alt (Φ p (Fintype.card V*m+i)))= (observe (Focus.census V) j (Order.logMarked (Bulk.Fk VK A.forest A.choices (Page.basisColor A M Q) (tint G (Exterior.Body 1 A.c) p) j)) i).part (onto (univ:Finset V)):=by
 let W j (p:A.X) (t:V→ℝ):= ratePlan (Phase.tallP A (Page.nozzle A M Q t) hO) j p; let k:=Fintype.card V*m+i; unfold Page.bookK; change Complex.ofReal (alt (fun t:V→ℝ=> W k p t - A.intercept O k - A.aster O hO k p))=_; rw [Turnstile.empties _ _ (A.aster O hO k p) hc,Turnstile.empties _ _ _ hc]; unfold k; rw [Nat.add_comm]; exact Bunch.FKtag M Q.mark Q.path Q.root A.Fs A.shape (Aux.scope x) A.legal A.choices p A.tube.high A.tube.up VK i A.σ A.ν A.he A.loom.large A.path.choose_spec hm ha hc j hi h
end Page
end YM.QuadraticLocal.Aperture
