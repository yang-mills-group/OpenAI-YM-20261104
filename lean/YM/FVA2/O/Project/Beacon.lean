import YM.FVA2.O.Project.Coin
/-!
# Definition of the formal separated physical OPE

As in the manuscript's subsection on the separated physical OPE and its uniqueness.
Tested via full diagram product correlations. Specify coefficients as functions on separated
shapes; uniform estimates over BOTH inner and exterior shape sets (fixed separated compacts).
Use t = −log of separation radius. Extend by zero outside configurations; no estimates
on contact terms! Positions measured relative to fixed origin in given scaling units;
`Q` is the physical alphabet, coefficients in formal order space. `O/Canon` supplies this
predicate on both sides of the formal-to-formal comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Project
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick Metric Real
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix
open FVA2.Scale MS.Rake MS.Theater Level O.Score LogTime MS.Plane MS.Heat MS.Tone Momentum Rake.Geo
open Equator Facets Dframe O.Enh O.Bind
variable { G:Gauge }{I:Type} { n m k d j:ℕ }{s:Set (Points n)}{S:Set (Points m)}
variable {a t r:ℝ}{u:Scan G n}{v:Scan G m}{x:Points n}{y:Points m}
abbrev FLog (G:Gauge)(n:ℕ):= ℝ→ Fable G n
-- actual OPE entries at $r=exp(-t)$
abbrev QuoteP (u:Scan G n)(p:FLog G n): FLog G n:= fun t x=> pack u t ( p t x )
abbrev Submit (A:Album G)(u:Scan G n)(v:Scan G m)(t:ℝ)(p:FLog G n)
    (d:ℕ)(x:Points n)(y:Points m) :=
  Basket A u v ( QuoteP u p t x ) d ( squeeze t x ) y
abbrev Near (A:Album G)(s:Set (Points n))(K:Set (Points m))(p:FLog G n)
    (u:Scan G n)(v:Scan G m)(k:ℕ)(a:ℝ)(d:ℕ): Prop :=
  ChargeP d ( (k:ℝ) + a - (totalG u:ℝ) ) (fun (i:s×K) t=> Submit A u v t p k i.1.val i.2.val)
abbrev Exteriors (A:Album G)(s:Set (Points n))(p:FLog G n)(u:Scan G n)
    (k:ℕ)(a:ℝ)(d:ℕ): Prop :=
  ∀ (m:ℕ)(K:Set (Points m))(v:Scan G m), IsCompact K → K ⊆ Outside m → Near A s K p u v k a d
variable {A:Album G}{p:FLog G n}{u:Scan G n}
structure Markup (p:FLog G n) : Prop where
    /-- polynomial in `t` with ONE degree bound per perturbative order and label,
    valid for all shapes -/
    poly (b: Q G): Pace.formal (fun x t=> p t x b)
    off t: Off ( p t )
    stays t: PaceX ( p t )
    /-- uniform price of this polynomial on inner compacts as t→∞ -/
    clocks s: IsCompact s → s ⊆ conf n → ∀ (b:Q G)(k:ℕ),ChargeP k 0 (fun (x:↥s) t=>p t x.val b)
/-- *Characterization*, existence/uniqueness to be proved. -/
structure OPEA (A:Album G)(u:Scan G n)(p:FLog G n) : Prop extends Markup p where
    through s: IsCompact s → s ⊆ conf n → ∀ h k:ℕ, Exteriors A s p u h 1 k
      -- outputs through h, orders < k, exponent h+1-e

-- more visibly oriented proof of polynomial in log r itself (Definition permits distribution basis; we give functions).
lemma stamp_back (hp:Markup p)(q:Q G)(i:ℕ) : Pace ( fun x (t:ℝ)=>coeff i ( p (-t) x q ) ):= by
    obtain ⟨k,hk⟩:= hp.poly q i; refine ⟨ k*( -(Polynomial.X:Polynomial ℝ) ).natDegree,fun x=>?_⟩; obtain ht:= ( hk x ).clock ( - Polynomial.X ); simpa only [Polynomial.eval_neg, Polynomial.eval_X] using ht
lemma Quote_apply (r:ℝ)(hp:0<r)(q:Q G)(i:ℕ): coeff i ( QuoteP u p (-Real.log r) x q ) = (r ^ ( ( heft q:ℝ ) -(totalG u:ℝ) ) : ℝ)* ( coeff i ( p (-Real.log r) x q ) : ℂ ):= by
    rw [QuoteP,pack,coeff_C_mul]; unfold Score.fee; rw [ neg_neg, Real.rpow_def_of_pos hp ]
lemma stamp_fee (h:Markup p)(hs:IsCompact s)(he:s⊆ conf n)(q: Q G): ChargeP k ( ( heft q:ℝ )-(totalG u:ℝ) ) ( fun (x:↥s) t=> QuoteP u p t x.val q ):= by
    refine ChargeP.grow ( ChargeP.joint ( a:=( (heft q:ℝ)-(totalG u:ℝ) ) ) feeV ( h.clocks s hs he q k ) ) ( by simp )
-- no convention about values assigned at collisions in the truth of the approximation
lemma before {x:Points m} (t:ℝ): squeeze t ( squeeze (-t) x )=x:= by simpa only [ neg_neg ] using ( Score.after ( x:=x ) (-t) )
lemma crossN : forest ( squeeze t x ) y= squeeze t ( forest x ( squeeze ( -t ) y ) ):= by rw [ Enh.distil,before ]
theorem district (h: IsCompact s)(he:s⊆conf n)(hp:IsCompact S)(hr:S⊆Outside m): ∀ᶠ t:ℝ in atTop,∀ y∈S,∀ x∈s, forest ( squeeze t x ) y∈ conf (n+m):= by
    filter_upwards [Enh.clusterE h he hp hr,eventually_ge_atTop (0:ℝ)] with t H ht y hy x hx; rw [ crossN ]; let P:Geo Unit:= ⟨fun _=> t,0,fun _=> ht ⟩; let X (_:Unit):= x; let Y (_:Unit):= y; obtain ⟨ h0,hH,hP,hV,hY ⟩:= H ( P:=P ) ( fun _=> le_rfl ) X Y ( fun _=> hx ) ( fun _=> hy ); exact squeeze_away ( due ( f:=fun i=> forest ( X i ) ( Stretch P Y i ) ) ( colored ( P:=P ) ( Seam.mesh_sep h0 ) ( Seam.mesh_sep hP ) (fun i j=> hY j i ) ) () ) _
end YM.FVA2.O.Project
