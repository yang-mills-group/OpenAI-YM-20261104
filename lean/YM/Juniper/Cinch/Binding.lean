import YM.Juniper.Cinch.Landed
import YM.Juniper.Bright.Motion
import YM.Juniper.OrbitPrice.Curves
/-!
 # Re-expression **at exact same ACTUAL coupling and threshold** before next kernel
 
Not assuming the spare pre-response shift is the trajectory's. Two versions of Φ use the
same EARLY Mark readout. Obtain strict arithmetic and recurrence-ready end via
βShift stabilization independent of selecting a trajectory below. Applies to
ANY re-expression earning `Boundary`. Publication includes exact residual norm cost of
this version from differences of representations GIVEN corresponding exact-ledger fares.
This binder operates before multi-mark transfers; doesn't infer automatic lifting of
representations of sources between the two Φ-grammar families.
Reconciles `Thermal.shift` and Sector Actual anchor. Doesn't feed it to timePickup branch.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Cinch
open Function Filter Metric Lattice Wilson RG PhysicalNext PhysicalNext.Repeat
open Push Push.AbsoluteSums AnalyticBridge VerifiedReset Collection Averaging
open Filter Function Lattice RG Pressure Pressure.Testing Tree Wilson
open Push Push.AbsoluteSums Precision Next.Fluctuations SectorMeasure
open ConnectedActivityE6 Coat Rain
open Further.PhysicalPeriodLimitF933 Macrame Uniform
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Input Org Supply Opera Pane Roof Push.PriceCompiler ThroughLaunch Blaze Roost Push.Uniform
open Progress.DirectedRecipe Time Legato
open UVExtension Dales
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G: Gauge} {X:Metals G} {c:Side} {D:Rolls X.p} {A:Alloy X D} (R:Factor A) {ε ε₀ v β τ b e:ℝ}
local notation "P"=> A.B.a
variable {Y Y':Listing G c}{f g: Collection.Source G c}{N n m:ℕ}
local notation "t"=> A.B.a.clock.hatBeta m
local notation "W"=> A.B.a.budget m
local notation "H"=> Time.forecastE A.B.a m
local notation "r"=> Time.forecastK A.B.a m R.scout β
local notation "T"=> A.B.a.params m
local notation "L"=> A.B.kin.path N m
local notation "C"=> (T).clip
local notation "α"=> A.B.kin.alpha N m
local notation "E"=> Collection.earlyValue
local notation "Y₀"=> A.B.a.clock.J (m+1)
local notation "q"=> quoteHard A.B.a m R.book β
local notation "p"=> forecastK A.B.a m R.scout β
variable (hG:G.Simple)(hc:Courtesy A.delay)(hw:wraps (A.B.a.clock.hatBeta m) c)(hn:20<c.val)(hm:m<N)
section
variable {Z: Config G c→ℝ}
-- same pre-evaluator at SAME β. `Own` old Dales from History. shifts exact.
structure Pristine (A:Alloy X D) (N m:ℕ)(hB:ℝ)(β δ:ℝ)(Z:Config G c→ℝ):Prop where
    vision : ∃ (X:Listing G c)(v: Collection.Source G c)(a b:ℝ), Collection.Local X (A.B.a.budget m) v hB a ∧ Collection.earlyValue X (A.B.kin.path N m) (A.B.a.params m).clip (A.B.a.budget m) v β b (A.B.kin.alpha N m)= Z ∧ δ=Averaging.delta (X.read v)
-- remove u
variable {δ:ℝ}
local notation "ψ"=> T
include hG hc hw hn hm
local notation "Ω"=> Averaging.delta (Y.read f)
local notation "K"=> H/(4*t^ (A.B.a.clock.J (m+1)))
-- pinned ≥poly moments, +1 soft. `Pristine` uses same Common bytes.
lemma guarded (he: Pristine A N m H β δ Z)(hβ:β∈ band P (m+1))(h₁ : Collection.Local Y W f ((1/2:ℝ)*H) r)(hp: E Y L C W f β τ α=Z) :
   (W).threshold^2*|Ω-δ| ≤ K ∧ Cinch.forecastW G c W (Ω-δ) ≤ K ∧
    Nonempty (Pylon W c) ∧ ∀ U:Pylon W c, let p':= Cinch.lacquer U f Y L C α τ β δ
      p'.eval = Z∧ Ingredients (adobe (shelves Y L W) U) (flint U (Ω-δ) (Collection.fill Y L C W f α δ)) W (fraction P m) q ∧ p'.activities.Valid W (fraction P m) q:= by
   obtain ⟨X₁,A',a,b,hA₀,hA,h'⟩:= he.vision
   have hx:=hA₀.H_nonneg; have ht: 1≤t:= (P).fits.delayed m|>.le
   have hd := Bright.here R hm hβ 0
   have hV := Cinch.shimmer (enlarge h₁ (by linarith only [hx] : (1/2:ℝ) * H ≤ H)) hA₀ hG hn (hp.trans hA.symm)
   obtain ⟨ha,hc'⟩:= ((issued («r»:=m) hc).2 c hn hw (W) ⟨rfl,rfl,rfl⟩ rfl (Ω-δ) H hx) (show _ ≤ _ by rw [h']; convert hV using 1; ring) -- scrutiny needs Same
   refine ⟨ha,hc', slate W hn hd.decent.radius, fun U=>?_⟩
   intro p'; let θ:= (W).threshold^2; have ht': 0≤θ:= sq_nonneg _; let H₀:= 3/4*H; have hK: K≤ H/4:=div_le_div_of_nonneg_left hx (by norm_num) (by linarith only [one_le_pow₀ ht (n:=A.B.a.clock.J (m+1))]) -- binder
   have htδ : (W).threshold^2*|δ|≤ H₀:= by
      have hh:= delta_bound hG h₁.projects
      have hD: |δ|= |(δ- Ω)+Ω|:= by rw [sub_add_cancel]
      apply le_trans _ (by unfold θ H₀; linarith only [ha,hK,hh]: θ*|Ω-δ| + θ*|Ω| ≤ H₀)
      rw [hD]; exact (mul_le_mul_of_nonneg_left (abs_add_le ..) ht').trans_eq (by rw [abs_sub_comm,mul_add])
   obtain ⟨hL,hT,hf⟩:= Cinch.financed (τ:=τ) («r»:=β) h₁ hG hd.width (A.B.support.cap N m hm.le) hd.decent hn U (hd.fees 0 (Set.mem_univ _)) H₀ (by unfold H₀; linarith only [hx]) (by unfold H₀; linarith only [hx]) htδ (hc'.trans (by unfold H₀; linarith only [hK]))
   exact ⟨hT.trans hp,hL,hf⟩
end

section shipping
open UVExtension Tabernacle Camp Oriel Charted
variable {S : Dales.Tour R N m n ε₀}{k: Cham A.B.a (m+1) n}{x: Valve (m+1) n A.B.a k} (hv:Reality A.B.a (m+1) n k x β) (s:ℝ)
local notation "x₁"=> mount R N (m+1) n x.val β s
local notation "Yp"=> A.B.a.S.side m n
local notation "U'"=> Tour.oracle R S k hv s
local notation "Ww"=> S.speck R k hv s
omit hm hc hw hn in
lemma preservesP (V:Guild.Crest R ε₀): Pristine A N m H β ((Ww).beta-(β+(A.B.kin.alpha N m))) ((A.B.a.clock.op m n).push β (x₁).eval):= by
    let J:= U'; obtain ⟨a,h⟩:= Native.bill_exists R S k hv s; let X₀:= S.atTopH; let u:= J.song R X₀ S.W S.k
    have hc:= Guild.ready R S.hm X₀ S.W S.k J.atH (J.links R S.atTopH) rfl J.related J.price J.aisle rfl V S.hr
    refine ⟨_, u, _, a,hc,funext h,?_⟩; apply add_sub_cancel_left -- order orientation
end shipping
end YM.Juniper.Cinch
