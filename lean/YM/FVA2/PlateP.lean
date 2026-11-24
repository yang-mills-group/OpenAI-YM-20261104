import YM.FVA2.TrueField
/-!
# Profile smearing uses same convention on marked arrays. Bare cancellation sold separately.

Coefficientwise regulators removed in this reading as well. This step uses scaled point estimates
with only convergence in the sampling theorem: not a quantitative quadrature rate.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 860000
namespace YM.FVA2.Spring
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX PositionX.Jet PositionX.Bare.Subcell
open Lattice Gauge PertExtension PertExtension.Chart PertExtension.LatticePT
open MS MS.Menus MS.Land MS.Theater MS.Tone MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open ColorCode Attend BoxOffice Counterpart Blaze Frost ArchTurn
open PowerSeries WorldJet Pond Fountain
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {Q: Booked (wings G)}(V:Warehouse G) (P: Prescription (wings G))(M:MS_Data G Q)
variable (H:ExactSpin V P)(HI:Trusted P) (he: MixedStory.AllProfiles M V P)
variable {m d:ℕ}(q:ℕ+)(hq:1 < q.val) (j:ℕ) (μ:ℝ)
local notation "Y"=> V.F
local notation "I"=> Fin m
local notation "Ω"=> sameAxis V.F d
local notation "Ξ"=> tuition V P H HI q
variable (v: Test m)(X:Fin m→ E V.F d)
local notation "Z"=> LatticePT.epsilon q
local notation "ψ"=> Pond.clock q
private def smeared (d:ℕ)(f:Test m)(k:ℕ) : MultilinearMap ℂ (fun _:Fin m=> E Y d) ℂ := PositionX.Bare.spread (sameAxis V.F d) (fun w=> f.applyTo (score M μ k w))
def ms (d n:ℕ) : Bank V.F d:= fun _ t=>smeared V M μ d t n
local notation "Γ"=> ms V M μ
-- read by point integral.
lemma payable (i:ℕ): Integrable (fun z=>v z*phys V M μ i z d X):= Test.smearing v (fun x hx=> (shapes V M i μ x X hx).continuousWithinAt ) -- syntax
lemma invoice (k:ℕ) : Γ d k m v X=v.applyTo (fun z:Points m=> phys V M μ k z d X):= by
   let F:= sameAxis V.F d; let t(i: Fin m→BasisIx G d):ℂ:= ∏ j,F.coord (i j) (X j)
   have ht(z): phys V M μ k z d X=∑ i:Fin m→BasisIx G d,t i* score M μ k i z:= PositionX.Bare.spread_value ..; change smeared V M μ d v k X=_; rw [smeared, PositionX.Bare.spread_value ]; unfold Test.applyTo; simp_rw [ ht, Finset.mul_sum,mul_left_comm (v _) ]; rw [ MeasureTheory.integral_finsetSum _ (fun i hi=>?_ ) ]; simp_rw [ integral_const_mul ]; rfl; exact (v.smearing (K:=score M μ k i) (fun x hx=> ( smoothL M k μ i x hx ).continuousWithinAt )).const_mul _
lemma vintage_ms (d:ℕ) : Γ d 0=pureBank V.F d := by
    funext n t; ext1 v; rw [invoice ]; apply Test.apply_eq; intro x hx; exact DFunLike.congr_fun (vintage V M μ x hx ) v
lemma valley_ms (h:d≤j)(k:ℕ) : pulls (up Y h) (Γ j k)=Γ d k:= by
    funext n t; ext1 p; change ms _ _ _ j k _ _ (up _ _ ∘ p)= _; rw [invoice,invoice ]; exact Test.apply_eq t (fun x _=> tower V M j μ p h k x)

-- weighted shift p averaging.Grid.sample.Note term. Keep cube even CE. Uniform frame output x.Center.
private def sweepC (x:ℝ) : Points m→ℂ:= fun i=> (sweep (Complex.re ∘ v) x i:ℂ)+Complex.I*(sweep (Complex.im ∘ v) x i:ℂ)
private lemma weight (k:ℕ)(v: Test m)(x: Fin m→ Site (side q k)): zoneμ q k x v= ((origins q k).card:ℝ)⁻¹ • sweepC v (Z k) (Grid.sample q k x):= by
   rw [ zoneμ,sweepC, Mixed.price, Mixed.price, Grid.sample_eq ]; push_cast; rw [smul_add]; rw [ Complex.real_smul ,Complex.real_smul ]; simp only [Function.comp_apply]; push_cast; ring

def prem (i r:ℕ) (o:LatticePT.Native q i)(w: Grid.offsets q m i) := sweepC v (Z i) (Grid.sample q i w) * PowerSeries.coeff r ( tuition V P H HI q i μ o w d X )
lemma green (k:ℕ) (L:ℂ→L[ℝ] ℝ):
    L (changedWorld V P H HI q j (μ-ψ j) d k m v X) = ((origins q j).card:ℝ)⁻¹*∑ o∈origins q j, Z j^(4*m)* ∑ w:Grid.offsets q m j,L ( prem V P H HI q μ v X j k o w ) := by
   let R:= LatticePT.Native q j; let p:ℝ:= ((origins q j).card:ℝ)⁻¹;
   rw [ WorldJet.plotE _ _ _ _ q j (μ-Pond.clock q j) ( fund q G j ) (gates q G j) v X k ]; simp_rw [ map_sum, map_smul (coeff _), weight, Finset.mul_sum, smul_eq_mul]; -- wrong last
   rw [ Finset.sum_comm ]; refine Finset.sum_congr rfl fun i _=> ?_; refine Finset.sum_congr (@univ_unique _ _ _) (fun t _=> ?_ ); unfold prem; let a:= sweepC v (Z j) (Grid.sample q j t); let b:= coeff k ( tuition V P H HI q j μ i t d X ); let u:= Z j; change L (p • a * (((u:ℂ)^4)^m)*b)=p*( u^(4*m)* L (a*b)); rw [ smul_mul_assoc, smul_mul_assoc,map_smul ]; congr 1; rw [ show a*((u:ℂ)^4)^m*b=(u^(4*m):ℝ) • (a*b) from ?_, map_smul ]; rfl; rw [ Complex.real_smul ]; push_cast; rw [ pow_mul ]; ring
private lemma sailC : Continuous (fun z:ℝ×Points m=> sweepC v z.1 z.2):= by
   have he (L:ℂ→L[ℝ]ℝ) := (Complex.ofRealCLM.continuous.comp (sweep_ok (L ∘ v) ( L.continuous.comp v.continuous )) ); exact ((he Complex.reCLM).add ((he Complex.imCLM).const_mul Complex.I))
include he hq
private lemma history (p:ℂ→L[ℝ]ℝ) (o:(t:ℕ)→ Native q t)(hO:∀ t,o t∈ origins q t):
    Tendsto (fun i:ℕ=> Z i^(4*m) * ∑ w: Grid.offsets q m i,p (prem V P H HI q μ v X i j (o i) w)) atTop (𝓝 ( p (Γ d j m v X) )):= by
    let F (k:ℕ)(w:Grid.offsets q m k):= p (prem V P H HI q μ v X k j (o k) w); let W:= valley (tsupport v); have ht:= valley_compact (h:=v.hasCompactSupport); have hh: W⊆ conf m := valley_conf (show tsupport v ⊆ conf m from v.tsupport_subset);
    rw [ invoice, Test.applyTo, ← p.integral_comp_comm (payable V M μ v X j) ];
    have hx:= Grid.integrable_spots (F:=F) (T:=fun x:Points m=> p ( v x * phys V M μ j x d X )) (K:= W) hq ?A ht ?P ?R; exact hx.2
    case A=> intro u x h hh1; have heV:= Fountain.density V P M H HI he q hq μ j X o (Eventually.of_forall hO) x ( hh h ) u hh1; let φ(t:ℕ):= ( Z t,Grid.sample q t (u t)); have hφ:Tendsto φ atTop (𝓝 (0,x)):= ((epsilon_zero hq).mono_right nhdsWithin_le_nhds).prodMk_nhds hh1; have hp : Tendsto (fun i=> sweepC v ( φ i ).1 ( φ i ).2 ) atTop (𝓝 ( v x )):= by
              obtain hK : sweepC v 0 x=v x:= by unfold sweepC; rw [no_sweep,no_sweep ]; rw [mul_comm Complex.I]; exact (v x).re_add_im
              rw [← hK]; exact (sailC v).continuousAt.tendsto.comp hφ
             exact p.continuous.continuousAt.tendsto.comp (hp.mul heV)
    case P=> intro k t hs; unfold F prem; have hv(L:ℂ→L[ℝ]ℝ): sweep (L ∘ v) (Z k) (Grid.sample q k t)= 0:= sweep_in ⟨(epsilon_pos q k).le,PositionX.Bare.Subcell.small q k⟩ ( fun x hz=> by_contra (fun hc=>hz (subset_closure (fun ht=> hc (by rw [comp_apply,ht,map_zero ]))))) hs; unfold sweepC; rw [ show sweep (Complex.re ∘ v) _ _=_ from hv Complex.reCLM, show sweep (Complex.im ∘ v) _ _=_ from hv Complex.imCLM ]; simp
    case R=> intro x hx; rw [show v x=0 from by_contra (fun h=> hx (includes _ (subset_closure h))), zero_mul,map_zero ]
theorem agrees : Tendsto (fun k=>changedWorld V P H HI q k (μ-ψ k) d j m v X ) atTop (𝓝 ( Γ d j m v X )):= by
     let x(k):= changedWorld V P H HI q k (μ-Pond.clock q k) d j m v X; let p:= Γ d j m v X; have hK(k):((x k).re:ℂ)+((x k).im:ℂ)*Complex.I=x k:= Complex.re_add_im ..; have hv (L:ℂ→L[ℝ]ℝ) : Tendsto (L ∘ x) atTop (𝓝 (L p)):= by
        unfold x; simp_rw [Function.comp_def, green ]; exact Grid.average_paths ( fun m=> hasOrigin q m ) (history V P M H HI he q hq j μ v X L) -- he shadow
     change Tendsto x atTop (𝓝 p); nth_rw 1 [← p.re_add_im ]; exact ((Complex.ofRealCLM.continuous.continuousAt.tendsto.comp (hv Complex.reCLM)).add (( Complex.ofRealCLM.continuous.continuousAt.tendsto.comp (hv Complex.imCLM) ).mul_const Complex.I)).congr (fun k=> hK k)
end YM.FVA2.Spring
