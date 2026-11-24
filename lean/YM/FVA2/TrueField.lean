import YM.FVA2.Pond
/-!
# Evidenced Field conversion (regularized): coefficientwise control on the actual physical sector
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.FVA2.Fountain
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX
open PositionX.Jet
open Wilson Lattice Gauge PertExtension PertExtension.Chart
open PertExtension.LatticePT RG
open MS MS.Menus MS.Land MS.Theater MS.Tone MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Counterpart Blaze Frost ArchTurn
open PowerSeries WorldJet Metric Pond
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {Q: Booked (wings G)}(V:Warehouse G) (P: Prescription (wings G))(M:MS_Data G Q) 
variable (H:ExactSpin V P)(HI:Trusted P) (he: MixedStory.AllProfiles M V P)
variable {m d:ℕ}(q:ℕ+)(hq:1 < q.val) (j:ℕ) (μ:ℝ)
local notation "Y"=> V.F
local notation "I"=> Fin m
local notation "Ω"=> sameAxis V.F d
set_option quotPrecheck false

def metric (x: Points m) : Fin m→MS.Tone.QP:= fun i=> Theater.out (x i)
abbrev pant {d m:ℕ}(w:Fin m→ BasisIx G d) : Fin m→ Rake.Label (wings G):= ColorCode.labelAt (wings G) ∘ w
def score (s:ℕ)(w: Fin m→ BasisIx G d) (x:Points m):ℂ := Dial.tour M (pant w) μ (metric x) Finset.univ s
def phys (s:ℕ)(x: Points m)(d:ℕ): MultilinearMap ℂ (fun _:Fin m=>E Y d) ℂ:= PositionX.Bare.spread (sameAxis V.F d) (fun w=> score M μ s w x)
variable (w: Fin m→BasisIx G d)
lemma onLit (s:ℕ)(x:Points m) : phys V M μ s x d (Ω ∘ w)= score M μ s w x:= PositionX.Bare.spread_eval ..
-- reading highest.Common facts.
lemma common_L (d:ℕ)(v:E V.F d): Extra.FD.writes V.F d v= Maxwell.Free.address V.F d v:= by obtain ⟨v,rfl⟩:= Table.onto _ _ v; rw [Extra.FD.writes_project,address_eval]; rfl
lemma vintage (x: Points m)(hp: x∈ conf m): phys V M μ 0 x d=visible V.F d x:= by
    apply ( Module.Basis.ext_multilinear (fun _ :Fin m=>Ω)); intro w; change phys V M μ 0 x d (Ω ∘ w)=_; rw [show phys V M _ _ x d _= _ from onLit V M μ w 0 x]; unfold score metric; rw [Dial.highest_zero M μ x (pant w) hp,PositionX.visible_eq ]; congr 1; funext i; change Letters (wings G) (w i) = address V.F _ _; exact Eq.trans (ColorCode.genuine V.F _).symm (common_L V d _)
lemma tower (v:Fin m→ E V.F d)(h:d≤j)(k:ℕ) (x:Points m): phys V M μ k x j (up V.F h ∘ v)= phys V M μ k x d v:= by
   let A:= phys V M μ k x j; let C:= A.compLinearMap fun _=>up V.F h; change C v=_; apply DFunLike.congr_fun; apply ( Module.Basis.ext_multilinear (fun _ : Fin m=> Ω) ); intro i; unfold C A; rw [MultilinearMap.compLinearMap_apply,show (fun t:Fin m=>up V.F h (Ω (i t))) = _ from funext fun t=> same_up V.F h (i t) ]; change phys V M μ k x j (sameAxis V.F j ∘ fun t=> includeI (wings G) h (i t))= phys V M μ k x d ( Ω ∘ i ); rw [ onLit,onLit ]; rfl
lemma metric_ok : Continuous (metric (m:=m)):= continuous_pi (fun i=> Theater.out.toContinuousLinearEquiv.continuous.comp (PiLp.continuous_apply 2 (fun _:Fin m=>E4) i) )
lemma metric_conf {x: Points m}(hp:x∈conf m): metric x∈CompactRate.disjoint _ := Injective.comp (Theater.out.injective) hp
lemma smoothL (x:Points m)(hp:x∈ conf m): ContinuousAt (score M μ j w) x:= ( Dial.contin M (pant w) _ (metric_conf hp) Finset.univ j μ ).1.comp metric_ok.continuousAt
lemma shapes (x:Points m)(v:Fin m→ E V.F d)(hx:x∈ conf m): ContinuousAt (fun x=> phys V M μ j x d v) x:= by
   unfold phys; simp_rw [fun z :Points m=> PositionX.Bare.spread_value (sameAxis V.F d) (fun w=> score M μ j w z) v]; exact tendsto_finsetSum _ fun i _ => ( smoothL M j μ i x hx ).const_mul _

local notation "N"=> LatticePT.side q
local notation "ϵ"=> LatticePT.epsilon q
local notation "ψ"=> Pond.clock q
abbrev fund (G:Gauge)(r:ℕ) := Module.finBasis ℝ (Wilson.Field G (LatticePT.side q r))
abbrev gates (G:Gauge)(r:ℕ):= Module.finBasis ℝ (Param G (LatticePT.side q r))
-- Kernel near mesh. `chartXYZ`
def tuition (o:LatticePT.Native q j)(v:Fin m→ LatticePT.Native q j)(d:ℕ): Court (E V.F d) m Cn:= altered V P H HI (side_even q j) ( fund q G j ) (gates q G j) (fun i=>v i + o) d (sx:=ϵ j) (x:=μ-ψ j)
lemma fresh (g:ℕ): ∏ i:Fin m,(((ϵ g:ℂ)^(w i).size))⁻¹= Port.τ (Vane.charge (Label.h ∘ pant w) Finset.univ) ( Pond.clock q g ) := by
   rw [Pond.ticket ]; unfold Port.τ; rw [zpow_natCast,Real.exp_neg,Complex.ofReal_inv ]; let x:ℝ:=Real.exp (Pond.clock q g); unfold Vane.charge; push_cast; -- product inverse
   simp_rw [inv_pow,inv_inv,Finset.prod_pow_eq_pow_sum ]; rfl
lemma secret (o:LatticePT.Native q j)(u:Fin m→ LatticePT.Native q j)(k:ℕ) : PowerSeries.coeff k ( tuition V P H HI q j μ o u d (Ω ∘ w) ) = Pond.markedPrice μ (pant w) V P (side q j) ( Pond.clock q j ) (Lattice.lift o) (Lattice.lift ∘ u) Finset.univ k:= by
    let A:= Lattice.lift o; let c:= Lattice.lift ∘ u
    have hv (i:I): u i + o= Channel.coord (side q j) A c i:= by unfold Channel.coord; rw [map_add ]; unfold A c; simp [add_comm];
    unfold tuition; rw [ funext hv, ← Clock.out_coeff,WorldJet.alters V P H HI (epsilon_pos q j).ne' A c, show (∏ i:Fin m,(↑(ϵ j) ^ (Glyph.size ∘ w) i)⁻¹ :ℂ)=_ from fresh q w j ]; rfl
lemma metric_sample (k:ℕ)(v:Fin m→ LatticePT.Native q k): metric (Grid.sample q k v)= Pond.site q k (Lattice.lift ∘ v):= by funext i; rw [ Grid.sample_eq, metric, points_apply ]; unfold LatticePT.point site; rw [Pond.ticket, Function.comp_apply,map_smul ]; rfl
-- output.Mc index.Heaps
variable {W: Set ( Points m )} (hw: W⊆ conf m)(hC:IsCompact W)
def feel (q:Side)(n:ℕ) : ℝ := Real.exp ( -mildG * Pond.clock q n )
lemma cost_pos (i:ℕ) :0 < feel q i:= Real.exp_pos _
local notation "pS" i=> Grid.sample q i
include hw hC he hq
lemma rate_pointBasis (t:ℕ) : ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop, ∀ o∈origins q i,∀ u: Grid.offsets q m i, Grid.sample q i u ∈ W → dist ( coeff t ( tuition V P H HI q i μ o u d (Ω ∘ w) ) ) (score M μ t w (Grid.sample q i u)) ≤ C*feel q i:= by
   let T:= metric (m:=m) '' W; have hp:T⊆ CompactRate.disjoint I := by rintro _ ⟨x,hx,rfl⟩; exact metric_conf (hw hx)
   obtain ⟨c,hc,h,hT⟩:= Pond.power M q hq μ (pant w) hp ( hC.image metric_ok ) V P he Finset.univ t; refine ⟨ c,hc,?_ ⟩; filter_upwards [eventually_ge_atTop h] with i hi o ho u hu; rw [secret,score, metric_sample]; -- rw changes u!? indices dependent. inspect
   obtain ha := hT _ hi _ (fromToday q i o ho) _ (show Pond.site q i (Lattice.lift ∘ u)∈ T from ⟨Grid.sample q i u,hu,metric_sample q i u⟩); simp_rw [Pond.times] at ha; exact ha
lemma rate_point (t:ℕ)(v:Fin m→ E V.F d) : ∃ C:ℝ,0<C∧∀ᶠ i:ℕ in atTop, ∀ o∈origins q i,∀ u: Grid.offsets q m i, Grid.sample q i u ∈ W → dist ( coeff t ( tuition V P H HI q i μ o u d v ) ) (phys V M μ t (Grid.sample q i u) d v) ≤ C*feel q i := by
   let Q:= Ω; let Wμ (w: Fin m→ BasisIx G d):ℂ:= ∏ j:Fin m, Q.coord (w j) (v j); choose C h hc using fun w:Fin m→ BasisIx G d=> rate_pointBasis V P M H HI he q hq μ w hw hC t;
   let R:ℝ:= ∑ w:Fin m→BasisIx G d, ‖Wμ w‖*C w; refine ⟨R+1, ?_,?_⟩; · have hm:0≤R:= Finset.sum_nonneg fun i _=> mul_nonneg (norm_nonneg _) (h _|>.le); linarith
   filter_upwards [eventually_all.mpr hc] with i hx o ho u hu;
   let M0:= tuition V P H HI q i μ o u d; let L0:= ( coeff t|>.compMultilinearMap M0 ); let S:= phys V M μ t (Grid.sample q i u) d; let X:= L0-S
   rw [dist_eq_norm ]; change ‖X v‖≤ _; apply le_trans ?_ (mul_le_mul_of_nonneg_right (show R≤R+1 by linarith) (cost_pos q i).le);
   unfold R; rw [ WorldJet.countr Y Q X, Finset.sum_mul ]; apply le_trans ( norm_sum_le .. ); apply Finset.sum_le_sum; intro a _;
   change ‖Wμ a * X (Q ∘ a)‖ ≤ _; have hm: ‖ X (Q ∘ a)‖≤ C a* feel q i:= by obtain hm:= hx a o ho u hu; rw [ ← onLit V M , dist_eq_norm ] at hm; exact hm
   rw [ norm_mul, mul_assoc ]; exact mul_le_mul_of_nonneg_left hm (norm_nonneg _)
omit hw hC in
lemma density (t:ℕ) (v:Fin m→ E V.F d) (w: (i:ℕ)→ Native q i)(hw:∀ᶠ i in atTop, w i∈ origins q i)(x:Points m)(hx:x∈conf m)(u: (i:ℕ)→ Grid.offsets q m i) (hu:Tendsto (fun i=> Grid.sample q i (u i)) atTop (𝓝 x)) : Tendsto (fun i=>coeff t ( tuition V P H HI q i μ (w i) (u i) d v )) atTop (𝓝 ( phys V M μ t x d v )):= by
     obtain ⟨e,he',heE⟩:= (nhds_basis_closedBall.mem_iff).1 ((conf_open m).mem_nhds hx);
     obtain ⟨C,h,hC⟩:= rate_point V P M H HI he q hq μ heE (isCompact_closedBall x e) t v;
     have hh:= (shapes V M t μ x v hx).tendsto.comp hu;
     apply Metric.tendsto_nhds.mpr; intro u' hp; have hv:Tendsto (feel q) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp ( (Pond.forward q hq).const_mul_atTop_of_neg (neg_lt_zero.mpr mild_p) );
     obtain hm:= (Metric.tendsto_nhds.mp hh) _ ( half_pos hp ); -- redundant `_`: read.
     filter_upwards [ hC,hv.eventually (gt_mem_nhds (div_pos (half_pos hp) h)),hm,hw, hu.eventually ( closedBall_mem_nhds x he' ) ] with i hI hv hh hc he;
     apply lt_of_le_of_lt (dist_triangle _ (phys V M μ t (Grid.sample q i (u i)) d v) _); exact ( add_halves u' ) ▸ add_lt_add ( (hI _ hc _ he).trans_lt ( by rw [mul_comm]; exact (lt_div_iff₀ h).mp hv ) ) hh
end YM.FVA2.Fountain
