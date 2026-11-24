import YM.QuadraticLocal.Earn.Payload
import YM.QuadraticLocal.Echo.Scone
/-!
# `Press` rolls: literal observation of output at root poses

This is the unsubtracted prescription. All output labels participate
(not just the subset that made it through the paid short comparison with
mask costs). Coalescing/repricing kernels in `Press.estate` does not move
these couplings. `Row.powered` lifts a row to the native Fk convention of
multiplying by positive powers of g BEFORE `markLetter`. It takes unmasked
values. It's (up to the spectator/test scalar) `Loan.letter`, not the value
at a pure abelian field.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Earn
open Function Filter Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid Planned.JetPort
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Haiku.Coat AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration AllOrder.Catch AllOrder.Catch.Clock AllOrder.Floe AllOrder.Plateau
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V:Type}{G:Gauge} {n c:Side} {k j e d r:ℕ} {a b σ :ℝ}
open Aperture Poetry Echo Work.G05 Toggle Aux Aux.Name Marker
open QuadraticLocal.Sunrise
namespace Wrap
variable {M : Type}[DecidableEq M][Fintype M]
lemma summable_label (X:Roll G M)(q:M)(W:M→Site n)(h:X.Faith univ q k σ a)(hx:0<σ)(v:Link G n)(e d:ℕ): Summable (Spot.label q W X e d v):=by
 let y:= Kinetic.Port.exteriorL G n v; let j:=e+d; let i:= (e+d)-e+k
 obtain ⟨Z,hp⟩:= paint_supply G i; have hv:= Trace.cali q W X h y hp 1 zero_lt_one hx (he:= show e≤j from by omega) le_rfl d (show d≤j from by omega) -- arg he check
 simpa only [bend,y,inv_one,one_smul,ContinuousLinearEquiv.symm_apply_apply,one_pow, one_mul] using hv
end Wrap
variable {ι α : Type} [DecidableEq V] {P:Passport n V} {R:Census V}
open Comparison.RG02
namespace Row
variable (J:Row P R G α)(t:α)(n₀:ℕ)(A:Stationary.Link G n)
set_option quotPrecheck false
local notation "Lx"=> J.lamp
local notation "χ"=> Stationary.Link G n
def powered (g:ℝ): Config G n→ℂ:= fun y=> J.paint t *Complex.ofReal (Loan.letter J.lamp J.atom J.center g y)
local notation "F"=> powered J t
lemma value (g:ℝ)(hg:g≠0)(y:Config G n): F g y= g^J.lamp.power • J.nominal g t y:=by
 have h:= Loan.emission J.lamp J.atom J.center g hg y; change _= (g^J.lamp.power) • (J.paint t * Complex.ofReal (g^J.lamp.lag*J.atom.unmasked y J.center)); rw [← h]; unfold powered; have hℂ:(Complex.ofReal g)≠0:= Complex.ofReal_ne_zero.mpr hg; rw [Complex.real_smul]; push_cast; field_simp -- smul synt.
-- helper on all-L grammar.Mark sum currency.Coherent all fields and orders <= any d.
def markReceipt (u:ℕ)(A:Stationary.Link G n): ℝ:= if J.lamp.e≤u then Radial.jet (Helmet.frame J.atom J.center) (u-J.lamp.e+J.lamp.r) A else 0
local notation "Γ"=> J.markReceipt n₀ A
-- estimate.Five.
lemma powered_graded : Assembly.GradeAt (J.lamp.power+J.lamp.e) (Bulk.projected (J.powered t)) := (Loan.frame J.lamp J.atom J.center).linear_contact (J.paint t • Complex.ofRealCLM) -- maybe mul_comm (toSpanSingleton)?
local notation "Υ"=> J.lamp.power
local notation "ν"=> J.nominal
-- Strip analytic TRUE relative grade exponent.n. use at projection by multiplying by external scalar.
lemma powerAudit : Assembly.jet (fun z:ℝ×Stationary.Link G n=> J.powered t z.1 (Stationary.input G n z.2)) (J.lamp.power+n₀) (1,A)= J.paint t * Complex.ofReal (J.markReceipt n₀ A):=by
 let f:= Helmet.frame J.atom J.center; have he: Assembly.GradeAt J.lamp.r f:= Helmet.frameGrade ..; let L(y:ℝ×χ):= y.1^J.lamp.stamp*f y.2; let M := (ContinuousLinearMap.toSpanSingleton ℂ (J.paint t)).restrictScalars ℝ ∘L Complex.ofRealCLM
 have hV(k:ℝ):M k=J.paint t * Complex.ofReal k:= mul_comm ..
 rw [show (fun z:ℝ×Stationary.Link G n=> J.powered t z.1 (Stationary.input G n z.2))= M ∘ L from funext fun k=> (hV _).symm]; rw [← Assembly.jet_apply_left M L _ ?_ _,hV]; rotate_left;
 · exact (ContDiffAt.mul (contDiffAt_fst.pow _) (he.smooth.comp (0:ℝ×χ) contDiffAt_snd)).of_le le_top -- comp type
 congr 2; change Radial.jet (fun z:ℝ×χ=> z.1^_*f z.2) _ (1,A)= _; unfold markReceipt; split;
 next hr=> have hz:= J.lamp.recovery; rw [favor_exp f he.smooth,if_pos (show J.lamp.stamp ≤ J.lamp.power+n₀ by unfold Loan.power; omega),one_pow,one_mul]; congr 1; unfold Loan.power; omega
 next hr=> exact favor_pocket f he.smooth (J.lamp.power+J.lamp.e) J.lamp.r J.lamp.stamp _ he.vanish 1 A (by unfold Loan.power; have h:=J.lamp.recovery; omega) (by omega)
end Row
namespace Press
set_option quotPrecheck false
open Club
variable (q:Ratio c n) (X:ι→ Row P R G α)(C:Club X)(F:Press X k)(B:Press.Receipt X F σ a)
variable (i:Fin (k+1)) (p:Press.Palette X q F C)
local notation "E"=> Press.estate X C q F B
local notation "S" i:max=> F.news C i
local notation "S₀"=> S p.fst
local notation "qx"=> Club.lowest X C
local notation "W"=> Club.site X C q
local notation "Θ" f:max i:max=> Spot.label qx W (S i) i.val f
variable (ρ:ℝ)(x:Stationary.Link G c)(t:α)
local notation "U'"=> Press.plant X C q F p
local notation "P₀"=> (p.fst.val:ℕ)
local notation "φ"=> C.val
local notation "α'"=> ∏ i∈C.val,(X i).paint t
local notation "z₁" v:max=> (E v ρ)
local notation "A0" f:max v:max=> (z₁ v).markReceipt f x
include B
-- address witnesses use exact `Mint` lengths. Age rates via `Row.powerAudit`
lemma inception (d:ℕ): (U').atom.budget ρ * (Press.estate X C q F B p ρ).markReceipt d x = Spot.label (Club.lowest X C) (Club.site X C q) (S p.fst) p.fst.val d x p.snd.val := by
 have he:= Press.magnitude X C q F p ρ; let p':=U'; let s:= p'.atom.budget ρ; let f:=Helmet.frame p'.atom (Club.roof X C q); let L'(i:ℕ):= d-i+(p').r; let y:= Helmet.frame (Bloom.letdown p'.atom s⁻¹) (Club.roof X C q); have hc:y=s⁻¹ • f:=funext fun i=> Bloom.grant _ _ _ _; unfold Spot.label; simp_rw [p.snd.prop.1,true_and]; -- `if_and` works?
 unfold Row.markReceipt; change s * (if p.fst.val≤d then Radial.jet y (L' p.fst.val) x else 0) = if p.fst.val≤d then Radial.jet f (L' p.fst.val) x else 0; split <;> rename_i hl; · rw [hc]; unfold Radial.jet; rw [iteratedFDeriv_const_smul_apply ((Helmet.frameGrade p'.atom (_:Site c)).smooth.of_le le_top : ContDiffAt ℝ _ f 0)]; simp only [_root_.smul_apply,smul_eq_mul]; have hps:0<s:=he; field_simp; ring
 rw [mul_zero]
lemma witness (d:ℕ) : (z₁ p).paint t * Complex.ofReal (A0 d p) = (∏ i∈C.val,(X i).paint t)*Complex.ofReal (Spot.label qx W (S p.fst) p.fst.val d x p.snd.val):=by rw [← inception q X C F B p ρ x d]; unfold Press.estate; dsimp only; push_cast; ring
omit B
private lemma missed (i:Fin (k+1))(u:(F.news C i).Ty)(d:ℕ)(hh: u∉Set.range (Subtype.val : Mint X q C (F.news C i)→ (F.news C i).Ty)): Spot.label qx W (F.news C i) i.val d x u = 0:= by
 unfold Spot.label; split; next h=>
    let v:= (F.news C i).leg u; have he:v.atom.magnitude ≤ 0:=le_of_not_gt fun h' => hh ⟨⟨u,h.1,h'⟩,rfl⟩; have hν : Helmet.frame v.atom ((Club.site X C q) (Club.lowest X C))=0:= funext fun i=> Bloom.awaken _ _ _ (le_antisymm he (Texture.mag_nonneg _)) -- ellipsis check
    change Radial.jet (Helmet.frame v.atom ((Club.site X C q) (Club.lowest X C))) _ _=_; rw [hν]; unfold Radial.jet; simp
 next=> rfl
local notation "U" i:max=> Press.Mint X q C (F.news C i)
local notation "Γ" i:max=> F.news C i
local notation "υ" i:max=> (S i)
local notation "Ύ" i:max x:max=> (show Press.Palette X q F C from ⟨i,x⟩)
variable (hx:0<σ)
include B hx
local notation "µ" d:max v:max=> ((z₁ v).paint t*Complex.ofReal (A0 d v))
local notation "D" i:max d:max=> (∑ a':Site c, ∑' j,Lantern.gleam ((F.news C i).leg j) a' (Bunch.mapC (Club.site X C q)) i.val d x)
lemma cluster (d:ℕ): HasSum (fun u:Press.Mint X q C (F.news C i)=> (z₁ (Ύ i u)).paint t*Complex.ofReal ( (z₁ (Ύ i u)).markReceipt d x)) ((∏ i∈C.val,(X i).paint t) * Complex.ofReal (D i d)):= by
 let L:= Spot.label (Club.lowest X C) (Club.site X C q) (F.news C i) i.val d x; have hf:= (Wrap.summable_label (F.news C i) qx W (B.care C i) hx x i.val d).hasSum
 have he : HasSum (L ∘ (Subtype.val : (U i)→_)) (∑ a:Site c,∑' j,Lantern.gleam ((F.news C i).leg j) a (Bunch.mapC (Club.site X C q)) i.val d x) := (Spot.anthem (Club.lowest X C) W (F.news C i) (B.care C i) i.val d x) ▸ ?_
 rotate_left
 · exact (Function.Injective.hasSum_iff Subtype.val_injective fun u hu=> missed q X C F x i u d hu).2 hf
 refine (((Complex.ofRealCLM.hasSum he).mul_left (∏ i∈C.val,(X i).paint t))).congr_fun fun v=>?_ -- signature
 exact (witness q X C F B (Ύ i v) ρ x t d) -- orientation
-- Press independent Cover.Plan shape.
abbrev Newspapers (d:ℕ)(Y:rule (Club.Keys X C) c) : ℝ:= ∑ i:Fin (k+1),∑ a':Site c, ∑' j,Lantern.gleam ((F.news C i).leg j) a' Y i.val d x
lemma rollCall (d:ℕ): HasSum (fun p:Press.Palette X q F C=> ( Press.estate X C q F B p ρ).paint t*Complex.ofReal ( Press.estate X C q F B p ρ|>.markReceipt d x)) ((∏ i∈C.val,(X i).paint t)*Complex.ofReal (Press.Newspapers X C F x d (Bunch.mapC (Club.site X C q)))) := by
 let g(i:Fin (k+1)):ℂ:= (∏ i∈C.val,(X i).paint t)*Complex.ofReal ((∑ b: Site c, ∑' j,Lantern.gleam ((F.news C i).leg j) b (Bunch.mapC W) i.val d x)); unfold Press.Newspapers; rw [Complex.ofReal_sum,Finset.mul_sum]
 let f(p: Press.Palette X q F C):= (µ d p); have h(i:Fin (k+1)): HasSum (fun y=>f ⟨i,y⟩) (g i):= cluster q X C F B i ρ x t hx d -- order
 have hp : HasSum g (∑ i:Fin (k+1),g i):= hasSum_fintype _; have he: Summable f:= Summable.of_norm (summable_sigma_of_nonneg (f:=fun x=>‖f x‖) (fun v=> norm_nonneg _)|>.2 ⟨fun i=> (h i).summable.norm,(hasSum_fintype _).summable⟩)
 change HasSum f (∑ i:Fin (k+1),g i); exact hp.unique (he.hasSum.sigma h) ▸ he.hasSum
end Press
end YM.QuadraticLocal.Earn

