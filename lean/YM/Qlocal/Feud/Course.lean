import YM.Qlocal.Feud.Mission
/-!
 # Actual price restoration for ready model in the full coordinate assembly
 Theta read at the coupling with all log tags. Translate from G.Polynomial to whole V.Q.Projection.
 `d` physical scale on X. Body uses stencil/support in additional certificate. Forecast exact unmasked;
 not for Mask.L.Stencil call until applying Health.W. Model reconstruction cost if high-power gaps; track powers.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Feud
open Function Filter Set Metric Lattice MeasureTheory ProbabilityTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis Bid
open AllOrder Ker Laplace Laplace.SigmaP Response Catch
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open Marker Multi PertExtension.Series Radial Extra.Iteration Floe PositionX.Jet
open Comparison.RG02.Order
open Comparison.RG02.Assembly
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge} {k j m i q r n:ℕ} {c f :Side}{S:StepData c f} {b a α δ t:ℝ}
open Quipu.Sonnet
namespace Peak
open Quipu Quipu.Sonnet Tern
variable {ι σ:Type*}{V:Type}[DecidableEq V]{Z:Marker.Census V}
open Cider Quipu.Sonnet.Tern.Stanza Bind Horn
open PertExtension PertExtension.Series Sienna Lantern Catch Catch.Clock Aux.Name Presented Poll
open Tensor
variable {S':Catch.Clock ι}{P:Patch}{K:KernelChoices}{v:Stage}{u:ℝ→ℝ}{κ:ℕ}{F:Uniform.Before G v.width v.paths P.J K (k+3+3)}
-- basic Ray.Actual.Name. Σ_j ≤k normalized with ξ sloping power.Preserve.
section tickets
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {x:E}{q :ℕ}{b t:ℝ} {u:E→ℝ}
lemma thor (i:ℕ)(u:E→ℝ)(x:E): Radial.jet u i x=diagonal (Tensor.coeff u i 0) x:= rfl
lemma illuminate (he: t≠0)(h:GradeAt q u)(x:E)(j:ℕ): (t^q)⁻¹*Work.G05.blockTaylor (q+j) u (t•x)=delay (fun i=> Radial.jet u (q+i) x) j t:= by
 unfold Work.G05.blockTaylor; rw [Finset.sum_apply]; simp_rw [← thor]; rw [show q+j+1=q+(j+1) by omega,sum_range_add,Finset.sum_eq_zero]; swap; · intro i hi; exact h.jet_z _ (mem_range.mp hi)
 rw [zero_add,Finset.mul_sum]; unfold delay; refine Finset.sum_congr rfl (fun i hi=> ?_); simp_rw [thor,homogeneous,smul_eq_mul]; rw [pow_add,mul_assoc,inv_mul_cancel_left₀ (pow_ne_zero _ he)]
-- helper skim.Be.Position
end tickets
variable (W:ι→ Aux.Name G P K u κ v (k+3) F)
    (R:∀ i,Bind.reed G (W i).c) (ht:Aux.Name.Proper W S')
    (d:ι→ℝ)(x:∀ i,(W i).X) (h:S'.Meter d (-(1/2:ℝ)))(hd: ∀ᶠ i in S'.rail,0<d i)(hx:S'.Meter (fun i=> ‖x i‖) (graded 1))
set_option quotPrecheck false
local notation "r'"=> fun i=>‖x i‖+d i+(W i).Θ
local notation "X[" i "]"=>(W i).X
local notation "v[" i "]"=>(W i).Θ
local notation "Z[" i "]"=>ℝ×(W i).X
set_option quotPrecheck false -- earlier
local notation "Q'"=> (S'.book (V:=fun i:ι=>Z[i]) (fun i=>closedBall 0 (r' i)))
local notation "H"=> horizon
local notation "xℓ"=> fun i:ι=> (v[i],x i)
include ht h hx hd
lemma opportunes : S'.Meter r' (-(1/2:ℝ))∧ ∀ᶠ i in S'.rail, d i ≤ r' i∧‖xℓ i‖ ≤ r' i ∧ 0< r' i∧r' i <1:= by
 let hh: S'.Meter r' (-(1/2:ℝ)):= ((hx.weak (by simp [graded])).add h).add (ht.meter W|>.1); refine ⟨hh,?_⟩; filter_upwards [hd,hh.low (by norm_num) (show (0:ℝ)<1 from zero_lt_one)] with i hi hx; let t:= v[i]; have hz: 0 < t:=(W i).Θp; let u:= ‖x i‖; have hp:0≤u:=norm_nonneg _; have h': r' i < 1:= (le_abs_self _).trans_lt hx; refine (show d i ≤ u+d i+t∧‖(t,x i)‖ ≤ u+d i+t∧0< u+d i+t∧u+d i+t <1 from ⟨by linarith,?_,by linarith,h'⟩); rw [Prod.norm_def, max_le_iff]; simp only [Real.norm_eq_abs,abs_of_pos hz]; change t≤ u+d i+t ∧ u≤u+d i+t; exact ⟨by linarith,by linarith⟩
omit ht h hx hd
noncomputable def imprint (k:ℕ)(i:ι)(x:(W i).X) := ((v[i] ^ k)⁻¹:ℝ)*H (R i) (v[i],x)
noncomputable def token (k:ℕ): Canopy.Lithe.Tape (fun i=> (W i).X):= fun i x j=> Radial.jet (H (R i)) (k+j) (1,(v[i])⁻¹ • x)
variable (hR: Ready W S' j R)
local notation "A₀"=> imprint W R
local notation "V₀"=> token W R
local notation "w"=> fun i=>v[i]
include h hx hd ht hR
-- price of ext projection along umbrella.Parameter.G mixed marks.Compare pivot.
lemma book_cover : Catch.Cover (V:=fun i=> Z[i.1]) Q' j 0 (fun _=>1) (fun i=> H (R i.1)) (fun i=> i.2.1):= Catch.Cover.book_home (p:=fun _=>1) (fun i=>closedBall (0:Z[i]) (r' i)) (fun p hp=> ((hR p hp).and (opportunes W ht d x h hd hx).2).mono fun i hi y hy=> hi.1 y ((mem_closedBall_zero_iff.mp hy).trans_lt hi.2.2.2.2))
omit hR in
lemma rim (b:ι→ℝ)(f:∀ i, (ℝ×(W i).X)→ℝ)(h':Catch.Cover S' j a b f xℓ) : Catch.Cover S' j a b (fun i x=> f i (w i,x)) x:=by
 intro e he; filter_upwards [h' e he] with i hi; let y:= (v[i],(0:X[i])); let t:= Lantern.hook (X[i]); let v:= x i; have hw(w0:X[i]): ((W i).Θ,w0) = y+t w0:= by simp [y,t]
 apply (skim v ((hw v) ▸ hi) n_hook).shimmy (Eventually.of_forall (fun w0=> congr_arg (f i) (hw w0)))
include hR
local notation "C"=> Catch.Cover S' j
variable (hV:∀ i, Flute (R i) q)
local notation "π"=>fun i=> (d i)⁻¹
omit h ht hx hd hR in
include hV in
lemma clarke (i:ι): GradeAt q (horizon (R i)):= GradeAt.coarse (f:=Comparison.RG02.Bulk.projected (R i)) (g:=(ContinuousLinearMap.id ℝ ℝ).prodMap (tint G _).toContinuousLinearMap) (hV i).zeroAt (ContinuousLinearMap.contDiff _|>.contDiffAt) (map_zero _) -- `w ledger Planner`
include hV in
lemma paints (hq:q+n<j): C (graded (n+1)) π (fun i=> A₀ q i - Canopy.Lithe.beam (V₀ q) n w i) x:= by
 have hZ := book_cover W R ht d x h hd hx hR; obtain ⟨ha,h₀'⟩:= opportunes W ht d x h hd hx; let U(i):=Work.G05.blockTaylor (q+n) (H (R i)); let v := fun i=>H (R i)-U i; let R':= r'; let H' := fun i=> (r' i)⁻¹; have hp: Catch.Cover S' j (graded (q+n+1)) H' v xℓ:= (((Cover.certainly ha (h₀'.mono (fun i hi=> ⟨hi.2.2.1, hi.2.2.2.le⟩)) (h₀'.mono fun i hi=> hi.2.1) hZ hq)).weak (by unfold graded; simp));
 let V:= fun i:ι=> v[i]; let z i:= (v[i])⁻¹^q; apply Catch.Cover.home ((Catch.Cover.small (Catch.Cover.caliber (rim W ht d x h hd hx H' v hp) (ht.meter W|>.2.pow q)) (g':=π) le_rfl (?_) (?_))); rotate_left
 · unfold graded; push_cast; linarith
 · exact (hd.and h₀').mono fun i hi=> (inv_le_inv₀ (hi.1.trans_le hi.2.1) hi.1).2 hi.2.1
 filter_upwards with i; ext1 u
 let b:= v[i]; have he: 0<b:= (W i).Θp; let t:Z[i]:= (1,b⁻¹ • u); have h : b • t=(b,u):= by simp [t,mul_inv_cancel_left₀,smul_smul,he.ne']
 let f:= H (R i)
 change b⁻¹^q*(f (b,u)-U i (b,u))= (b^q)⁻¹*f (b,u) - delay (fun k=>Radial.jet f (q+k) t) n b; rw [inv_pow,mul_sub,← h, show (b^q)⁻¹*U i (b•t)=delay (fun k=> Radial.jet f (q+k) t) n b from illuminate he.ne' (clarke W R hV i) t n]
omit hR in
lemma shave (R':∀ i,Bind.reed G (W i).c)(e:ι→ℝ) (hE:S'.Meter e (graded (n+q+1)))(he:Razor S' W e j R R'): C (graded (n+1)) π (fun i=> (A₀ q i)- (imprint W R' q i)) x:= by
 obtain ⟨L,hL,rfl⟩:=he; obtain ⟨a,h₀'⟩:= opportunes W ht d x h hd hx; have hh : C 0 π (fun i (x:X[i])=> horizon (L i) (v[i],x)) x:= by
    refine Catch.Cover.small (rim W ht d x h hd hx (fun _=>1) (f:=fun i=> H (L i)) ?_) le_rfl le_rfl (?_); swap
    · exact (((h.low (by norm_num) zero_lt_one).and hd).mono fun i hi=> (show (1:ℝ)≤ (d i)⁻¹ from (one_le_inv₀ hi.2).2 ((le_abs_self _).trans hi.1.le))) -- ordering edit
    exact fun p hp=> ((hL p hp).and h₀').mono fun i hi=> hi.1 _ (hi.2.2.1.trans_lt hi.2.2.2.2)
 let f:= fun i=> -e i*(v[i])⁻¹^q; have ht:S'.Meter f (graded (n+1)):= ((hE.neg).mul (ht.meter W|>.2.pow q)).weak (by unfold graded; push_cast; linarith);
 refine (((hh.caliber ht)).weak (by simp)).home (Eventually.of_forall (fun i=>?_ )); ext x; unfold f imprint horizon; dsimp only [Pi.sub_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul, Campus.oracle]; rw [inv_pow]; ring
end Peak
end YM.Qlocal.Feud
