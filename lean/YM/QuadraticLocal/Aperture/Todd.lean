import YM.QuadraticLocal.Aperture.Gross
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
variable {G:Gauge}{ι:Type*}{T:AllOrder.Catch.Clock ι} {D a B C Ω κ v:ℝ}{j k n m x:ℕ} {V:Type}[Fintype V][DecidableEq V]
variable {P:Patch}{K:KernelChoices}{s:Teller G}{r:Stage}{q:ℝ→ℝ}{U:Push.Uniform.Before G r.width r.paths P.J K ((k+3)+3)}
open Metric ConnectedActivityE6.Coat
open Till Tilt Lantern Aux Aux.Name Token
namespace Gross
variable (W:ι→ Aux.Name G P K q x r (k+3) U) (Q:∀i,(W i).forest.Slice G →ℝ) (Y:∀i,(W i).X)
variable (h:Aux.Name.Proper W T)(hx:T.Meter (fun i=> ‖Y i‖) (-(1/2:ℝ)))
set_option quotPrecheck false
local notation "Z'"=> T.rail
local notation "Ω'"=> (fun i=> (W i).attends (Y i))
variable (hp:∀ᶠ i in T.rail,0< (W i).attends (Y i)) (a:ι→ℝ)(ha : T.Meter a 0)
-- cost AFTER β-normalization at each Point.Level. full Rad b.Beta around Y.
variable (hK:∀ᶠ i in T.rail,Envelope (Q i) ∧∀ x:(W i).forest.Slice G,(W i).newZ (Y i) x≠0→ ‖Q i x‖≤ a i)
local notation "Zeta"=> (fun i=>(Ω' i)⁻¹ • (W i).attends) -- name
local notation "N'"=> (fun i=>(Ω' i)⁻¹ • heat (W i) (Q i))
-- chooses prime appropriate after k.Photo already Taylor.Zoom uses at unscaled 1.Meter interpolation.
include hK h hx hp ha
lemma rite (j:ℕ): Catch.Cover T j (j+(j:ℝ)*j) (fun _=>1) (fun i=>Gross.boundX (W i) (Q i)) Y:=by
 let X i:=(W i).X; let n i:=(W i).vol * (Fintype.card Axis:ℝ)
 have hρ(i:ι): (Fintype.card (Bond (W i|>.c)):ℝ)≤ n i:= by rw [Fintype.card_prod]; push_cast; exact mul_le_mul_of_nonneg_right (W i).loom.primary (Nat.cast_nonneg _)
 obtain ⟨S,hS,H⟩:= h.legible; obtain ⟨C,hC⟩:= paint_supply G j; obtain ⟨U,hU,he'⟩:= Brush.neighborhood 0 (f:=Real.exp) (k:=j) Real.contDiff_exp.contDiffAt; -- label U notation? none
 let Zt i:= (W i).beta; have hz :T.Meter n 0:= (Proper.counts W h).rscale _; let P' t:=Token.prime G K j C U (Zt t) (n t)
 have hE:T.Meter P' j:= by
    unfold P' prime clump; dsimp only; let v i:=|Zt i| * sizeN G K j (n i) C; have hh:T.Meter v 1:= (((Proper.strength W h).ab).mul ((hz.lscale K.penalty).rscale _)).weak (by linarith); let ht:=(Meter.const T 1).weak zero_le_one; exact (((ht.add (((ht.add (hh.add hh))).rscale 1)).pow j).lscale _).weak (by simp)
 let B':=Zeta; let C':=N'; let v:=Ω'; have he(hU0:0 ≤U):∀ᶠ i in Z',Brush j (P' i) 1 (B' i) (Y i)∧ Brush j (P' i*|a i|) 1 (C' i) (Y i):= by
    filter_upwards [H,hK,hp,hx.low (by norm_num) zero_lt_one] with i hi hx hA h'; let g:= W i; have he : 0≤ P' i:= Token.primeN (G:=G) K (W i).bpos le_rfl hU0 hC.1.le ((Nat.cast_nonneg _).trans (hρ i))|>.1; have he'' : prime G g.data.kernel j C U (Zt i) (n i)=P' i:= congr_arg (fun k=> prime G k j C U (Zt i) (n i)) g.rates; rw [← he'']; have ht: ‖Y i‖ <1:=(le_abs_self _).trans_lt h';
    exact ⟨Gross.crowned g hi hC he'.self_of_nhds (hρ i) (he''.symm ▸ he) _ ht hA, Gross.nominated g hi (Q i) hC he'.self_of_nhds (hρ i) (he''.symm ▸ he) (Y i) ht hx.1 (fun y hy=> (hx.2 _ hy).trans (le_abs_self _)) (abs_nonneg _) hA⟩
 let K0:= Catch.Cover.has hE ((he hU.le).mono fun _ hi=> hi.1); let hQ:= Catch.Cover.has ((hE.mul ha.ab).weak (b:=(j:ℝ)) (by simp)) ((he hU.le).mono fun _ hi=> hi.2);
 let f(x:ℝ):=x⁻¹; have ht:Tendsto (fun i=> B' i (Y i)) T.rail (𝓝 1):= tendsto_const_nhds.congr' (hp.mono fun i hi=> (inv_mul_cancel₀ hi.ne').symm); let H₁:= Catch.Cover.comp (f:=B') (Nat.cast_nonneg j) K0 (Catch.Cover.loc (v:=(1:ℝ)) (F:=f) (contDiffAt_id.inv (by simp)) ht); -- args
 refine Catch.Cover.home ((hQ.mul H₁).weak (by linarith)) (hp.mono fun i hi=> ?_); ext1 x; let u:=(W i).attends (Y i); change (u⁻¹ * Gross.heat (W i) (Q i) x) * ((u⁻¹ * (W i).attends x)⁻¹)= _; rw [_root_.mul_inv_rev, inv_inv]; unfold Gross.boundX; rw [div_eq_mul_inv]; field_simp; rw [mul_div_mul_left _ _ hi.ne'] -- if attends x=0? field_simp leaves
end Gross
end YM.QuadraticLocal.Aperture
