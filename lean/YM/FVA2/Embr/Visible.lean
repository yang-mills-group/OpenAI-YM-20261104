import YM.FVA2.Embr.Books
import YM.FVA2.Hearth.Posed
import YM.Work.G05.Taylor
/-!
 # Through accounting after paying Fk's many probes
 Critically, use the *entire* true physical insertion stamp
 (including product and assigned valuation allowance) unlike
 probes available only unmarked. Use one PostFix planet at y, one
 Shelf on it, ALL authorities. Finite then all orders.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Hearth.Clan RGComparison.Core16 Lumen Fk Forge
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{L:Fabric G n}{T:Cloth L}{w:L.Accounts→ℝ→ℝ}
variable {y:Flats G (Bottom L)}{s:G.ColorIndex}{Ω:Lumen.Shelf G Unit (Warm T)}(j:Warm T→Site n)
local notation "Δ"=> Lumen.Point G (Warm T)
local notation "X"=> (Warm T→G.El)
local notation "P"=> Hearth.localClimate T y s w
local notation "P'"=> home T w y s Ω j
variable (F:Habitat T w y s Ω)(J:ChartRatio G)
include F
lemma same_shelves : Fk.rise P =ᶠ[𝓝 0] Fk.rise P':= by
 let v(x:Fk.Door G (Warm T)):= (x.1 • Lumen.colors G s, fun i=>Lumen.turn (x.2 i)); have hv : Tendsto v (𝓝 0) (𝓝 0):= by
    have h:=((show Continuous v from (continuous_fst.smul continuous_const).prodMk (continuous_pi (fun i=> turn_hot.continuous.comp ((continuous_apply i).comp (f:=Prod.snd) continuous_snd)) )).tendsto 0); exact Eq.subst (motive:=fun u=> Tendsto v (𝓝 0) (𝓝 u)) (show v 0=0 from Prod.ext (zero_smul ..) (funext fun i=> turn_zero)) h
 filter_upwards [hv.eventually (closedBall_mem_nhds 0 (F.resolves j).prices.positive)] with u hu
 unfold Fk.rise Fk.lapse; rw [Fintype.sum_unique,Fintype.sum_unique]; exact congr_arg (_ + ·) (F.exactness () (v u) hu).symm

variable {L':Type}
lemma RightHarvest (p:Lumen.Stuff G (Warm T) L')(ψ:(L'→G.Color)→ℝ): Fk.harvest P J p ψ= Fk.harvest P' J p ψ := congr_fun (Therm.stamp_protect _ _ _ (EventuallyEq.refl _ _) (same_shelves j F)) 1
lemma harvestVal (p:Lumen.Stuff G (Warm T) L')(ψ:(L'→G.Color)→ℝ): Fk.valuation P J p ψ= Fk.valuation P' J p ψ:= congr_arg₂ divide (RightHarvest j F ..) ( RightHarvest j F ..)

-- true unmasked LINKS probes
variable (O:Wilson.Config G n →ℝ)(hO:PreTest O)
def scroll (T: Cloth L)(y: Flats G (Bottom L)) : Melody G (Warm T) := fun v x=> attending L O (committed T y v x)
local notation "p" => tease T s
local notation "V"=> scroll O T y
local notation "C'"=> Option (Warm T)→G.Color
lemma relaxed (U:X)(g:ℝ)(hg:0<g) (h:Lumen.Planet.crisp (Ω.δ/2) univ U):
    V g U= lens T y s (Hearth.rad T O) (g • Lumen.book p g U):= by
 let u : C':=g • Lumen.book p g U; have he0 : u none= g • Lumen.colors G s:= rfl
 have he(i):u (some i) = G.curvature (U i):= smul_inv_smul₀ hg.ne' _
 let a := readRay T s u; have ha:a.1=g:= by change u none s=_; rw [he0,Hearth.xseat ..]; -- check
 have hx(i):launch (u (some i))=U i:= by rw [he]; apply (F.resolves (fun _=>0)).prices.reenter; exact (h i (mem_univ _)).trans (half_lt_self (F.resolves (fun _=>0)).prices.extent.1)
 unfold scroll; change _= (Hearth.seed O ∘ line T) (Facade.flank y a); rw [← show (a.1,a.2)=a from rfl,←Hearth.flowed T y O]; congr; rw [ha]; exact (funext hx).symm
include hO
lemma seen : ∃ c, Lumen.Visible Ω (lens T y s (Hearth.rad T O)) V p (Fintype.card (Warm T)) c:= by
 obtain ⟨a,h⟩:= (eligible L hO).reading.bounded
 have hp(g:ℝ)(x:X): ‖V g x‖≤a:= h _; refine ⟨ a,fun g _=> ⟨((eligible L hO).reading.meas.comp ((committed_cont T y|>.comp (continuous_const.prodMk continuous_id)).measurable)),a,hp g⟩,fun g _ x=> hp g x,univ,le_rfl,fun i=> i.recOn (show ‖colors G s‖≤_ from (F.resolves (fun _=>0)).priced ()) (fun j=> mem_univ j), fun g _ hg x hx=> relaxed F O x g hg hx⟩ -- args
omit F hO

section
variable (T s y)
lemma dispatch_warm : ContDiffAt ℝ ω (fun x:C' => line T (flank y (readRay T s x))) 0:= by
 let f:= line T ∘ₗ (flank y); have hx : ContDiffAt ℝ ω (readRay T s) 0:= ( ((EuclideanSpace.proj s:G.Color→L[ℝ]ℝ).contDiff.contDiffAt.comp _ (contDiffAt_apply ℝ _ none _))).prodMk (contDiffAt_pi.mpr (fun i=> axis_hot.comp (f:=fun x:C'=>x (some i)) _ (contDiffAt_apply ℝ _ _ _)))
 exact ( LinearMap.toContinuousLinearMap f ).contDiff.contDiffAt.comp _ hx
lemma stationary_lens : line T (flank y (readRay T s 0))=0:= by rw [show readRay T s 0=0 from Prod.ext rfl (funext fun i=>axis_zero)]; simp
lemma canopy (h:ContDiffAt ℝ ω (Hearth.seed O) 0): ContDiffAt ℝ ω (lens T y s (Hearth.rad T O)) 0:= ((stationary_lens T y s).symm ▸ h).comp (f:=fun x:C'=>line T (flank y (readRay T s x))) _ (dispatch_warm T y s)
end

variable (Y:XSpace.Initialize G)(l:List (Arrival.Folio G)) (s T y)
open Arrival
local notation "Λ"=> Hearth.rad T (Folio.scenario Y n l)
lemma challenged (l:List (Arrival.Folio G))(h:Even n.val): ContDiffAt ℝ ω (Hearth.seed ( Folio.scenario Y n l)) 0:= by
 let f := LinearMap.toContinuousLinearMap ((Pert.Orb.LinkP G n).subtype.comp ( Orbit.fanEquiv (G:=G) h).symm.toLinearMap)
 induction l with
 | nil=> exact contDiffAt_const
 | cons i l ih=>
    let p0:= Folio.placard Y i n; let Y':= p0 ∘ MS.Native.Chart.nation
    refine ContDiffAt.mul (show ContDiffAt ℝ ω (Hearth.seed p0) 0 from ?_) ih; have he:Folio.placard Y i n ∘ Orbit.ignite = Y' ∘ f:= by
       funext x; let k: Pert.Orb.LinkP G n:= (Orbit.fanEquiv (G:=G) h).symm x; change p0 (Orbit.ignite x)=p0 (Pert.Orb.positiveLinks k); rw [← Orbit.lit k,show Orbit.touches G n k=x from (Orbit.fanEquiv h).apply_symm_apply x]
    change ContDiffAt ℝ ω (p0 ∘ Orbit.ignite) 0; unfold p0; rw [he]; exact (((map_zero f).symm ▸ Change.Stencil.crease i.addr (Folio.leaf Y i) : ContDiffAt ℝ ω Y' (f 0)).comp _ f.contDiff.contDiffAt)

lemma charges_ok: Lumen.Zeros (Folio.asset l) (lens T y s Λ):= by
 intro i hi; let ψ:= Hearth.seed (Folio.scenario Y n l); let F₀:Flats G n→ℝ:=0;
 have hv (k:ℕ)(hk:k≤ i): jet ψ k=jet F₀ k:= by
    have he: PowerSeries.coeff k (Stack.rise ψ)=0:= by
       change PowerSeries.coeff k (imprintRoot ( Folio.scenario Y n l )) = _; rw [ ← Hearth.launching Y l L.even,PowerSeries.coeff_X_pow_mul',if_neg (by omega)]
    have hB:PowerSeries.coeff k ( Stack.rise F₀ )=0:= by
       unfold F₀; apply Subtype.ext; ext x; unfold Stack.rise; rw [PowerSeries.coeff_mk]; change jet (0:Flats G n→ℝ) k x=0; simp [jet]
    unfold Stack.rise at *; rw [PowerSeries.coeff_mk] at he hB; exact congr_arg Subtype.val (he.trans hB.symm) -- issue occurs
 let v(x:C'):=line T (flank y (readRay T s x)); let f:=lens T y s Λ; have hr:f=(ψ∘v):=rfl; have h0 : v 0=0:= stationary_lens T y s
 have hA := (dispatch_warm T y s).of_le (m:=i) le_top; -- parameter
 have hw (k:ℕ) : ContDiffAt ℝ ω ψ 0:= challenged Y l L.even
 have he (k:ℕ)(hk:k≤ i): iteratedFDeriv ℝ k ψ 0=iteratedFDeriv ℝ k F₀ 0:= by
    apply Tensor.ext_diag _ _ (Analysis.sym_Jet ((hw k).of_le le_top)) (Analysis.sym_Jet contDiffAt_const)
    funext x; apply mul_left_cancel₀ (a:= ((Nat.factorial k:ℝ)⁻¹)) (by positivity); exact congr_fun (hv k hk) x
 have hG :=Work.G05.jets_comp ( f:=v ) ( f':=v ) hA hA ( show ContDiffAt ℝ i ψ (v 0) from h0.symm ▸ (hw i).of_le le_top ) ( show ContDiffAt ℝ i F₀ (v 0) from contDiffAt_const ) rfl (fun _ _=>rfl) (fun k hk=> h0.symm ▸ he k hk) i le_rfl
 change jet f i = _; unfold jet; rw [hr,hG]; ext x; simp [ Function.comp_def, F₀ ]
end YM.FVA2.Embr
