import YM.FVA2.Embr.Yards
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
/-!
# Realizing the stipulated Fk data for the inversion epoch

E.g., can ask for coefficients at arbitrary finite orders at each given finite regulator,
use each finite $V$ budget (including powers removed), and compare to these `Steady`
structures from exactly the `Cloth` under evaluation. See `Embr/Provider.lean`.

Without estimates on obtaining those data on every sequence of such geometries. These
results don't rely on enumerating some growing set of local cases as part of an error
estimate; just use a fixed `Habitat`, built from this very epoch.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Embr
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Finset MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade Hearth Hearth.Clan RGComparison.Core16 Lumen Fk Forge
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {L:Fabric G n} (T:Cloth L)(w:L.Accounts→ℝ→ℝ)

section
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
-- same cutoff trick as their Parcel/Oven
private lemma extendSmooth (f:E→ℝ)(h:ContDiffAt ℝ ω f 0): ∃ g:E→ℝ,g=ᶠ[𝓝 0] f ∧ ContDiff ℝ ∞ g:= by
 let A:= {x:E| ContDiffAt ℝ ω f x}; obtain ⟨b,hb,_,hB,_,he⟩:= exists_contDiff_tsupport_subset (n:=⊤) (show A∈𝓝 0 from h.eventually (by simp)); let u: ContDiffBump (1:ℝ):= ⟨1/4,1/2,by norm_num,by norm_num⟩
 refine ⟨fun x=> u (b x)*f x,?_,contDiff_iff_contDiffAt.mpr (fun x=> ?_)⟩
 · filter_upwards [hB.continuous.continuousAt.eventually (show closedBall (1:ℝ) (1/4) ∈ 𝓝 (b 0) by rw [he]; exact closedBall_mem_nhds _ (by norm_num))] with x hx; rw [show u (b x)=1 from u.one_of_mem_closedBall hx,one_mul]
 by_cases hx:x∈A
 · exact (((u.contDiff (n:=⊤)).comp hB).contDiffAt.mul ((show ContDiffAt ℝ ω f x from hx).of_le le_top))
 refine (contDiffAt_const (x:=x) (c:=(0:ℝ))).congr_of_eventuallyEq ?_
 filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (show x∉ tsupport b from fun he=>hx (hb he))] with y hy; change b y=0 at hy; rw [hy,show u (0:ℝ)=0 from u.zero_of_le_dist (by norm_num [u,Real.dist_eq]),zero_mul]
end

variable (y:Flats G (Bottom L))(s:G.ColorIndex)
local notation "Δ"=> Lumen.Point G (Warm T)
local notation "X"=> (Warm T→G.El)
set_option quotPrecheck false
local notation "Θ"=> ((Hearth.primeBook T y s w).U ()) -- true front at lift
local notation "P"=> Hearth.localClimate T y s w
lemma heard (a:Δ) : Θ a= (Facade.raise (Facade.rate T) w y) (Hearth.readRay T s (fun i=>i.elim a.1 a.2))- (a.1 s)^2 := by
   rw [truePrice]; change front _ _ _ _ _= (a.1 s)^2+front T w y (a.1 s) (fun i=> launch (a.2 i))- (a.1 s)^2; rw [add_comm,add_sub_cancel_right]
variable {Y₀ : L.Accounts→PowerSeries ℝ}{p:ℕ} (h:∀ i,0<term (Y₀ i) 0)(hp:∀i,Through p (amount (w i)) (Y₀ i))(H:∀i,ContDiffAt ℝ ω (w i) 0)
include H
lemma heatBorn : ContDiffAt ℝ ω Θ 0:= by
 rw [show Θ=_ from funext (heard T w y s)]
 let j:= (EuclideanSpace.proj s:G.Color→L[ℝ] ℝ); let f(a:Δ):=(j a.1,fun i=> Lumen.axis.symm (a.2 i)); have he : f 0=0:= Prod.ext (map_zero j) (funext fun i=> Lumen.axis_zero)
 have hq: ContDiffAt ℝ ω (fun x:Δ => j x.1) 0:= j.contDiff.contDiffAt.comp _ contDiffAt_fst
 exact (((he.symm ▸ Facade.hotter_all (Facade.rate T) w y (Facade.tasty T) H)).comp (f:=f) _ (hq.prodMk (contDiffAt_pi.mpr (fun i=> axis_hot.comp (f:=fun x:Δ => x.2 i) _ ((contDiff_apply ℝ _ _).contDiffAt.comp _ contDiffAt_snd))))).sub (hq.pow 2)

include h hp
lemma born : IsLocalMin Θ 0:= by
   let j:= (EuclideanSpace.proj s:G.Color→L[ℝ] ℝ); have hv : Tendsto (fun x:Δ=>j x.1) (𝓝 0) (𝓝 0):= ((j.continuous.comp continuous_fst).tendsto _)
   filter_upwards [hv.eventually (eventually_all.mpr (fun i=> (H i).continuousAt.eventually (eventually_gt_nhds (zeroWeight w Y₀ h p hp i))))] with x hx
   change Θ 0≤ _; rw [heard]; change Facade.raise (Facade.rate T) w y (0,(fun _=> Lumen.axis.symm 0))-(0:ℝ)^2≤Θ x; rw [show (fun _:Warm T=> @Lumen.axis G|>.symm 0)= 0 from funext fun _=>axis_zero, (show Facade.raise (Facade.rate T) w y ((0:ℝ),(0:Facade.Panel T))=0 from (Facade.steep T Y₀ h w y H p hp).base0), zero_pow (by decide), sub_zero]; exact L.nonneg_cost hx _

variable (Ω:Shelf G Unit (Warm T))(j:Warm T→Site n)
def home : Planet Ω n (Warm T) Unit (Clan L):= {
 loc:=j, root:=0, meter:= fun v k x=> poll L (committed T y v x) k, cost r t x _:= desk T w y r t x, glyph:= id, stem:=fun _=> some, ray:= fun _=>colors G s }
local notation "K"=> home T w y s Ω j
variable {w y s T j Ω}
omit h hp H
lemma reportage (r:ℝ)(U:X):
 (K).bureau r U = Real.exp (- (w none r / r^2 * wilson (L.principal (committed T y r U)))) *
   (L.thermostat (fun i=> w (some i) r/r^2)* Hearth.worlds L (fun i=> w (some i) r /r^2) (committed T y r U)):= by refine Eq.trans ?_ (tribute L (fun i=> w i r / r^2) _); change (∑ i:Clan L,poll _ _ i * Base.cash _ _ _ _) =_; refine Finset.sum_congr rfl fun i _=> congr_arg₂ _ rfl ?_; unfold Base.cash Base.action; erw [Fintype.sum_unique]; unfold home desk Planet.F; dsimp only; rw [neg_div, Embr.squares]
-- horizon independent probes & their gauges remain in same climate

open Push.AbsoluteSums.Animals
lemma breadth (n:Side) : ∃ b:ℕ,∀ (x y:Site n),separation x y≤b:= by obtain ⟨b,hb⟩:= (Set.finite_range (fun p:Site n×Site n=> separation p.1 p.2)).bddAbove; exact ⟨b,fun x y=>hb ⟨(x,y),rfl⟩⟩
variable {b:ℕ}(hb:∀x y:Site n,separation x y≤b)
include hb
lemma stars {ι:Type}[Fintype ι](j:ι→Site n)(x)(d:ℕ)(h:b≤d): neighborsOf j d x=univ:= eq_univ_of_forall fun i=>(Forge.member ..).2 ((hb _ (j i)).trans h)
lemma adheres {g:ℝ}(η:Ω.sector.b=b)(hK:Fintype.card (Warm T) ≤ Ω.sector.K) (hA:∀ i x,0≤ desk T w y g i x)(h:∀ t,Adhere T w y t Ω.sector.D g): ((K).F g).Admits Ω.sector g:= by
 refine ⟨fun x i=> steady_vote L _ i,fun x=> total L _,fun t=> (flexible L t).comp ((committed_cont T y|>.comp (continuous_const.prodMk continuous_id)).measurable),fun x t _=> hA t x, fun t _=> (Embr.spends_meas L (fun i=> w i g) t).comp ((committed_cont T y|>.comp (continuous_const.prodMk continuous_id)).measurable),fun x=> (card_le_univ _).trans hK, fun x=> (card_le_univ _).trans (by simp; exact Ω.sector.K_pos), ?_, ?_,?_⟩
 · intro x t i _; rw [stars hb _ _ Ω.sector.b η.symm.le, Fintype.sum_unique]; exact (h t).tiny x i
 · intro x t _ _; rw [stars hb _ _ _ η.symm.le]; exact (h t).suite x
 let P0(t:ℝ)(_ : t=g) a k:= poll L (committed T y g a) k
 intro x u v n' _; refine ⟨fun k t=> P0 g rfl u k* P0 g rfl v t, ⟨fun i j=>mul_nonneg (steady_vote ..) (steady_vote ..),fun i=>?_,fun i=>?_⟩, fun i j q a hx=> False.elim ?_⟩
 · rw [←mul_sum,show ∑ i, P0 g rfl v i=1 from total L _,mul_one]; rfl
 · rw [←sum_mul,show ∑ i, P0 g rfl u i=1 from total L _,one_mul]; rfl
 rw [stars hb _ _ _ (by rw [η]; omega)] at hx; exact hx (mem_univ _)
omit hb

include h hp H
variable (T w y s)
structure Habitat (Ω:Shelf G Unit (Warm T)):Prop where
 resolves (j:Warm T→Site n) : (home T w y s Ω j).Steady
 exactness a : ∀ x:Δ,x∈closedBall 0 Ω.R→ Ω.U a x=Θ x

set_option maxRecDepth 4000 in
set_option maxHeartbeats 300000 in
lemma enroll : ∃ Ω, Habitat T w y s Ω:= by
 -- constructor from true local wet Shelf & sup norms
 obtain ⟨f,hf,F⟩:= extendSmooth Θ (heatBorn T w y s H)
 obtain ⟨r,hr,Lift⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (hf.and (((heatBorn T w y s H).congr_of_eventuallyEq hf).eventually (by simp)))
 obtain ⟨e,he,Rest⟩:= crisp_nbhd (@leaving G)
 let D:= ℝ×X
 have hD: ∀ᶠ x in 𝓝 ((0:ℝ),(1:X)),∀ t: Clan L, desk T w y x.1 t x.2=front T w y x.1 x.2 ∧ poll L (committed T y x.1 x.2) t=poll L 1 t:=by
    filter_upwards [(hotlinks T y).eventually ((impression L).and (level_money L))] with i hi t using ⟨hi.1 _ _, hi.2 _⟩
 obtain ⟨d,hd,Q⟩:= shine T hD
 obtain ⟨A,hA,V⟩:= admissible T w y h hp H
 obtain ⟨q,hq,M⟩:= Metric.nhds_basis_closedBall.mem_iff.mp (V.and (Q.and (starts T w y h hp H)))
 obtain ⟨b,B⟩:= breadth n
 let δ:= min (min e d) (r/2); have hδ:0<δ:= lt_min (lt_min he hd) (by linarith); have he':δ≤e:=(min_le_left ..).trans (min_le_left ..); have hd':δ≤d:=(min_le_left ..).trans (min_le_right ..); have hr': δ<r:= (min_le_right ..).trans_lt (by linarith)
 let β:=min q (r/2); let Ω:Shelf G Unit (Warm T):=⟨ ⟨b,Fintype.card (Warm T)+1,A,by omega,hA⟩,fun _=>f,r,δ,β,1⟩
 have hot {g:ℝ}(hg:Planet.amen Ω g): g∈ closedBall (0:ℝ) q:= mem_closedBall_zero_iff.mpr (by rw [Real.norm_of_nonneg hg.1]; exact hg.2.trans (min_le_left ..))
 have exactness a x (hx:x∈closedBall 0 Ω.R):Ω.U a x=Θ x:= (Lift hx).1
 refine ⟨ Ω,fun j=>?_,exactness⟩; let P1:= home T w y s Ω j
 have area (i:Unit): P1.soil i=univ:= stars B _ _ _ le_rfl
 have K0 : Lumen.Good Ω:= {
    positive:= hr
    extent:=⟨hδ,hr'⟩
    thick:=⟨one_pos,lt_min hq (half_pos hr),show β*1<r from (mul_one β).trans_lt ((min_le_right ..).trans_lt (by linarith))⟩
    reenter u hv:= Rest _ (hv.trans_le he')
    payment a x hx := (Lift hx).2
    smooth _:=F
    zeroth _:=hf.self_of_nhds.trans (by rw [heard]; change Facade.raise (Facade.rate T) w y (0,(fun _=> Lumen.axis.symm 0))-(0:ℝ)^2=0; rw [show (fun _:Warm T=> @Lumen.axis G|>.symm 0)= 0 from funext fun _=>axis_zero, (show Facade.raise (Facade.rate T) w y ((0:ℝ),(0:Facade.Panel T))=0 from (Facade.steep T Y₀ h w y H p hp).base0), zero_pow (by decide), sub_zero] ) -- fix
    first _ := by
       apply HasFDerivAt.congr_of_eventuallyEq _ hf; rw [← (born T w y s h hp H).fderiv_eq_zero]; exact ((heatBorn T w y s H).differentiableAt (by simp)).hasFDerivAt
 }
 have hray : ‖colors G s‖=(1:ℝ):= by exact OrthonormalBasis.orthonormal (EuclideanSpace.basisFun G.ColorIndex ℝ) |>.1 s -- possibly simp
 have hi(k:Warm T): P1.heat k=univ:= stars B _ _ _ (show b≤ 2*b by omega)
 refine {
   prices:=K0, tickets:=fun g hg=> adheres B rfl (Nat.le_add_right ..) (fun k x=> (M (hot hg)).2.2 x k) (M (hot hg)).1, priced:=fun _=>hray.le, thread:=fun a i t _=> area a ▸ mem_univ t,
   warm:=?_, pay:=?_, outside:=?_ }
 · intro g hg i x x' _ hv hv' a
   have ht(x:X)(hx:Planet.crisp Ω.δ (P1.heat i) x): P1.meter g a x=poll L 1 a:= ( (M (hot hg)).2.1 x (Planet.crisp_negligible _ _ hd' (hi i ▸ le_refl _) hx) a).2
   exact (ht x hv).trans (ht x' hv').symm
 · intro g hg a x t hx; change Planet.crisp Ω.δ (P1.soil _) x at hx; rw [area a] at hx
   let E:Δ:=P1.load a g x
   have he₀ : E.1 s=g:= Hearth.xseat ..
   have heu : launch ∘ E.2=x:= funext fun i=> K0.reenter _ (hx i (mem_univ i))
   have he:E∈ closedBall 0 Ω.R:= by
      refine mem_closedBall_zero_iff.mpr (max_le (b:=‖E.2‖) ?_ ?_) 
      · change ‖g • colors G s‖≤_; rw [norm_smul,hray, Real.norm_of_nonneg hg.1,mul_one]; exact hg.2.trans ((min_le_right ..).trans (half_le_self hr.le))
      · apply (pi_norm_le_iff_of_nonneg K0.positive.le).mpr; intro i; exact (G.curvature_norm _).trans (lt_trans (hx i (mem_univ i)) hr').le
   change desk T w y g t x=Ω.U _ E; rw [exactness _ E he]; refine Eq.trans ( ( (M (hot hg)).2.1 x (Planet.crisp_negligible _ _ hd' (le_refl _) hx) t).1 ) ?_; change front T w y g x= front T w y (E.1 s) (launch∘ E.2); rw [heu,he₀]
 · intro g _ a x y t h; exact congr_arg (P1.cost g t · a) (funext (fun i=> h i (area a ▸ mem_univ i)))
end YM.FVA2.Embr
