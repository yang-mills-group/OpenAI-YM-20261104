import YM.SignedWilsonExpansion.F9.Shovel
/-! # Complete docket and its realization, including all ℂ-linear combinations. -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b N M i j l r d p u n :ℕ}
variable {B Q D Z X Y η t a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
variable {F:Frames G}{H:Hol G}{A':∀ h, Survey G H h}{K:∀ h,Rays G h H}
local notation "Rι"=> (F.level h)
namespace MergeTrip
open Stair Tape Cirrus
open Normalize (Sec)
open SignedWilsonExpansion.Commission.Method SignedWilsonExpansion.Commission.Method.Epic
variable (W':Initialize G){Ki:∀ h,Rays G h W'.hol}{Ω:Council F}
local notation "Rθ"=> (F.level h)
local notation "A0" => R.draws
variable (Q':MergeTrip Ω (launch F W'.hol W'.surveys Ki k) R.draws R.paid m b v c c h e k u X)
section lanes
variable (S:SectionData (F.level d))(Y:Normalize.Store G)(x:Mesh)(f:(F.level d).Coeff)
lemma vote_boost (i:(F.level d).Index): Q'.snapD W' S Y x l r ρ (Pi.single i 1)= Q'.shapeD W' S Y x i l r ρ:= by unfold snapD; simp only [LinearMap.coe_mk,AddHom.coe_mk, Pi.single_apply,ite_smul,zero_smul, one_smul]; simp
lemma snap_star : ∀ k, Q'.snapD W' S Y x l r ρ (star f) k=Normalize.reel h (Q'.snapD W' S Y x l r ρ f k):=by
   intro k; unfold snapD; simp only [LinearMap.coe_mk,AddHom.coe_mk,Finset.sum_apply,map_sum,Pi.smul_apply,(Normalize.reel h).map_smulₛₗ]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [Q'.shape_real W' S Y x i]; rfl
variable {P':Hol G} (hS:S.Sound P')(p0:Bid.pop S)(v₀:d≤h)
include hS p0 v₀
lemma snap_spin (s:Signed) : Q'.snapD W' S Y x l r ρ ((F.level d).act s.ortho f)= Tape.layer (Normalize.ori s.ortho h) (Q'.snapD W' S Y x l r ρ f):=by
    let F':= F.level d; let q:= realM F' s; have ht (x:F'.Coeff): x=∑ j,x j • Pi.single j 1:=by ext1 j; simp [Pi.single_apply]
    let R:=Q'.snapD W' S Y x l r ρ; let T:= (F.level d).act s.ortho
    have hv (i:F'.Index): R (T (Pi.single i 1))= Tape.layer (Normalize.ori s.ortho h) (R (Pi.single i 1)):=by
       rw [ht (T _), map_sum]; unfold R; simp_rw [map_smul]; rw [Q'.vote_boost W']; simp_rw [vote_boost]; rw [Q'.shape_spin W' S Y x hS p0 v₀]; exact Finset.sum_congr rfl (fun j _=> congr_arg (fun c:ℂ=> c • _) (bleach_even _ _ j i))
    change R (T f)=Tape.layer (Normalize.ori s.ortho h) (R f); rw [ht f]; simp_rw [map_sum,map_smul,hv]
omit v₀ in
lemma snap_leaf : Q'.snapD W' S Y x l r ρ ((F.level d).e0) = Tape.side (Normalize.leaf G h) 1:=by rw [Frame.e0,Q'.vote_boost,Q'.shape_unit W' S Y x hS p0]
end lanes
section catalog
open Looms
variable (d':Fin (n+1)→ℕ) (U':∀ i:Fin (n+1),SectionData (F.level (d' i)))(x:Sample (n+1))
variable (P0:(i:Fin (n+1))→(F.level (d' i)).Coeff)
local notation "δ"=> sizeT R.draws ρ
variable {W₁:Credit}
abbrev probeMany (A: Levels G)(Ñ:ChartRatio G)(N k r v:ℕ)(y:Fin (n+1)→ Cover)(f:(i:Fin (n+1))→(F.level (d' i)).Index) := FadeRaw A Ñ N ((n+1)*k) r v (embark (fun i=> literal (U' i) (f i)) y)
def dockD (A:Levels G)(Ñ:ChartRatio G)(N k r v:ℕ)(y:Fin (n+1)→ Cover): InkQ:= ∑ f:(i:Fin (n+1))→(F.level (d' i)).Index, (∏ i:Fin (n+1), P0 i (f i)) • insertQ (probeMany d' U' A Ñ N k r v y f)
noncomputable abbrev dockL (T:Tape.Table (Sec G h) (n+1))(x:Mesh)(Z:InkQ)(Vn:Normalize.Store G) (l r:ℕ)(ρ:ℝ): InkQ:= tabular (composed T Z) (fun i:Fin (n+1)=> Q'.snapD W' (U' i) Vn x l r ρ (P0 i))
-- comparison includes coefficient powers and each signed f-stencil externally exactly
variable (Vn:Normalize.Store G)(Kn:Rose.Pick Vn)
theorem paidDock (Y:ℝ)(s:ℕ→ Cover)(w:ℕ→ Fin (n+1)→ Cover)(Wt:ℕ) (τ:ℝ)(xP:Budget (c:=c) x s (w c)) (M:Regard (W'.tree x.F.p) R l c s F W'.surveys Ki h k (w c) Y)(Ve:Vn.Meets W' x.F h)(Vm:Rose.Use W' Kn x.F)(g:Dormitory R ((n+1)*k) 0 U)(g':Dormitory R k u W₁)(V':SpringD R ((n+1)*k) 0 u V) (T':Canopy R l c X) (L:l≤b) (tv:l≤r)(y:r≤v)(z:c≤N)(hρ:0<ρ)(ht:0<t)(hp:(n+1)*h≤u)(hc:δ v≤1)(Wn:Cowrie R.draws b c w (SpanR R.draws ρ t)) (a:Fin (n+1)→ℝ)(hf:∀ (i:Fin (n+1))(j:(F.level (d' i)).Index), Respect k e u 1 ( literal (U' i) j) (a i)) :
    let D:= (Ethos W'.surveys Ki F Ω h k e u n E).buy X*((δ c)^((n+1)*h))⁻¹*(∏ i,a i)*Y+(finish W'.hol F Ω k h e u n t E U W₁ V).buy X*((δ b)^u+(paceT R.draws.S b v)^h+(R.tempC r v+R.tempC v c))*(∏ i,a i)
    let T:= Q'.dockL W' d' U' P0 (numeral W' Kn x h) x.F (recallH W' Kn R.draws R.paid c l r x.F) Vn l r ρ
    FitsZ e (T- dockD d' U' P0 R.draws R.paid N k r v (w v)) ((∑ f:(i:Fin (n+1))→(F.level (d' i)).Index, ‖∏ i:Fin (n+1),P0 i (f i)‖)*D):=by
    intro D; let Z:=Tape.composed (numeral W' Kn x h) (recallH W' Kn R.draws R.paid c l r x.F); let atF(f:(i:Fin (n+1))→(F.level (d' i)).Index):= insertQ (probeMany d' U' R.draws R.paid N k r v (w v) f); let A (f:(i:Fin (n+1))→(F.level (d' i)).Index):=Tape.tabular Z (fun i=> Q'.shapeD W' (U' i) Vn x.F (f i) l r ρ)
    have hK f: FitsZ e (A f-atF f) D:=by
        unfold A; simp_rw [← Q'.shape_alpha W']; exact Of.hearing W' Kn Q' x l r Y s w xP M Ve Vm g g' V' T' L tv y z hρ t ht hp hc (fun i=> literal (U' i) (f i)) a Wn (fun i=>hf i _)
    dsimp only [dockL,snapD,LinearMap.coe_mk, AddHom.coe_mk,dockD]; rw [MultilinearMap.map_sum, ← Finset.sum_sub_distrib]; simp_rw [MultilinearMap.map_smul_univ, ← smul_sub]; rw [ Finset.sum_mul]; exact FitsZ.stack _ _ _ (fun i _=> (hK i).price_div _)
end catalog
end MergeTrip
end YM.WilsonCoeffUV.Mer.Xa
