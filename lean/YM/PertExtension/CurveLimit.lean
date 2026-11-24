import YM.PertExtension.PlaneCovariance
import YM.PertExtension.BlendAsymptotic

/-! Same joint kernel and scope of distinct eigen-mode pair limits. -/
set_option autoImplicit false
set_option maxHeartbeats 980000
namespace YM.PertExtension.LatticePT.Curve
open MeasureTheory Filter Topology Analysis Maxwell Asymptotics Next.Rank Lattice Beamer CellsInt Set Function Finset Next.Rank.Normal
open Configuration LatticePT BlendAsymptotic Screens Air Wall
open scoped BigOperators Classical ContDiff Topology
variable {G : Gauge}{q : ℕ+}{n d:ℕ}(x:Points n)(hx:x∈conf n)(hq:1<q.val) {s:ℕ→Fin n→Cover}(hready:PathReady x q s)
noncomputable section
local notation "reg"=> (atTop:Filter ℕ)
local notation "r" k => (magnify q k)
local notation "KK" k => (jointKernel (G:=G) q (s k) k)
local notation "H" k => lifted d s atAddress (G:=G) (q:=q) k -- abbreviation issue
variable {O : ℕ→Cover}{U : Fin n→ℕ→Cover}(hO:Placement q O)(hU:∀ i,Tendsto (fun k =>epsilon q k • mapZ (U i k)) atTop (𝓝 (x i)))
variable (hs : s=fun t j=>withOrigin O (U j) t)
include hO hU hs hq
lemma home_cost (i : Fin n)(a b:Atom G)(d:ℕ): PolyFlow.rate_as (fun k =>(sliceK (KK k) i).cov a b) ((covarianceSymbol G).cov a b) (fun k =>(r k:ℂ)^d) reg :=by
    have he d:= image_zone hq hO hU a b d i
    have ht:Tendsto (fun t=>(magnify q t:ℝ)^d • ((sliceK (KK t) i).cov a b-(covarianceSymbol G).cov a b)) reg (𝓝 0):= by simpa only [hs] using! he d -- exact defeq
    have ht₀:Tendsto (fun t=>((sliceK (KK t) i).cov a b-(covarianceSymbol G).cov a b)) reg (𝓝 0):=by simpa only [pow_zero,one_smul,hs] using! he 0
    refine ⟨?_,?_⟩
    · convert! ht₀.add (tendsto_const_nhds (x:=(covarianceSymbol G).cov a b)) using 1 <;> simp
    convert! ht using 2
    next t => rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_eq_mul]; exact congr_arg (· * ((sliceK (KK t) i).cov a b-(covarianceSymbol G).cov a b)) (Complex.ofReal_pow (r t) d).symm

include hq hready hx
omit hO hU hs in
lemma cooling (X Y:ℕ→Cover){i j:Fin n}(hgap : Adrift (q:=q) (x:=x) i j X Y)(hij:i≠j)(a b:Address G) :
   Tendsto (fun t=> echo (side q t) (X t) (Y t) a b) reg (𝓝 0) := by
   obtain ⟨r',hr',hw⟩:=hgap.image
   let P(a:Address G):Degree G:=⟨a.2.1,a.2.2,a.1,0,Fin.elim0⟩
   have hL:=price_total (G:=G) (q:=q) (X:=X) (Y:=Y) hq (show (x i-x j)∈away from sub_ne_zero.mpr ((show Injective _ from hx).ne hij)) hgap.gap (P a) (P b) hr' hw
   let D:ℕ→Bridge G:=fun k =>echo (side q k) (X k) (Y k)
   have he k : mourn (gesture (P a)) (gesture (P b)) (D k)=D k a b:=rfl
   have hr := scale_inv hq
   have ht:Tendsto (fun k =>((r k)^4) * (D k a b)) reg (𝓝 (Prayer.gleam (P a) (P b) (x i-x j))) := by
      convert hL using 1; funext k; rw [(he k : mourn _ _ _ = _)]; dsimp only [amount,P];unfold D;ring
   have hh := (hr.pow 4).mul ht
   simp only [zero_pow (show 4≠0 by decide),zero_mul] at hh
   apply hh.congr (fun k =>?_); have hu0:0<r k:= by unfold magnify;exact pow_pos (Nat.cast_pos.mpr q.pos) _
   change (r k)⁻¹^4*((r k)^4* (D k a b))=_; field_simp; rfl
omit hO hU hs in
lemma cross_bound : PolyFlow.Bounded (fun k => onlyCross (KK k)) reg:=by
   intro a b; simp_rw [only_mixed]; split_ifs with h
   · exact ⟨1,Eventually.of_forall fun _=>by simp⟩
   have hAB:=cooling x hx hq hready (fun t=>s t a.1) (fun t=>s t b.1) (hready _ _ h) h (atAddress a.2) (atAddress b.2)
   exact ⟨1,(hAB.norm.eventually $ ge_mem_nhds (by simp : ‖(0:ℝ)‖ < (1:ℝ))).mono fun k hk=> by simpa [jointKernel,Complex.norm_real] using! hk⟩

omit hO hU hs
end
end YM.PertExtension.LatticePT.Curve
