import YM.PertExtension.CurveLimit
import YM.PertExtension.LiftBounds
import YM.PertExtension.VertexSymbol
import YM.PertExtension.Ticked
import YM.PertExtension.MixedRule

/-! Reassemble already-decoupled same-mark and cross Wick contractions. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
noncomputable section
namespace YM.PertExtension.LatticePT.Leading
open Function Set Filter Finset RG Wilson Lattice Labels Source Drops Hue MvPolynomial
open Next.Rank Next.Rank.Beamer Next.Rank.Configuration Heat.Top Bid Heat Next.Rank.LiftMark Normal Next.Rank PolyFlow Maxwell
open LatticePT Mixed BlendAsymptotic Wall CellsInt Screens
open scoped Topology ContDiff Classical BigOperators

variable {G : Gauge}{D n:ℕ}(q : ℕ+)(hq:1<q.val)
variable {O:ℕ→Cover}{U:Fin n→ℕ→Cover}{x : Points n}{S:Type*}
variable (hO : Placement q O)(hx:x∈conf n)(hU:∀ i,Tendsto (fun k=>epsilon q k • mapZ (U i k)) atTop (𝓝 (x i)))
local notation "reg" => (Filter.atTop:Filter ℕ)
abbrev routes (O:ℕ→Cover)(U:Fin n→ℕ→Cover) := fun t j=>Screens.withOrigin O (U j) t
abbrev smear (v:Word G) := Vertex.combination v.S v.H v.sound v.chosen v.axis
abbrev KK (O:ℕ→Cover)(u:Fin n→ℕ→Cover)(t:ℕ) := jointKernel (G:=G) q (routes O u t) t
private lemma cross_struct (s:ℕ→Fin n→Cover)(k): onlyCross (jointKernel (G:=G) q (s k) k) = crossKernel q s k:=by
     ext1; funext a b; rw [only_mixed]
     change _ = (((if a.1=b.1 then (0:Bridge G) else echo (side q k) (s k a.1) (s k b.1)) (atAddress a.2) (atAddress b.2):ℝ):ℂ)
     by_cases a.1=b.1 <;> simp [*,jointKernel]
include hO hx hU hq
set_option backward.isDefEq.respectTransparency false in
lemma top_limit {s:Finset (Fin n)}(w:Fin n→Word G)(hd:∀ i, (w i).d ≤ D) :
   let u0:=fun i=> (rename (Sum.inl:KeyIn G D→KeyIn G D⊕Atom G)) (thawKey (raiseLabel G (hd i) ((w i).F.basis (w i).axis)))
   let p:=fun i=>Vertex.combination _ _ (w i).sound (w i).chosen (w i).axis
   Tendsto (fun t:ℕ=>(magnify q t :ℂ)^(∑ i∈s,(w i).d) * blend (KK (G:=G) q O U t) 0 (pot s p)) reg (𝓝 (blend (currentX hx G D) 0 (pot s (fun i=>thawKey (raiseLabel G (hd i) ((w i).F.basis (w i).axis)))))) := by
   intro u0 p
   let K:=KK (G:=G) q O U
   let u1:=routes O U
   let b := lifted (G:=G) (q:=q) D u1 atAddress
   let u2:=fun t=> features (G:=G) D atAddress (magnify q t)
   let oracle := fun i=>thawKey (raiseLabel G (hd i) ((w i).F.basis (w i).axis))
   let n:= fun i=>(w i).d; let M:=currentX hx G D
   have hm t: 0<magnify q t:=pow_pos (Nat.cast_pos.mpr q.pos) _
   have hr:= ready hq hO hx hU
   have hs(t): onlyCross (K t)= scope (perSlot (fun _=>u2 t)) (b t):=by unfold K KK; rw [cross_struct]; unfold crossKernel b u2 lifted; rw [shaped]; exact hm t
   change Tendsto _ _ (𝓝 (blend M 0 (pot s oracle)))
   have h1 (i)(hi:i∈s) : Limit (fun k=>((magnify q k :ℂ)^(w i).d) • Normal.exchange (u2 k) (milk (covarianceSymbol G) (p i))) (u0 i) reg:= by
       have he:=Vertex.priced (G:=G) _ _ (w i).sound (w i).chosen (w i).axis (hd i)
       let d:=(w i).d ; let basis:= ((w i).F.basis (w i).axis); let a:=(w i).F.grades (w i).axis
       have pureD : (basis.val).IsWeightedHomogeneous bidegree (d,a.2) :=by rw [show (d,a.2)=a from Prod.ext (w i).weight.symm rfl]; exact (pure_grade a basis).1 ((w i).F.pure _)
       have hsize:= tendsto_pow_atTop_atTop_of_one_lt (α:=ℝ) (r:=(q:ℝ)) ?hle
       case hle => exact_mod_cast hq
       unfold u2
       have he:=Ticked.earns (f:=atAddress) (show Tendsto (magnify q) reg atTop from hsize) (hd i) pureD he
       convert! he using 1
       funext t; symm;rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact congr_arg (· • _) (Complex.ofReal_pow ..)
   refine BlendAsymptotic.accumulate (s:=s) (r:=magnify q) (H:=b) (u:=u2) (K:=K) (covarianceSymbol G) p n ?_ ?_ _ oracle M hs ?_ h1 ?_
   · exact Curve.home_cost x hq hO hU (s:=u1) rfl
   · exact Curve.cross_bound x hx hq hr
   · exact LatticePT.any_lift_bound hx hq u1 hr
   exact any_lift_low hx hq u1 hr

end YM.PertExtension.LatticePT.Leading
