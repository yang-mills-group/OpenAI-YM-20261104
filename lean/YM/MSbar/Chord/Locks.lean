import YM.MSbar.Chord.Intact
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter
open Lattice Wilson Gauge Work.F03 Push Push.Uniform RG Precision Exterior MSbar.Rolling MSbar.Wave Cacao
open MeasureTheory Set Bakery
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f: Side}{n:ℕ}
open MvPolynomial
local notation "X"=>Positions (Primary c G)
local notation "µ"=> PowerSeries.coeff
lemma born (c:Side)(e:G.Color) (i:ℕ): caliper c e (PowerSeries.coeff i (opening G c))=0:=by
    let P:= µ i (opening G c); let Y(x:Positions (Primary c G)):= eval x P
    suffices hp: rim Y=0 by change stackH c e (rim Y)=0; rw [hp,map_zero]
    have ht:ContDiffAt ℝ 2 Y 0:= (vent ..).contDiffAt.of_le le_top
    by_cases he:i=0
    · have hh : P=0 :=by unfold P; rw [opening, map_neg,he, splitK,neg_zero]
      ext1 x; ext1 y; unfold rim Y; simp [hh]
    have hp: P= -(potter (widthV G c) (i+2)):=by unfold P opening; rw [map_neg,splitV,map_sub,PowerSeries.coeff_C_of_ne_zero he,sub_zero,singularity,PowerSeries.coeff_mk] -- remove unused binder
    have hh(x:Positions (Primary c G)): Tendsto (fun t:ℝ=>Y (t•x)/t^2) (𝓝[≠] 0) (𝓝 (0:ℝ)):=by
        have H(x):Y x= -Tensor.diagonal (Tensor.coeff (widthV G c) (i+2) 0) x:=by unfold Y; rw [hp,_root_.map_neg,pots]
        let A:=Y x; have hV:Tendsto (fun t:ℝ=>t^i) (𝓝[≠] 0) (𝓝 0):= by simpa [he] using ((show Tendsto id (𝓝[≠] (0:ℝ)) _ from tendsto_id (x:=𝓝 (0:ℝ))|>.mono_left nhdsWithin_le_nhds).pow i)
        have ht:= hV.mul_const A; rw [zero_mul] at ht; refine ht.congr' ?_; filter_upwards [show ∀ᶠ t:ℝ in 𝓝[≠] (0:ℝ),t≠0 from self_mem_nhdsWithin] with t hv; unfold A; rw [H, H,Tensor.homogeneous,pow_add]; rw [smul_eq_mul]; field_simp
    have ht(x y:Positions (Primary c G)):rim Y x y=0:= by apply Eq.trans (show rim Y x y=iteratedFDeriv ℝ 2 _ 0 ![x,y] from (iteratedFDeriv_two_apply Y 0 ![x,y]).symm); exact hessian_polar ht (Q:=fun x y=>0) (by simp) (fun _ _=>rfl) (fun x=> (tendQ Y ht _ hh).2.2 x |>.trans (mul_zero _)) _ _
    exact ContinuousLinearMap.ext fun x=>ContinuousLinearMap.ext fun y=> ht ..
-- h target chain finite periods.Layout Work uses covariance K singular.Emp.Exp with B parameters η.D.FCost stamps. Choice uniform statement.Once boots. through active scales m..N fixed order.
variable {L:Levels G}{H:Horizon L}{A:ChartRatio G}{Y: Supply.Sheet G}{W: Supply.Rolls Y}(K:Kin H A)(T:PostCost W)(J:ℕ)
variable (i:ℕ)(p:ℕ)
local notation "κ"=> Kin.path
local notation "v!" j=>L.S.side j i
-- Use partial queue; all periods parameters frozen. Derivative.Work. ratio e!
structure Scene (L : Levels G)(i p :ℕ) where
    Poly(j:ℕ) : Nesting G (L.S.side j i) -- implicit G align.Levels
    film(j:ℕ) : ℝ → Config G (L.S.side j i) → ℝ
    action (j:ℕ): PowerSeries ℝ
structure Realized (K:Kin H A)(J i m p:ℕ)(e:G.Color)(F:Scene L i p) :Prop where
    cap : m≤J
    top0 : F.film J= breed G (L.S.side J i)
    opening : F.Poly J=Rolling.opening G (L.S.side J i)
    budget (j:ℕ)(he:j≤J)(hg:m≤j): Trend (F.film j) (F.Poly j) (K.path J j) (L.params j).clip p ∧ Keeps (F.Poly j) p e
    step (j:ℕ)(he:j < J)(hv:m≤j): let S:= L.clock.op j i
                                 ∃ (B:Tree.Forest S.ratio) (x:S.Choices), let b:=F.action j; let P:=K.path J j; let Q:=K.path J (j+1); let v:=(L.params j).clip; PowerSeries.coeff 0 b=1 ∧ F.film j=(shunt S (F.film (j+1)) ∘ tiltMap b p)∧
                                    F.Poly j=bley b (colorCut B x Q (L.params (j+1)).clip A (F.Poly (j+1)) (K.stationary J j i B)) (ink (L.S.side j i) v P)
-- Calendar.T assumes.L.I. Need dealer.N.Asset. Stage after; quantities enough.Take all Forest.PortWhy
variable (hv : K.Planned T) (e:G.Color)(he:‖e‖=1)(hA : LocalRatio A)
structure Light (L: Levels G) (H:Horizon L)(F : MapPrices) :Prop where
    paid : H.Suffices F
    sector (m p:ℕ) : Bid.Larger (L.clock.op m p) (G:=G)
-- Eligibility in actual.P.Shape. Budget.View
variable (hQ:∀ j, j < J→ n≤ j → let c:=L.params j; let S':= L.clock.op j i; Bid.Larger S' (G:=G)∧∃ v:ℕ,10*(v+4)<(L.S.side j i).val∧ Fintype.card PlaqAxes*(c.paths*c.paths*url (L.S.side j i) v c.width) ≤ 1)
include hv he hQ hA
lemma freezes (ht:n≤J) :∃ F:Scene L i p, Realized K J i n p e F :=by
    induction ht using Nat.decreasingInduction with
    | self=>
       let F : Scene L i p:=⟨fun _=> Rolling.opening G _,fun _=>breed G _,fun _=>1⟩
       have hs:Trend (F.film J) (F.Poly J) (K.path J J) (L.params J).clip p:=sprout _ _ (fun j hi=> let h:=hv.peak J i j (by omega); ⟨h.2.1,h.1,h.2.2.symm⟩) p
       refine ⟨F,le_rfl,rfl,rfl,fun j hj hh=> le_antisymm hj hh |>.symm ▸ ⟨hs,⟨fun i _=>born _ e _,hs.plane⟩⟩,fun j hj hk=> (not_lt.mpr hk hj).elim⟩
    | of_succ m hm ih=>
       obtain ⟨F,hF⟩:=ih (fun j he hj=> hQ j he (by omega)); let a:= L.clock; let V:=a.op m i; obtain ⟨hg, v,hw,hz⟩:= hQ m hm le_rfl; have hS : Serves V G:=⟨hg.1,(L.blocks m i).symmetric,(L.blocks m i).gauge,hg⟩
       let B:= Classical.choice (Tree.select V.ratio V.patch.odd_side); let j:=Classical.arbitrary V.Choices
       let P:= K.path J m; let Q:=K.path J (m+1); let C:=(L.params m).clip; let C':=(L.params (m+1)).clip; let g:=F.Poly (m+1); let k:= K.stationary J m i B
       have hf: Trend (F.film (m+1)) g Q C' p:= hF.budget (m+1) hm le_rfl|>.1; have hK:Matrix.PosDef (Push.Uniform.block (priced B j C' Q) 0):= blueprint B j Q C' hg.1 hf.quiet (T.price _) (hv.gap J m i hm B); obtain ⟨T',P',ht,hp',ht',hτ⟩:= prices P C p v B Q C' j e g k A he hf hS ((hv.critical J m i hm B).1) (hv.classicalPart J m i hm B) hK (hv.cap J m hm.le) hA hw hz -- order
       let W:=shunt V (F.film (m+1)) ∘ tiltMap T' p; let H: Scene L i p :=⟨update F.Poly m P',update F.film m W,update F.action m T'⟩; have hc:P'=H.Poly m:= (update_self m P' F.Poly).symm; have hx:W=H.film m:= (update_self m W F.film).symm; have hT:T'= H.action m:= (update_self m T' F.action).symm; have hp(i:ℕ)(hi:m < i): H.Poly i=F.Poly i ∧ H.film i=F.film i∧H.action i=F.action i:= ⟨update_of_ne hi.ne' P' F.Poly, update_of_ne hi.ne' W F.film, update_of_ne hi.ne' T' F.action⟩
       refine ⟨H, ⟨hm.le, (hp J hm|>.2.1).trans hF.top0,(hp J hm|>.1).trans hF.opening,fun j hj hh=>?_,fun r hr hs=>?_⟩⟩
       · by_cases he:j=m; rw [he, ←hc,←hx]; exact ⟨hτ,ht'⟩
         rw [hp j (by omega)|>.1,hp j (by omega)|>.2.1]; exact hF.budget j hj (by omega)
       by_cases he:r=m
       · subst r; refine ⟨B,j,hT ▸ hp',?_,?_⟩; rw [← hx,hp (m+1) (by omega)|>.2.1,← hT]; rw [← hc,hp (m+1) (by omega)|>.1,← hT]; exact ht
       obtain ⟨α,Y,hβ,hξ,hψ⟩:= hF.step r hr (by omega); have h:= hp r (by omega); have h':=hp (r+1) (by omega); refine ⟨α,Y,h.2.2 ▸ hβ,?_,?_⟩; rw [h.2.1,h.2.2,h'.2.1];exact hξ; rw [h.1,h.2.2,h'.1]; exact hψ
end YM.MSbar.Midpoint
