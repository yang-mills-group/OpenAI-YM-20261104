import YM.MS.Plum.Ripe
/-!
# Terrain continuity of oceania and trees

Proving full z `<Town>` preservation and cost from Compact approximators. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plum
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans
open Momentum Metric
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{U V: Rip G}{m n:ℕ}{K:Shade G}{b c:Bool}
variable {F H: Mob G}{X Y:ℕ→ Mob G}{Z:ℕ→Rip G}
variable (h:Drift b X F)(hv:From b Z U){s:ℂ}(hs:s∈Town)
include h hv hs
lemma carries : fell 0 fade fun i=>ocean s (Z i) (X i)-ocean s U F:= by
    obtain ⟨n,hn⟩:= exists_nat_ge (2*s.re+1); have ht : ∀ n:ℕ, scaleC 0 1 (fun _:ℕ => ‖2*(s-n)‖):= fun n=>const_sc ..
    have he: ∀ i:ℕ,ocean s (Z i) (X i)-ocean s U F=ocean s (Z i) (X i-F)+ocean s (Z i-U) F:= fun i=>core_difference (hv.go i) (h.ticket i) hv.price h.real hs
    simp_rw [he]; refine fall_add ?_ ?_
    · convert regular_fin ht (b:=fun _:ℕ=>1) h.grey hv.haze (fun _=>hs) (fun _=>hn) (fun i=>((h.ticket i).sub h.real).token) (fun i=>(hv.go i).token) (fun _=>zero_le_one) using 1; simp
    convert regular_fin ht (f:=fun _:ℕ=>F) (travel h.real.price) hv.ops (fun _=>hs) (fun _=>hn) (fun _=>h.real.token) (fun i=>((hv.go i).sub hv.price).token) (fun i=> (being i).le) using 1; simp
omit h hv in
lemma torn (hf:Form0 b F)(hu:Knot b U): Form0 b (ocean s U F):= by
   obtain ⟨n,hn⟩:= exists_nat_ge (2*s.re+1);
   have he := newer hu; have ht (i:ℕ) :=tried hu (fade i) (being i) (sold i)
   let Q(i:ℕ):=ocean s (twine (fade i) U) F; let L:= ocean s U F; have hx (i): Sturdy b (Q i):=((ht i).volume0 hf.sync).vote s hs
   have hy (n:ℕ)(l:Legs (Shore G n)) : Tendsto (fun i=> Q i n l) atTop (𝓝 (L n l)):= lean (carries (steak hf) he hs) l
   refine ⟨?_,{grows:=fun he v=>?_, turn:=fun m K hK=>?_}⟩; · convert! regular_fin (Z:=fun _:Unit=>s) (fun n=> const_sc ..) hf.price hu.price (fun _=>hs) (fun _=>hn) (fun _=>hf.token) (fun _=>hu.token) (fun _=>zero_le_one) using 1; simp
   swap; · refine tendsto_nhds_unique (hy _ _) ((hy _ v).congr fun i:ℕ=>?_); exact ((hx i).grows he v).symm
   let V := flagS K G; funext l; have hk : ∀ U ∈ Centre _, Tendsto (fun i:ℕ=> U (Q i m)) atTop (𝓝 (U (L m))) := ?_
   · exact tendsto_nhds_unique (hk (fun F=> V.beam F l) ( V.sense|>.reaches l)) ((hy m l).congr (fun i:ℕ=>Eq.symm (congr_fun ((hx i).turn _ _ hK) l)))
   intro Z hZ; refine Submodule.span_induction (p:=fun U _=> Tendsto (fun i:ℕ=> U (Q i m)) atTop (𝓝 (U (L m)))) ?_ (by simp) ?_ ?_ hZ; rintro U ⟨k,rfl⟩; exact hy m k
   · intro a b hx hy he hV; exact he.add hV
   intro a b hx he; exact Tendsto.const_smul he a
lemma oceansLine : Drift b (fun i=>ocean s (Z i) (X i)) (ocean s U F):= ⟨torn hs h.real hv.price, fun i=>torn hs (h.ticket i) (hv.go i), carries h hv hs⟩
omit hs in lemma arborial (hr: Drift b Y H)(ht: closedF U c)(ht':∀ i, closedF (Z i) c)(hp:reverseF U)(hp':∀ i, reverseF (Z i)):
    Drift b (fun i=> arbor (Z i) (X i) (Y i)) (arbor U F H):= by
    refine ⟨Form0.treed hv.price ht hp h.real hr.real,fun i=> Form0.treed (hv.go i) (ht' i) (hp' i) (h.ticket i) (hr.ticket i),?_⟩
    have he (i:ℕ): arbor (Z i) (X i) (Y i)-arbor U F H= arbor (Z i) (X i-F) H+ arbor (Z i) (X i) (Y i-H)+arbor (Z i-U) F H:= by
        have hi: arbor (Z i-U) F H=arbor (Z i) F H-arbor U F H:=by rw [sub_eq_add_neg,two_leg,← neg_one_smul ℂ U,down_leg,neg_one_smul, sub_eq_add_neg]
        rw [hi]; simp only [← schedule,map_sub,LinearMap.sub_apply]; abel
    simp_rw [he]; refine fall_add (fall_add ?_ ?_) ?_; · convert! for_tree h.grey (a:=fade) (h:=fun _=>H) (travel hr.real.price) (fun m a b=> railto (hv.haze m a b)) (fun _=>zero_le_one) using 1; simp
    · convert! for_tree h.level hr.grey (fun m a b=> railto (hv.haze m a b)) (fun _=>zero_le_one) using 1; simp
    convert! for_tree (f:=fun _=> F) (travel h.real.price) (h:=fun _=>H) (travel hr.real.price) (fun m a b=> railto (hv.ops m a b)) (fun i=>(being i).le) using 1; simp
end YM.MS.Plum
