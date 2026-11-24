import YM.MSbar.Domain.Histogram
/-! Centered dense moment condition, even when momentum shape has zero external generators. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops MeasureTheory Function Set Filter
open scoped Topology BigOperators Classical ContDiff
variable {C:Type} {E D:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup D][NormedSpace ℝ D][FiniteDimensional ℝ D] {m n j : ℕ} {U:Set ℂ}
lemma Plot.catalogue (n:ℕ)(a:Fin n → Token C m)(w:Fin n→ E→Mom m) (hw:∀ i,(w i).HasTemperateGrowth) : Plot E C m (fun x=> catalogue n a (fun i=>w i x)):=by
   induction n with
   | zero => simp_rw [Loops.catalogue,List.ofFn_zero]; exact Plot.empty
   | succ n ih =>
      simp_rw [Loops.catalogue,List.ofFn_succ]; exact Plot.cons _ _ _ (HasTemperateGrowth.const _) (hw 0) (ih _ _ fun i=>hw i.succ)
private lemma exposed (n:ℕ)(a:Fin n→Token C m): Plot (Fin n→Mom m) C m (catalogue n a) := Plot.catalogue n a (fun i (p:Fin n→ Mom m)=> p i) (fun i => (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>Mom m) i).hasTemperateGrowth)
lemma fares {F : Functionals C} (hf:Eligible U j (arena C) F) {z:ℂ} (hz:z∈U) : Arc (F z m):=by
   intro n a; cases n with
   | zero => simp_rw [catalogue,List.ofFn_zero]; exact continuousOn_const
   | succ n =>
     let f(p: (Fin (n+1)→Mom m)):=catalogue _ a p;let s (p):=channel (f p)
     let q(p)(i:Fin (n+1)):=if i=0 then p i - s p else p i;have ht := (exposed (n+1) a).sum; have hr: HasTemperateGrowth s := ht
     let L:(Fin (n+1) → Mom m)→L[ℝ] (Fin (n+1) → Mom m):= ContinuousLinearMap.id .. -- dummy
     have hn(i): HasTemperateGrowth (fun p=>q p i):=by
         have h:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _=>Mom m) i).hasTemperateGrowth; unfold q; split_ifs; exact h.sub hr; exact h
     have hW(p): s p=∑ i,p i:=by unfold s f Loops.catalogue channel; rw [List.map_ofFn,List.sum_ofFn]; rfl
     have hv:Bet U j (fun v:ℂ×(Fin (n+1)→Mom m)=> F v.1 m (f (q v.2))):=hf.ev _ _ ⟨Plot.catalogue (n+1) a _ hn,by
          intro x; change s (q _)=_; rw [hW,Fin.sum_univ_succ]; simp [q,hW x, Fin.sum_univ_succ]⟩
     refine (hv.cost.slice hz).1.continuous.continuousOn.congr fun v hh=>?_
     change F z m (f v)= F z m (f (q v)); rw [show q v=v from ?_]; funext i; change s v=0 at hh; simp [q,hh]

lemma Eligible.freeze {X:ℕ→Type}{S:Site X}{F:Record X} (hf:Eligible U j S F){z:ℂ} (hz:z∈U) : Eligible univ 0 S (fun _=>F z) := ⟨fun _ _=>hf.natural z hz,by introv H; exact Bet.static (((hf.ev _ _ H).cost).slice hz)⟩
variable {W:Edition C} {d:Bit}{F G:Functionals C}{L:Links C}
lemma Pilot.freeze (h:Pilot U j W d L){z:ℂ}(hz:z∈U): Pilot univ 0 W d (fun _=> L z):=
    ⟨fun a b => (h.cost a b).freeze hz,fun i j he _ _=> h.parity i j he z hz,fun a b _ _=> h.uniformL a b z hz,fun a b _ _=> h.uniformR a b z hz⟩
lemma Full.freeze (h:Full U j W d F){z:ℂ}(hz:z∈U): Full univ 0 W d (fun _=> F z):=
    ⟨h.licensed.freeze hz,fun _ _=> h.quiet z hz,fun _ _=> h.colors z hz,fun _ _=> h.span z hz⟩
end YM.MSbar.Domain
