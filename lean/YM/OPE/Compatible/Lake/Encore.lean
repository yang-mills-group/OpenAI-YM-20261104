import YM.OPE.Compatible.Lake.Silica
/-!
# Paths. At fixed basis over physical directions. Exact all-orders coupling scheme isn't necessary to use this (different criteria for proving this price). Still needs its Physical producer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof Next.Extract Dash Extra.Histories
open Next.Rank Next.Rank.Price Extraction
open ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {d k N D:ℕ}{G:Gauge}{C:Family G}{T:C.Makes}{E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)] {H:Extraction.Order}{W:Table C.book}
structure Escort (T:C.Makes) (H:Extraction.Order)(W:Table C.book)(d k D:ℕ):Prop where
    height : C.ref d ≤ k
    each φ : φ.NeBot→ φ ≤ H.fuse→∃ ψ:Filter (ℕ×ℕ),ψ.NeBot∧ ψ ≤ φ ∧ ∃ (Q:ℕ→ C.label d ≃L[ℂ] C.label d),Conic T ψ Q ∧
       ∃ E:Fin (d+1)→Type, ∃ _ :∀ i,NormedAddCommGroup (E i), ∃ _ :∀ i,NormedSpace ℂ (E i), ∃ P:ℕ→ W.Field d ≃L[ℂ] Dock E, Coach C W k D E Q P
lemma escorting {P:DiffPlan W}(h:P.Inclusions W)(A:Services C H W)(a:∀ d,∃ k D,Escort T H W d k D) : Lanes (F:=H) P:=by
   constructor
   · constructor; intro d x
     obtain ⟨k,D,hk,hD⟩:=a d; let R:ℝ:=((d+1:ℕ):ℝ)* OPE.Columns.juice C.path.levels k*(C.labels.level d).coeffSize x
     refine ⟨2*D+1,?_⟩; filter_upwards [(β_ascent (C:=C) A.simpleGate).eventually_gt_atTop R,eventually_ge_atTop k] with i hi he f hf hp
     obtain ⟨ψ,hψ,hq,Q,M,E,N,X,F,hh⟩:= hD f hf hp; letI:=N;letI:=X
     obtain ⟨y,hy,hv⟩:= hh.pennant M (hq.trans hp) hk x he
     have hL: chargeTerm d y (Q i)< β C i^(2*D+1):=by
          have hr: (β C i^D)^2 >0:=pow_pos (pow_pos (β_pos ..) _) _
          refine lt_of_le_of_lt hv (lt_of_lt_of_le (mul_lt_mul_of_pos_left hi hr) ?_)
          rw [pow_succ (β C i) (2*D), mul_comm 2 D,pow_mul]
     refine ⟨ψ,hψ,hq,y,hy,?_⟩
     filter_upwards [(tallyRange T M (hq.trans hp) (hk.trans he) _ y (tendsto_const_nhds (x:=y))).eventually (ge_mem_nhds hL)] with j hj; rw [paidTerm]; exact hj
   constructor; intro d e he u hu
   obtain ⟨k,D,hk,hD⟩:=a d; let v:= LinearMap.toContinuousLinearMap u; let t:= v.comp (LinearMap.toContinuousLinearMap (W.project d)); let b := 2*((d+1:ℕ):ℝ)*‖t‖ * outward C d k * C.S.a k^(d-e)
   refine ⟨2*D+1,?_⟩; filter_upwards [(β_ascent (C:=C) A.simpleGate).eventually_ge_atTop b,eventually_ge_atTop k] with i hi hl f hf hp w z q hc ha
   obtain ⟨ψ,hψ,hq,Q,M,E,N,X,F,hh⟩:=hD f hf hp; letI:=N; letI:=X
   have hx:= hh.ensign M (hq.trans hp) A hk h v hu he hl z
   have heq:= le_of_tendsto (tallyRange T M (hq.trans hp) (hk.trans hl) _ z (hc.mono_left hq)) (ha.filter_mono hq)
   refine hx.trans (mul_le_mul ?_ heq (Work.G08.size_nonneg _ _) (pow_nonneg (β_pos ..|>.le) _)); change b*(β C i^D)^2≤_; rw [pow_succ (β C i) (2*D), mul_comm 2 D,pow_mul,mul_comm (b:ℝ)]; exact mul_le_mul_of_nonneg_left hi (pow_nonneg (pow_nonneg (β_pos ..|>.le) _) _)
end YM.OPE.Lake
