import YM.MSbar.Domain.Centre

/-! An unbounded-plane test identity including on external collisions of **momenta**. Not to be
applied to graph kernels without transfer growth! (Internal power counting of divergent graphs
will not have this estimator.) `Total` as proof abstraction omits polarization; get that from
integer dimensions. Include all hidden/ev tensor colors.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops MeasureTheory Function Set Filter
open scoped Topology BigOperators Classical ContDiff
variable {C:Type} {E D:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {m n j : ℕ} {U:Set ℂ}
variable {W:Edition C} {d:Bit}{F G:Functionals C}
structure Total (U:Set ℂ)(j:ℕ)(F:Functionals C) : Prop where
    safe: Eligible U j (arena C) F
    quiet (z : ℂ) : z∈U → ∀m:ℕ, Quiet (F z m)

lemma Full.total (h: Full U j W d F): Total U j F:= ⟨h.licensed,h.quiet⟩
namespace Total
lemma add (h : Total U j F)(h': Total U j G): Total U j (F+G) := ⟨h.safe.add h'.safe, fun z hz n=> (h.quiet _ hz n).add (h'.quiet _ hz n)⟩
lemma scale (h:Total U j F)(c:ℂ): Total U j (c • F):= ⟨h.safe.scale c,fun z hz n=> (h.quiet _ hz n).scale c⟩
lemma zero : Total U j (0:Functionals C) := ⟨Eligible.zero, fun _ _ _=> Quiet.zero⟩
lemma neg (h:Total U j F): Total U j (-F) := by simpa only [neg_smul,one_smul] using h.scale (-1:ℂ)
lemma sub (h:Total U j F)(h':Total U j G): Total U j (F-G) := by rw [sub_eq_add_neg]; exact h.add h'.neg
lemma wager (h:Total U j F) (hu:IsOpen U)(x:Words C m): Bet U j (fun p:ℂ×ℝ=>F p.1 m x):=by
    by_cases he:channel x=0
    · exact h.safe.ev _ (fun _ : ℝ=>x) ⟨Plot.cte x, fun _=> he⟩
    exact Bet.zero.congr hu (fun z hz _=> Eq.symm (h.quiet z hz m x he))
lemma translates (h:Total U j F){V: Move m n}{z:ℂ}(hz:z∈U)(x:Words C m): F z n ((line C).move V x)=F z m x:=h.safe.natural _ hz V x

section univ
variable (h : Total univ j F) (h':Total univ j G)
lemma movement (h:m≤n): ∃ L : Move m n, True:=by induction h with | refl=>exact ⟨LinearIsometry.id,trivial⟩ | step h ih=>obtain ⟨L,-⟩:=ih; exact ⟨(up _).comp L,trivial⟩
abbrev Earn (j) (f:ℂ→ℂ):= Bet univ j (fun x:ℂ×ℝ=> f x.1)
lemma ticket {j} {f g:ℂ→ℂ}(hf:Earn j f)(hg:Earn j g)(he:∀ᶠ n:ℕ in atTop,f n=g n)(z): f z=g z:= Transfer.Market.price (hf.gains rfl) (hg.gains rfl) 0 (fun v => hf.cost.cr v 0 (mem_univ _)) (fun v=> hg.cost.cr v 0 (mem_univ _)) he z
include h h'
lemma identify (he:∀ i:ℕ,F i i= G i i): F=G:=by
    funext z i x; apply ticket (f:=fun z=>F z i x) (g:=fun z=>G z i x) (h.wager isOpen_univ x) (h'.wager isOpen_univ x) _ z
    filter_upwards [eventually_ge_atTop i] with n hn; obtain ⟨V,-⟩:=movement hn
    rw [←h.translates (V:=V) (mem_univ _) x, ← h'.translates (V:=V) (mem_univ _) x,he]
omit h'
lemma choose_hom (W:Edition C)(he:∀ i:ℕ,Homogeneous (lift (W.binary i)) d (F i i))(z:ℂ): Homogeneous (lift (W.binary m)) d (F z m):=by
    constructor
    · intro u a b v; let L:=u++a::b::v; let R:=u++b::a::v; let s:=sign (W.parity a.1.1) (W.parity b.1.1)
      change F z m L=s*_; refine ticket (f:=fun t=>F t m L) (g:=fun t=>s*F t m R) (h.wager isOpen_univ _) ((h.scale s).wager isOpen_univ _) ?_ z
      filter_upwards [eventually_ge_atTop m] with n hn; obtain ⟨V,-⟩:= movement hn; rw [← h.translates (V:=V) (mem_univ _) L,← h.translates (V:=V) (mem_univ _) R]; unfold line L R; dsimp; rw [List.map_append,List.map_append]; exact (he _).commute ..
    intro u hu; refine ticket (f:=fun t=> F t m u) (g:=fun _=>0) (h.wager isOpen_univ u) Bet.zero ?_ z
    filter_upwards [eventually_ge_atTop m] with n hn; obtain ⟨V,-⟩:=movement hn; rw [← h.translates (V:=V) (mem_univ _) u]; apply (he n).shape; unfold oddity line; dsimp; rw [List.map_map]; exact hu
-- no integer O simplification. linearity in hat angle of each vector slot required.
lemma choose_color (W:Edition C)(he:∀ i:ℕ, Polar W (F i i))(z:ℂ): Polar W (F z m):= by
    intro c p u v
    let k(t:ℂ)(y:Hat m):= F t m (u++((c,y),p)::v)
    have hT(n:ℕ)(hn:m≤n): Dim.One (W.vector c) (k n):=by
       obtain ⟨L,-⟩:=movement hn; let f(q):= F (↑n) n ((line C).move L u++ ((c,q),taxi L p):: (line C).move L v)
       rw [show k n=f ∘ L from ?_]; exact (he n c (taxi L p) ((line C).move L u) ((line C).move L v)).compose L.toLinearMap
       funext y; unfold k f; rw [← h.translates (V:=L) (mem_univ _) _]; unfold line; dsimp; rw [List.map_append]; rfl
    have hy(y):= h.wager isOpen_univ (u++((c,y),p)::v)
    change Dim.One _ (k z); unfold Dim.One; split_ifs with hv
    · have H(n:ℕ)(hn:m≤n):∃ g : Hat m →ₗ[ℝ] ℂ, k n=g:= by
         have h:=hT n hn; simp only [Dim.One,hv,↓reduceIte] at h;obtain ⟨g,hg⟩:= h; exact ⟨_,funext hg⟩
      refine ⟨{toFun:= k z,map_add':=fun a b=>?_, map_smul':=fun c x=>?_},fun x=> rfl⟩
      · apply ticket (f:=fun t=>k t (a+b)) (g:=fun t=>k t a+k t b) (hy (a+b)) ((hy a).add (hy b)) _ z; filter_upwards [eventually_ge_atTop m] with n hn; obtain ⟨g,hg⟩:=H n hn; rw [hg,map_add]
      refine ticket (f:=fun t=>k t (c•x)) (g:=fun t=>c • k t x) (hy _) ((hy x).const_scale (↑c:ℂ)) ?_ z; filter_upwards [eventually_ge_atTop m] with n hn; obtain ⟨g,hg⟩:=H n hn;rw [hg,map_smul]
    refine ⟨k z 0,fun t=> ticket (f:=fun s=>k s t) (g:=fun s=>k s 0) (hy _) (hy _) ?_ z⟩
    filter_upwards [eventually_ge_atTop m] with n hn; have H:=hT n hn; simp only [Dim.One,hv,↓reduceIte] at H; exact (H.choose_spec t).trans (H.choose_spec _).symm
end univ
end Total
end YM.MSbar.Domain
