import YM.Frontier6.Pair.FixedWord
import YM.MergeProof.West.Sally

/-! A continuum family avoids a fixed grid of exterior seams, even for literal point estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Platform
open Set Filter Function Lattice Extraction Spec Next.UVStress MergeProof.Ribbons
open scoped Topology BigOperators
variable {G:Gauge}{C:Family G}{b n : ℕ} (H:Schedule)
private lemma step_next (x:ℝ)(h:∀ z:ℤ,x+1/2 ≠ z) : ∃ z:ℤ, |x-z| < (1/2:ℝ):=by
    let t:= x+1/2; have hx : ↑⌊t⌋<t:= lt_of_le_of_ne (Int.floor_le _) (h _|>.symm)
    have hv:x+1/2<⌊t⌋+1:= Int.lt_floor_add_one _; refine ⟨⌊t⌋,abs_lt.mpr ?_⟩; dsimp only [t] at *; constructor <;> linarith
private lemma floating (x:Fin n→ℝ) : ∃ (a ε:ℝ)(v:Fin n→ℤ),0<ε∧∀ i:Fin n, |x i+a-v i| < 1/2-ε:=by
    let f(i:Fin n × ℤ):ℝ:= i.2-(x i.1+1/2)
    obtain ⟨p,hp⟩:=(nonempty_compl.mpr (mt (fun h:range f=univ=> h ▸ countable_range f) (fun hu=>not_countable_univ hu))) -- edit
    choose v hv using fun i:Fin n=> step_next (x i+p) (fun z hz=>hp (show p∈range f from ⟨(i,z), (show (z:ℝ)-(x i+1/2)=p by linarith only [hz])⟩))
    obtain ⟨ε,hε,hQ⟩:= ((show ∀ᶠ ε:ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin).and (eventually_all.mpr fun i=> (show ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < 1/2-|x i+p-v i| from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (sub_pos.mpr (hv i)))))).exists
    exact ⟨p,ε,v,hε,fun i=>by specialize hQ i; linarith⟩

private lemma floatWidth (n : ℕ) : ∃ ε:ℝ,0 < ε ∧ ∀ x:Fin n→ℝ, ∃ (a:ℝ) (v:Fin n→ℤ),∀ i, |x i+a-v i| < 1/2-ε:=by
    classical
    let X:= Fin n→ℝ; let K:Set X:= Set.pi univ (fun _=> Set.Icc (0:ℝ) 1); let W:= ↥K
    choose a ε v he hε using fun x:W=>floating (x.val)
    let U(x:W):Set X:= ⋂ i:Fin n,{y | |y i+a x-v x i| < 1/2-ε x}
    have hu(x:W):IsOpen (U x):= isOpen_iInter_of_finite (fun i=>isOpen_lt (by fun_prop) continuous_const)
    obtain ⟨k,hk⟩:=(isCompact_univ_pi (fun _ : Fin n=> isCompact_Icc)).elim_finite_subcover (s:=K) U hu (fun i hi=> mem_iUnion.mpr ⟨⟨i,hi⟩,mem_iInter.mpr (fun l=> hε ⟨i,hi⟩ l)⟩) -- implicit check
    obtain ⟨δ,hδ,hp⟩:=((show ∀ᶠ ε:ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin).and ((eventually_all_finset k).mpr fun i _=> (show ∀ᶠ d in 𝓝[>] (0:ℝ), d < ε i from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (he i))))).exists
    refine ⟨δ,hδ,fun x=>?_⟩
    let u i:= Int.fract (x i)
    obtain ⟨y,hy,hu⟩:= mem_iUnion₂.mp (hk (show u∈K from fun i _=> ⟨Int.fract_nonneg _,Int.fract_lt_one _|>.le⟩))
    refine ⟨a y,fun i=> v y i+⌊x i⌋,fun i=>?_⟩
    dsimp only; rw [Int.cast_add,show x i+a y- _ = u i+a y -v y i from (show x i+a y-((v y i:ℝ)+ ↑⌊x i⌋)=u i+a y-v y i by unfold u Int.fract; ring)]; exact (show _ < _ from mem_iInter.mp hu i).trans (sub_lt_sub_left (hp y hy) _)

lemma distinct_stops (x:Points n) (hx:slide H b x) {δ:ℝ} (h:0 ≤ δ) (p:E4)(u:Fin n→ Lattice.Cover) (hp:∀ i,atStop H b (u i) δ (x i+p)) : Injective u:=by
    intro i j he; by_contra hQ; obtain ⟨l,hl⟩:=above_coord _ _ (hx i j hQ)
    have hi:=hp i l; have hj:=hp j l; rw [he] at hi; change |x j l+p l-H.gridPoint b (u j) l| < _ at hj; change |x i l+p l-H.gridPoint b (u j) l| < _ at hi
    apply (not_le.mpr hl); change |x j l-x i l| ≤ _; obtain ⟨hl,hu⟩:= abs_lt.mp hj; obtain ⟨he,hh⟩:= abs_lt.mp hi; exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma fit_chart (n:ℕ) : ∃ d:ℕ, ∀ (b:ℕ)(x:Points n), ∃ (p:E4)(u:Fin n → Lattice.Cover), ∀ i,
    atStop H b (u i) (3*H.a (b+d)) (x i + p):=by
    obtain ⟨ε,hε,hf⟩:= floatWidth n
    obtain ⟨d,hd⟩:= exists_nat_gt (3/ε)
    have hd:3 ≤ ((d:ℝ)+1)*ε:=by have hx:3 < (d:ℝ)*ε:= (div_lt_iff₀ hε).mp hd; linarith only [hx,hε]
    refine ⟨d,fun b x=>?_⟩
    let r:= H.a b; have hr:0<r:=H.a_pos b; let c:= H.a (b+d); have hc:0 < c:= H.a_pos _
    choose a v hv using fun j:Axis=> hf (fun i=> x i j / r)
    refine ⟨WithLp.toLp 2 (fun i=>a i*r), fun i j=> v j i, fun i j=>?_⟩
    have he:=fur d b H
    change |x i j + a j * r - r*(v j i)|< r/2-3*c
    have hz : r*(x i j/r+a j-v j i)=x i j + a j*r - r*(v j i):=by field_simp
    rw [← hz,abs_mul,abs_of_pos hr]; have h := mul_lt_mul_of_pos_left (hv j i) hr
    change r*|x i j/r+a j-v j i|< r*_ at h
    change ((d:ℝ)+1)*c ≤ r at he; linarith only [mul_le_mul_of_nonneg_right he hε.le,mul_le_mul_of_nonneg_right hd hc.le,h]
lemma refiner (b:ℕ) (x:Points n):∃ᶠ y in 𝓝 x,y∈generic n∧∃ k ≥ b, ∃ (u:Fin n→ Lattice.Cover), y=Extraction.Order.grid C k u:=
   (meets_grid C x).mono fun t ⟨ht,l,u,h⟩=> ⟨ht,max b l,le_max_left ..,pushSite C.S (le_max_right ..) ∘ u,h.trans (PiLp.ext fun i=> (finer C.S (le_max_right ..) _).symm)⟩

variable {S:Table C.book}{f:Extraction.Order}(K:Spec.Final C f S)
open Org in
lemma state_budget (h:Grill C f)(v:Fin n→ C.book.Token) (d:ℕ)
   (hf:∀ (b:ℕ)(x:Points n), ∃ (p:E4)(u:Fin n → Lattice.Cover), ∀ i, atStop C.S b (u i) (3*C.S.a (b+d)) (x i+p)) :
    ∀ᶠ m:ℕ in atTop, ∀ s:StateIndex K, ∀ x:Points n, slide C.S m x → ‖(state K s).read x v‖ ≤ honor C.S v (m+d):=by
    filter_upwards [(tendsto_add_atTop_nat d).eventually (story_period v K h)] with m hm s x hx
    obtain ⟨p,u,hp⟩:= hf m x; have hu:= distinct_stops C.S x hx (mul_nonneg (by norm_num) (C.S.a_pos (m+d)).le) p u hp
    let z:= Points.across p x; let T:= state K s; have h:= hierarchy K s; have hX:x∈conf n:= slide_conf C.S _ hx; have hz:= Points.across_in p hX
    rw [← h.translations n _ hX p v]
    refine le_of_tendsto_of_frequently (x:=𝓝 z) ((show ContinuousAt (fun x=> T.read x v) z from (T.smooth_read h.smooth v).continuousOn.continuousAt ((conf_open _).mem_nhds hz)).norm) (((refiner (C:=C) m z).and_eventually (eventually_all.mpr fun i=> (show ∀ᶠ x in 𝓝 z,atStop C.S m (u i) (3*C.S.a (m+d)) (x i) from (show Continuous (fun x:Points n=> x i) by fun_prop).continuousAt.eventually ((atStop_open ..).mem_nhds (hp i))))).mono ?_)
    rintro y ⟨⟨hy,l,hl,v',rfl⟩,hp'⟩; exact hm m l v' u (Nat.le_add_right ..) hl hu hy hp' s
end YM.Frontier6.Platform
