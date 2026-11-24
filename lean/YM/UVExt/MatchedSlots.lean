import YM.UVExt.MixedRent
import YM.UVExt.RelayDetector

/-!
# Match every finite normalized single-slot difference, then use products

Bootstrap the weak detector one layer at a time by single SBPs at fixed period in fuse order.
Keep the equation witnesses until all the erasures. We work off projected coincidence in
extraction order; no passage through coincidences.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Slots
open Set Function MeasureTheory Filter Lattice Wilson RG Push Extraction Extraction.Lease RelayDifference
open Cells MergeProof Dash Bid
open scoped Topology NNReal InnerProductSpace BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {F P : Trial C} {n : ℕ} {S : Table C.book} {d : ℕ}
set_option quotPrecheck false
section Algebra
private lemma prod_env (N p n) (F : Fin n→Trial C) (u : Fin n→Site (C.side N p)) (H : ∀ i, Envelope (F i N p (u i))) :
    Envelope fun x=>∏ i,F i N p (u i) x := Envelope.prodC _ _ (fun i _=> H i)
private lemma product_split (i : Fin n) (f g z : Fin n→ℂ) (hi : g i=f i-z i) (hf : ∀ b≠i,g b=f b) (hz : ∀ b≠i,z b=f b) :
    ∏ b,g b = (∏ b,f b) - ∏ b,z b:= by
  rw [← Finset.mul_prod_erase _ g (Finset.mem_univ i),← Finset.mul_prod_erase _ f (Finset.mem_univ i),← Finset.mul_prod_erase _ z (Finset.mem_univ i)]
  rw [hi,sub_mul,show ∏ j∈Finset.univ.erase i,g j=_ from Finset.prod_congr rfl (fun j hj=> hf j (Finset.ne_of_mem_erase hj)),
    show (∏ j∈Finset.univ.erase i,z j)=_ from Finset.prod_congr rfl (fun j hj=> hz j (Finset.ne_of_mem_erase hj))]

private lemma probes_split (Z V F : Fin n→Trial C) (i : Fin n) (h0 : V i= F i-Z i) (hv : ∀ j≠i,V j=F j) (hz:∀ j≠i,Z j=F j)
    (hf:∀ i, Bid.sober C (F i) o) (ht:∀ i, Bid.sober C (Z i) o) :
    o.late fun N p=> ∀ x:Fin n→Site (C.side N p), probes N p n F x=probes N p n V x+probes N p n Z x:=by
  unfold Bid.sober Order.late at ht hf; filter_upwards [eventually_all.mpr hf,eventually_all.mpr ht] with p hh hb
  filter_upwards [eventually_all.mpr hh,eventually_all.mpr hb] with N hn hr u
  rw [←sub_eq_iff_eq_add]; symm
  let w(H:Fin n→Trial C) (U):=∏ i,H i (o.mesh N) (o.per p) (u i) U
  change moment (C.beta _ _) (w V)= moment _ _ - moment _ _; unfold moment
  calc
    _ = ∫ U,w F U - w Z U ∂Wilson.law G _ _ := congr_arg _ (funext fun U=>?iro)
    _ = _:= integral_sub ((prod_env _ _ _ _ _ (fun i=> ⟨(hn i _).1,(hn i _).2⟩)).integrableC _) ((prod_env _ _ _ _ _ (fun i=> ⟨(hr i _).1,(hr i _).2⟩)).integrableC _)
  case iro =>
    unfold w
    refine product_split i _ _ _ (by rw [h0]; rfl) (fun j hh => by simp only [hv j hh]) (fun j hh=>by simp only [hz j hh])

def isolated (o : Extraction.Order) (F : Trial C) := ∃ z, manifest z ∧ Stencilled o z ∧ TiledCaps C o (F-z)
lemma manifest_zero (C : Family G) : manifest (C:=C) 0 := ⟨0,0,fun _ _=> ⟨0,continuous_const,Mark.MicroAt.zero G 0 0,fun _ _=> rfl⟩⟩
lemma rolled (hC : C.Makes) (hB : CenterPort C o) (v : C.book.Token) : isolated o (visits C v.1 v.2) := by
  refine ⟨0,manifest_zero C,show Stencilled (C:=C) o 0 from ⟨∅, Eventually.of_forall fun i=> ⟨fun _ _=>rfl,fun x=>Cells.Interior.constant _ _⟩⟩,?_⟩
  rw [sub_zero]; exact from_tight hC hB ⟨‖v.2‖,Eventually.of_forall fun _=>Eventually.of_forall fun _=>le_rfl⟩

theorem erased_bounds (hC:C.Makes) (F: Fin n→Trial C) (hs:∀ i,Stencilled o (F i)) (hZ:∀ i,isolated o (F i)) {δ:ℝ} (hd:0<δ) :
    ∃ A:ℝ,0≤A ∧ o.late fun N p=> ∀ x, (∀ i j,i≠j→ δ ≤ C.S.a N * separation (x i) (x j)) → ‖probes N p n F x‖≤A :=by
  choose z hz hm he using hZ
  let V(s : Finset (Fin n)) (i) := if i∈s then F i-z i else F i
  have hs' (s i): Stencilled o (V s i) := by unfold V; split_ifs; exact (hs i).sub (hm i); exact hs i
  obtain ⟨A,hA,H⟩:= packing hC (V Finset.univ) (fun i=>by simpa only [V,Finset.mem_univ,↓reduceIte] using! And.intro (hs' Finset.univ i) (he i)) hd
  have hw (s) : o.late fun N p=> ∀ x:Fin _→Site (C.side N p), (∀ i j,i≠j→ δ ≤ C.S.a N * separation (x i) (x j)) →
      probes N p n F x=probes N p n (V s) x := by
    induction s using Finset.induction_on with
    | empty => exact Eventually.of_forall fun _=> Eventually.of_forall fun _=> by simp [V]
    | @insert i s hi ih=>
      let W j:=if i=j then z j else V s j
      have hv(j): Stencilled o (W j) := by unfold W; split_ifs; exact hm _; exact hs' ..
      have ht:= erase_manifest hC W hv i (by simp [W,hz i]) hd
      have hw:= probes_split W (V (insert i s)) (V s) i (by simp [W,V,hi]) (fun j hj=> by simp [V,hj]) (fun j hj=>by simp [W,Ne.symm hj]) (fun i=>(hs' _ i).sober) (fun j=>(hv j).sober)
      filter_upwards [ht,ih,hw] with p hh h h'; filter_upwards [hh,h,h'] with N hn hP H x hx
      rw [hP x hx,H,hn x (fun j hj=>hx j i hj),add_zero]
  exact ⟨A,hA,((hw Finset.univ).and H).mono fun j hj=>(hj.1.and hj.2).mono fun i hi x hx=>by rw [hi.1 x hx]; exact hi.2 x hx⟩
lemma erased_gain (hC:C.Makes) (hB : CenterPort C o) (hz : isolated o F) (hF : Stencilled o F) :
    gain F o (fun _ _=>1:ℕ→ℕ→ℝ) := by
  intro n q i δ hδ; choose A hA h using erased_bounds (o:=o) hC (update (fun i=> visits C (q i).1 (q i).2) i F) (fun j=>by by_cases h:j=i <;>simp [Function.update, *, Stencilled.visits hC]) (fun j=>by by_cases h:j=i <;>simp [Function.update, *,rolled hC hB]) hδ
  refine ⟨A,hA,h.mono fun j hj=>hj.mono fun N hi x hx=>?h⟩; rw [mul_one]; convert hi _ hx using 2
  unfold probes featuring; congr 1; funext; refine Finset.prod_congr rfl fun u _=>?_
  split
  next he=> subst u; rw [update_self]
  next he=> rw [update_of_ne he]; rfl
end Algebra
section Limits
open Work.D03 (jump pair_sum residue period_cost cells_lift physical uniform)
private lemma split_at (F : Trial C) (N p) (q) (i : Fin n) (r : Fin n → Site (C.side N p)) :
    featuring F q i N p r = moment (C.beta N p)
      (fun U => F N p (r i) U * ∏ j ∈ Finset.univ.erase i, C.seen (q j) (r j) U) := by
  unfold featuring; congr 1
  refine funext fun x=>by rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),if_pos rfl]; congr 1
                          exact Finset.prod_congr rfl fun j hj => if_neg (Finset.ne_of_mem_erase hj)
set_option maxHeartbeats 750000 in
lemma one_shift' {v : Shot C.book} {F:Trial C} (a : Axis) (hf : Stencilled o F) :
    o.late fun N p=>∀ r, featuring (next a F) v.left v.i N p r = (C.S.a N:ℂ)⁻¹ *
      (featuring F v.left v.i N p (r+jump v.i a)- featuring F v.left v.i N p r) := by
  filter_upwards [hf.sober] with p h; filter_upwards [h] with N hn r
  let g(U) := ∏ j ∈ Finset.univ.erase v.i, C.seen (v.left j) (r j) U
  have hh(i):Envelope (fun U=>F (o.mesh N) (o.per p) i U * g U):= Envelope.mulC ⟨(hn i).1,(hn i).2⟩ (RG.Envelope.compactC (continuous_finsetProd (Finset.univ.erase v.i) (fun j _=> C.continuousO ..)))
  simp_rw [split_at,moment]
  have hw : (fun U=>∏ j∈Finset.univ.erase v.i,C.seen (v.left j) ((r+(jump v.i a:Fin v.n→Site (C.side (o.mesh N) (o.per p)))) j) U)=g :=
    funext fun U=> Finset.prod_congr rfl (fun j hj=>by rw [Pi.add_apply,Work.D03.jump,Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj),add_zero])
  change (∫ x,_*g x ∂_) = (C.S.a (o.mesh N):ℂ)⁻¹ * ((∫ x, _*((fun U=>∏ j∈Finset.univ.erase v.i,C.seen (v.left j) ((r+(jump v.i a:Fin v.n→Site (C.side (o.mesh N) (o.per p)))) j) U) x) ∂_) - ∫ x,_*g x ∂_)
  rw [hw,← integral_sub ((hh _).integrableC _) ((hh _).integrableC _),← integral_const_mul]
  congr 1; funext x
  simp [Work.D03.jump,next]; ring

private lemma on_torus (v : Shot C.book) (a : Axis) (hf : Stencilled o F) : o.late fun N p=>
    targetB (next a F) v N p = (C.S.a N:ℂ)^(4*v.n) *
      ∑ r : Fin v.n → Site (C.side N p), ((C.S.a N:ℂ)⁻¹ *
          (v.f (Order.cells C N p (r-jump v.i a)) - v.f (Order.cells C N p r))) *
        featuring F v.left v.i N p r := by
  filter_upwards [one_shift' (v:=v) a hf] with p h; filter_upwards [h] with N hn
  simp_rw [targetB,hn]
  exact congr_arg (_ * ·) (pair_sum (fun r => v.f (Order.cells C (o.mesh N) (o.per p) r)) ..)
lemma height_error (h : gain F o (fun _ _=>1:ℕ→ℕ→ℝ)) (hf:Stencilled o F) (v : Dash.Shot C.book) (a:Axis) :
    Tendsto (fun j : ℕ × ℕ => targetB (next a F) v j.1 j.2 +
      (C.S.a j.1:ℂ)^(4*v.n)*(∑ r, (down v.f v.i a) (Order.cells C j.1 j.2 r)*featuring F v.left v.i j.1 j.2 r)) o.fuse (𝓝 0) := by
  obtain ⟨K,hK,hx,hc⟩ := exists_compact_between
    (v.f.hasCompactSupport.union (down v.f v.i a).hasCompactSupport) (conf_open _)
    (union_subset (show tsupport v.f ⊆ conf _ from v.f.tsupport_subset)
      (show tsupport (down v.f v.i a) ⊆ conf _ from (down v.f v.i a).tsupport_subset))
  have hK1 := subset_union_left.trans hx
  have hK2 := subset_union_right.trans (hx.trans interior_subset)
  obtain ⟨δ,hδ,h₁⟩ := v.f.hasCompactSupport.exists_thickening_subset_open isOpen_interior hK1
  let P := Points.direction v.i a
  have hs : ∀ᶠ N : ℕ in atTop, ∀ y ∈ tsupport v.f, y + C.S.a N • P ∈ K := by
    filter_upwards [C.S.shrinks.eventually (gt_mem_nhds hδ)] with N hN y hy
    apply interior_subset (h₁ (Metric.mem_thickening_iff.mpr ⟨y,hy,?_⟩))
    rw [dist_eq_norm,add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (C.S.a_pos _)]
    simpa [P, Points.direction] using hN
  obtain ⟨r,hr,hP⟩ := Gaps.someGrows C.S hK hc
  obtain ⟨D,hD,H⟩ := h v.n v.left v.i r hr
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  rw [Order.fused, Order.late]
  filter_upwards [on_torus v a hf, H,o.per.cofinal.eventually hP,o.per.cofinal.eventually (room C.S hK)] with k hsume hk hto hper
  let p := o.per k
  have hp : 0 < Extraction.length C.S p := by unfold Extraction.length; positivity
  let V := Extraction.length C.S p ^ (4*v.n)
  have hV : 0 < V := pow_pos hp _
  let e := ε / (V * (D+1))
  have hDen : 0 < V*(D+1) := mul_pos hV (by linarith)
  have he := uniform v.f v.i a C.S (show 0 < e from div_pos hε hDen)
  filter_upwards [hsume,hk, o.mesh.cofinal.eventually hs, o.mesh.cofinal.eventually he] with j hq hj ht he
  let N := o.mesh j
  let t := C.S.a N
  have Ht (r : Fin v.n → Site (C.side N p)) := physical C v.f v.i a
    (hK1.trans (interior_subset.trans hper)) (fun y hy => hper (ht y hy)) r
  let q := Order.cells C N p (n:=v.n)
  let M (r : Fin v.n → Site (C.side N p)) := residue v.f v.i a t (q r) * featuring F v.left v.i N p r
  have hr (r) : ‖M r‖ ≤ e*D := by
    by_cases hh : q r ∈ K
    · dsimp only [M]; rw [norm_mul]
      exact mul_le_mul (he _) (by
          have hQ := hj r (fun a b hb=> @Gaps.gridSeparation C.S v.n (o.per k) (o.mesh j) (lift ∘ r) r (funext fun a=> (wrap_lift (r a)).symm)
            _ (hto _ hh) b a hb.symm)
          exact hQ.trans_eq (mul_one D)) (norm_nonneg _) (div_nonneg hε.le hDen.le)
    have h1 : v.f (q r) = 0 := by_contra fun h => hh (interior_subset (hK1 (subset_closure h)))
    have h2 : down v.f v.i a (q r) = 0 := by_contra fun h => hh (hK2 (subset_closure h))
    have h3 : v.f (q r - t • P) = 0 := by
      by_contra h
      exact hh (sub_add_cancel (q r) (t • P) ▸ ht (q r-t • P) (subset_closure h))
    have h0 : M r = 0 := by dsimp only [M,residue]; rw [h1,h2,h3]; ring
    rw [h0,norm_zero]; exact mul_nonneg (div_nonneg hε.le hDen.le) hD
  have Hsum : targetB (next a F) v N p + (C.S.a N:ℂ)^(4*v.n) * (∑ r, (down v.f v.i a) (q r) * featuring F v.left v.i N p r) =
      (C.S.a N:ℂ)^(4*v.n) * ∑ r, M r := by
    rw [hq]; change (C.S.a N:ℂ)^(4*v.n)*_+(C.S.a N:ℂ)^(4*v.n)*_= _
    rw [←mul_add,← Finset.sum_add_distrib]; congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    dsimp only [M,residue,q,N,p]; rw [Ht r, ← add_mul]
  change dist (targetB _ v N p + _) 0 < ε
  rw [dist_zero_right, Hsum]
  apply (period_cost C.S M (e*D) hr).trans_lt
  change V * (e*D) < ε
  have hw : e * (V * (D + 1)) = ε := div_mul_cancel₀ ε hDen.ne'
  nlinarith [mul_pos (show 0 < e from div_pos hε hDen) hV]
end Limits

lemma match_and_erase {S : Table C.book} (R : Bin S) {d : ℕ} (h : Stencilled o F)
    (hC : C.Makes) (hB : CenterPort C o) (hO : o.Ordered C S) (hL : Live S) (hv : ∃ m : Shot C.book→ℂ, ∀ v,Tendsto (uncurry (targetB F v)) o.fuse (𝓝 (m v)))
    (he : vet C o d F) (hc : StrongBin C R o d) (hr : RelayBin C R o d) (hw : Bin.Good R hL d) : isolated o F := by
  obtain ⟨x,h_cost,hxz⟩:=he; obtain ⟨m,hm⟩:=hv
  let w n := (R d).step n (x n)
  have hM := bounded_fit hC hB hO hr hw h.sober hm x h_cost hxz
  let y n := x n - w n
  obtain ⟨z,hz,he,hoz⟩:=hc.mark y (fun n => by simp only [y,w,map_sub,(R d).projection,sub_self])
    (dollar_sub h_cost (Work.D01.answer C hC _ _ _ hM))
  have hf_ : upper C x - upper C w = upper C y := by
    funext N p o U; change C.O N p (x _) o U - C.O _ _ _ _ _ = C.O _ _ (y _) _ _
    exact (congr_fun (C.linearO N p _ o|>.map_sub _ _) _).symm
  have ht_ : (upper C y - z) - (upper C x - F) + upper C w = F - z:= by rw [← hf_]; abel
  exact ⟨z,hz,he, ht_ ▸ ((from_close hC hoz|>.sub hC (from_close hC hxz)).add hC (from_tight hC hB hM))⟩ -- add hC?

theorem slot_deployment {S : Table C.book} (R : Bin S) (hC : C.Makes) (hB : CenterPort C o) (hO : o.Ordered C S) (hL : Live S)
    (hc : ∀ d, StrongBin C R o d) (he : ∀ d, RelayBin C R o d) (hw : ∀ d,Bin.Good R hL d)
    (x : C.book.Token) (w : List Axis) : Stencilled o (slotField x w) ∧ isolated o (slotField x w) ∧
    ∃ m : Shot C.book→ℂ, ∀ q, Tendsto (uncurry (targetB (slotField x w) q)) o.fuse (𝓝 (m q)) := by
  induction w with
  | nil=> refine ⟨Stencilled.visits hC _,rolled hC hB x,_, fun q=> (Order.along (hO.reads q.n (q.record x.2) q.f)).congr
      (fun p=>?_)⟩
          unfold uncurry targetB Order.smears
          congr 1; refine Finset.sum_congr rfl (fun r _ => congr_arg _ ?_); unfold featuring moment
          rw [Family.num]; congr 1; funext; refine Finset.prod_congr rfl fun i _=>?_
          split
          next he=> subst i; rw [Shot.record,update_self]; rfl
          next he=> rw [Shot.record,update_of_ne he]
  | cons b w ih=>
      let F:= slotField (C:=C) x w
      obtain ⟨ht,hs,m,hm⟩:= ih
      have hK := stencilled_next ht b
      have hv(q) : Tendsto (uncurry (targetB (slotField x (b::w)) q)) o.fuse (𝓝 (-(m (pushT q b)))) := by
        specialize hm (pushT q b); have hY:=(height_error (erased_gain hC hB hs ht) ht q b).sub hm
        dsimp [pushT, Bid.targetB, Function.uncurry] at hY
        change Tendsto (fun z:ℕ×ℕ=>(↑(C.S.a z.1):ℂ)^(4*q.n)*∑ r,q.f (Extraction.Order.cells C z.1 z.2 r)*featuring (next b F) q.left q.i z.1 z.2 r) _ _
        simpa only [Function.uncurry, targetB, add_sub_cancel_right,zero_sub,slotField,F,pushT] using hY
      exact ⟨hK,match_and_erase R hK hC hB hO hL ⟨_,hv⟩ ((hc x.1).vets _ _) (hc _) (he _) (hw _),_,hv⟩
end YM.UVExt.Slots
