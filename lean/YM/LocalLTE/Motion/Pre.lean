import YM.LocalLTE.Motion.Path
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
-- Career lift. uniform Θ with Horites
variable (k':ℕ) (tag:ℕ→ℕ)
-- permits initial Loft post l_b. Needs W.l<chip.I ad.
local notation "P"=>X.p.profile I
local notation "L"=>D.L J
open Collection.Price LocalLTE.FrameBox Progress.DirectedRecipe Averaging
namespace Career
local notation "Ω"=> F.hearth H
local notation "d'"=> W.crew H m*radiusB x₀
local notation "Q₀"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "t₀"=> (F.school H W k' tag)
local notation "V₀"=> (F.porch H W k' tag)
local notation "κ₀"=> H.κ
local notation "T₁"=> (Trio.resize H.w.ℓ (Rain.lint R.target A m))
local notation "S"=> (A.B.a.S)
local notation "u"=> W.hop H m
local notation "κd"=> W.pay
variable (J' : Adorn H W) (hk:F.Accepts H k)(hF:∀ x∈s, Trail.Hired H W (Q x) tag)
variable (x:ℝ)(hx:x∈s)(j:ℕ)(hj:j≤p)
local notation "s'"=> (A.B.a.budget (m+1))
local notation "A!"=> (A.B.a.S.side (m+1) n)
-- Need Post for gears. Price after all L.Y wait.Stokes paths. Crew.Shape from Trail finite K tags. 
local notation "C"=> (R.target (J) (I))
local notation "d₁"=> (R.shape)
variable (hp : East.Peers (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) (Testing.query X.p X.K (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.walls (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (R.shape.o (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) (pie j+1) p (W.lease H m j) H.w.ℓ H.κ)
    -- R.walls edit. includes all old geometry.
variable (hX:∀ x∈s,Trail.Keeps H (F.hearth H x) tag p k')
set_option quotPrecheck false
local notation "T₀" => F.fruits H W k' tag
include hp hF hx hj hk hX hm J'
lemma sprint (v:ℝ)(he:0 < v)(i:ℕ): ∀ᶠ y in 𝓝[s] x,(B).supBounds ((t₀).reg i).site ((t₀).reg i).support (F.fruits H W k' tag x j i-F.fruits H W k' tag y j i) v:=by
    let c:= (A₀); change ∀ᶠ y in _, (B).supBounds ((Sum.elim (V₀).reg _ (Marlin.leanU c i):RegularAddress c).site) ((Sum.elim (V₀).reg (sea d') (Marlin.leanU c i):RegularAddress c).support) ((Sum.elim (Trail.histogram H W (F.hearth H x) tag k' j) (Song.choir (F.glance H x j))) (leanU c i)-(Sum.elim (Trail.histogram H W (F.hearth H y) tag k' j) (Song.choir (F.glance H y j))) (leanU c i)) v
    cases he':Marlin.leanU c i; next he' => exact Career.terrain H F W hm k' tag hk hF x hx _ hj hp hX v he _
    next e=>
       have hxE:0 < Song.Rim c:= by unfold Song.Rim; positivity
       have hs:0 < Rim c*turnFee B:=mul_pos hxE (turnFee_pos _); let v':= v/(Rim c*turnFee B)
       filter_upwards [F.sunR H W hm J' hk x hx _ hj (v:=v') (div_pos he hs) e.2,self_mem_nhdsWithin] with y hy hY
       let A:=F.glance H x j e.2; let D':=F.glance H y j e.2; let V':=(A ∘ Seat.view e.1); let Z:=D' ∘ Seat.view e.1
       have hv: (B).supBounds _ _ _ _:= CouplingShape.sup_scale (Rim c) (Song.transSup e.1 (VerifiedReset.reg_sub ((F.coating H W hm J' hk _ hj hx).1) ((F.coating H W hm J' hk _ hj hY).1)) hy); rw [abs_of_pos hxE,← mul_assoc,mul_comm (Rim c*turnFee B),div_mul_cancel₀ _ hs.ne'] at hv -- edit
       change (B).supBounds (sea d' e).site (sea d' e).support (Rim c • V' -Rim c • Z) v; rw [← smul_sub]; exact hv
-- Regularity uses hP doesn't depend ζ.Lift Budget.
local notation "t'"=> F.index H W k' tag k
omit hp hX hx
include hX hx
lemma plotted : ∃ v, Meadow.Budget B (t₀|>.reg) (F.fruits H W k' tag x j) v:=by
    have ht:= F.atEarn H W hm k' tag hk hF _ hx; obtain ⟨Vk,h,hV⟩:= ht.cheap
    have hp:= F.primordial H W hm k' tag J' hk hF _ hx j hj (hX _ hx)
    let f:= t' x; have hs := Urns.minus_cost (show Meadow.Budget (B) (t₀|>.reg) (F.index H W k' tag k x|>.logRead) ((u)*(betaF G x₀ (D.L J))^(Pastel.chip 0)) from ⟨Vk,hV,fun i=>⟨ht.smooth i,h i⟩⟩) hp; rw [sub_sub_cancel] at hs; exact ⟨_,hs⟩
-- finite shelf quietness.L<.
omit J' hx hk hF hm hj hX
lemma folioSpan : ∃ S₀:Finset ℕ,∀ i∉S₀,∀ x:ℝ,F.fruits H W k' tag x j i=0:=by
    let f:= East.locker (F.holds.base) (East.lectures (F.holds.base) p H.w.ℓ tag) k'; let N:=leanU (A₀); let g':=Finset.disjSum f (univ:Finset (Door (A₀))); refine ⟨g'.map N.symm.toEmbedding,fun i h x=>?_⟩
    have he:N i∉g' :=fun hx=>h (by simpa using Finset.mem_map_of_mem N.symm.toEmbedding hx)
    unfold fruits; rw [Function.comp_apply]; cases hk':N i
    next «b»=>
       rw [hk', Finset.inl_mem_disjSum] at he; change ¬ («b»∈f) at he
       let Y:= F.hearth H x; have ht : «b» ∉ East.locker Y (East.lectures Y p H.w.ℓ tag) k':= by rw [show East.locker Y (East.lectures Y p H.w.ℓ tag) k'=f from (F.tables H k' tag (p:=p) x|>.2.symm)]; exact he
       have hh:= mt (East.aisle .. |>.mpr) ht
       let d:=pennant Y «b»; change Song.Rim (A₀) • ((East.strand Y O tag p H.w.ℓ k' j (W.lease H m j) H.κ) d.2 ∘ d.1.view)=_
       unfold East.strand; cases hf:d.2
       next q=>
         have hk : ¬award Y tag p H.w.ℓ k' j q:=fun h=>hh (by change d.2∈_; rw [hf]; exact h.1)
         simp only [Sum.elim_inl,if_neg hk]; rw [show (0:Config G _→ℝ)∘ d.1.view=0 from rfl,smul_zero]
       dsimp only [Sum.elim]; rw [show (0:Config G _→ℝ)∘ d.1.view=0 from rfl,smul_zero]
    next z' => exact False.elim (he (by rw [hk',Finset.inr_mem_disjSum]; simp))
include hp hF hx hj hk hX hm J'
lemma gateU (ε:ℝ)(he:0<ε): ∀ᶠ y in 𝓝[s] x, Meadow.Budget B (t₀|>.reg) (F.fruits H W k' tag x j- F.fruits H W k' tag y j) ε :=by
   obtain ⟨q,hq⟩:= F.folioSpan H W k' tag j
   let Z:=t₀; let D(i:ℕ):=Real.exp (preExponent B*coverNumber (B).B (Z.reg i).support); let c₀:= 1+∑ i∈q,D i; have hs:0≤∑i∈q,D i:= Finset.sum_nonneg fun i _=> Real.exp_nonneg _; have ht:0 < c₀:= add_pos_of_pos_of_nonneg zero_lt_one hs
   let v:=ε/c₀; have hV:0<v:=div_pos he ht
   filter_upwards [(eventually_all_finset q).mpr fun i hi=>F.sprint H W hm k' tag J' hk hF x hx j hj hp hX v hV i,self_mem_nhdsWithin] with y hy hY; let f(i:ℕ):=if i∈q then v else 0
   obtain ⟨_,w,hr,hM⟩:=F.plotted H W hm k' tag J' hk hF x hx _ hj hX; obtain ⟨_,t,hu',hP⟩:= F.plotted H W hm k' tag J' hk hF y hY _ hj hX; refine ⟨f,fun i=>?_,fun i=>⟨VerifiedReset.reg_sub (hM _|>.1) (hP _|>.1),?_⟩⟩ -- edit
   · let g j:=f j*D j; apply budget_mono (f:=g) (?_) (fun i=> ?_) (fun i=>?_)
     · have hv:HasSum g (∑ i∈q,g i):= hasSum_sum_of_ne_finset_zero (f:=g) (s:=q) (fun i h=>by simp [g,f,h])
       have hx i:0≤g i:=mul_nonneg (by unfold f; split; exact hV.le; exact le_rfl) (Real.exp_nonneg _); refine ⟨hx,hv.summable,hv.tsum_eq.trans_le ?_⟩; rw [Finset.sum_congr rfl (g:=fun i=>v*D i) (fun i h=>by unfold g f; rw [if_pos h]),← Finset.mul_sum]; refine (mul_le_mul_of_nonneg_left (show ∑ i∈q,D i≤ c₀ from le_add_of_nonneg_left zero_le_one) hV.le).trans (div_mul_cancel₀ _ ht.ne'|>.le)
     · split; next=> exact mul_nonneg (by unfold f; split; exact hV.le; exact le_rfl) (Real.exp_nonneg _)
       exact le_rfl
     split; exact le_rfl; exact mul_nonneg (by unfold f; split; exact hV.le; exact le_rfl) (Real.exp_nonneg _)
   unfold f; split; next he=> exact hy i he
   next hz=> rw [Pi.sub_apply,hq i hz,hq i hz,sub_zero]; exact VerifiedReset.sup_le (VerifiedReset.sup_const 0) abs_zero.le
end Career
end YM.PhysicalNext.Repeat.Mallow
