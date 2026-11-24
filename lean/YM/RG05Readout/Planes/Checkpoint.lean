import YM.RG05Readout.Planes.Polish
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Planes
open Function Finset Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells Overlay
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure Copper Motion
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage Many Next.Rank.Station Ribbons
open Records Basket Halls Shadow Flatten
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}
    {b k l:ℕ}{Q:ℝ}(h:C.Makes){D: Address.Rail C}{B:ℕ→ℕ→ℝ}
set_option quotPrecheck false
open Pulse Extraction Extraction.Lease
open Push.RelayDifference
variable {D:Address.Rail C}

variable {f: Extraction.Order}

/-! A transcription at common origin: affordable → vetted literal against calibrated matrices, absorb a finite bank then same at ALL higher SBP orders on-demand. For low-weight planes repaint them further. -/
open Bay Chalice

/-!
# Cone receipts.Boolean Ward.
 Weighted REAL ancestry maps. Projection kernel not discarded here. This proves linear inverse attenuation for surviving low-engineering weights and propagation bound for the rest, not lower/separated aperture budget by assumption. Using m≫ as required from Husk.C. -/
local notation "Z!"=> C.path.levels
local notation "χ"=> Address.clear C
local notation "S"=> Palette C d
local notation "J"=> Mark C d
local notation "ξ"=> C.S.block
local notation "L"=> C.S.block i
local notation "p!"=> BudgetPoint
variable {e:ℕ}{s t α A E:ℝ}
local notation "ΠΩ"=> Address.clear C d e
local notation "T"=> LinearMap.id (R:=ℂ) (M:=S) - Address.clear C d e
local notation "Ω"=> amplify d C L
/-!
# Actual limiting dictionary including transitions on same extraction. E units threshold within. Holds in kernel identified by all Poem tests.This is same linear mapping in ANY extraction.H.Phase fields ported by common T.F. -/
open Function Filter MeasureTheory Extraction Next.Extract
open Petals Dash
variable {b₀:ℕ→ℕ} (Y:∀ d:ℕ,Cutoffs→ Emblems C d)
abbrev Edge (C:Family G)(d:ℕ):= (Palette C d→L[ℂ] Palette C d)
variable {T₀ S₀:YM.Table C.book}{L0:ℕ→YM.Table C.book}{W:DiffPlan T₀}{R:Dash.Bin S₀}(H:Next.Extract.Base C f S₀ L0 R T₀ W) {g:Extraction.Order}
variable {G':∀ d:ℕ,ℕ→Palette C d→ₗ[ℂ] C.label d}(hp:Chalice.Anchored D B h b₀ Y)(ht:Tune (dims:=b₀) H Y g G')
noncomputable def feeling (d m i:ℕ) (hk:m ≤ i)(u:Cutoffs): Edge C d × Edge C d:= let X:= finer (Y d u) hk
      ⟨X.toLinearMap.toContinuousLinearMap,X.symm.toLinearMap.toContinuousLinearMap⟩
local notation "X'"=>∀ d:ℕ,Emblems C d
local notation "F₀"=> feeling Y d
structure Tempo (b₀:ℕ→ℕ)(f:Extraction.Order)(Z:∀ d:ℕ,Emblems C d):Prop where
    til (d m:ℕ) : b₀ d ≤ m → Tendsto (feeling Y d m (m+1) m.le_succ) f.fuse (𝓝 ((Z d m).symm.toLinearMap.toContinuousLinearMap,(Z d m).toLinearMap.toContinuousLinearMap))
include hp h
lemma sustain (d m:ℕ)(he:b₀ d ≤ m) : ∃ A:ℝ,0≤ A∧ ∀ᶠ N in atTop,∀ p:ℕ, ‖feeling Y d m (m+1) m.le_succ (N,p)‖≤A:=by
    let a:= ld C.path.levels m; let D':ℝ:= ((C.S.block m).val:ℝ)^d; let b:=Fintype.card (Mark C d); have h_a:1 ≤ a:= lamp_nn _; have h_b: 1 ≤ D':= one_le_pow₀ (by exact_mod_cast (C.S.block m).property)
    refine ⟨max (a * b) (a*D'*b), (mul_nonneg (zero_le_one.trans h_a) (Nat.cast_nonneg b)).trans (le_max_left ..),?_⟩
    filter_upwards [eventually_gt_atTop m] with N hk p; have hx:=hp.paid (N,p) d (he.trans hk.le); obtain ⟨V,hS⟩:=hx; let X:=feeling Y d m (m+1) m.le_succ (N,p)
    rw [Prod.norm_def]; apply max_le_max
    · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (zero_le_one.trans h_a) (Nat.cast_nonneg b)); intro x
      change ‖finer _ _ x‖≤_; exact ((size_norm _).trans ((hS.inverse_cost he (Nat.le_succ m) hk x).trans (by rw [string_next (le_refl m), string_base,mul_one];exact (mul_le_mul_of_nonneg_left (Petals.size_paid x) (zero_le_one.trans h_a)).trans_eq (mul_assoc ..).symm)))
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)); intro x; let v:= Y d (N,p); have hh:(finer v m.le_succ).symm x=v m x:=by rw [finer_next (le_refl m),base_value]; rfl
    have hv: ‖v m x‖≤ _:= (size_norm _).trans ((hS.follows m he hk).strength x |>.2); change ‖(finer v _).symm x‖ ≤ _; rw [hh]; exact hv.trans ((mul_le_mul_of_nonneg_left ((size_tuned ..).trans (mul_le_mul_of_nonneg_left (Petals.size_paid x) (zero_le_one.trans h_b))) (zero_le_one.trans h_a)).trans_eq (by unfold D' a b;ring))
variable (g:Extraction.Order)
omit hp h
lemma realizeD {p:Edge C d × Edge C d}(he:Tendsto (feeling Y d m (m+1) m.le_succ) f.fuse (𝓝 p)) :∃ u:(Palette C d≃ₗ[ℂ]Palette C d), (u.symm.toLinearMap.toContinuousLinearMap,u.toLinearMap.toContinuousLinearMap)=p:=by
       let q:=p.fst; let p:=p.snd; have h1(x: Palette C d): q (p x)=x:=by
           apply tendsto_nhds_unique_of_eventuallyEq (Dash.arcing (W:=fun i=>(feeling Y d m (m+1) m.le_succ i).fst) (he.fst_nhds) (Dash.arcing (he.snd_nhds) (tendsto_const_nhds (x:=x)))) tendsto_const_nhds; exact Eventually.of_forall fun j=> (finer (Y d j) m.le_succ).apply_symm_apply x
       have h2(x:Palette C d):p (q x)=x:=tendsto_nhds_unique_of_eventuallyEq (Dash.arcing (he.snd_nhds) (Dash.arcing (he.fst_nhds) (tendsto_const_nhds (x:=x)))) tendsto_const_nhds (Eventually.of_forall fun j=> (finer (Y d j) m.le_succ).symm_apply_apply x)
       let u : Palette C d≃ₗ[ℂ]Palette C d:=LinearEquiv.ofLinear p.toLinearMap q.toLinearMap (LinearMap.ext (h2)) (LinearMap.ext (h1)); exact ⟨u,rfl⟩
include h hp
abbrev Crew (b:ℕ→ℕ):= (d:ℕ) × {m:ℕ//b d ≤ m}
abbrev shoes (C:Family G)(b:ℕ→ℕ)(i:Crew b):=Edge C i.fst × Edge C i.fst
abbrev Kiosk (i:Crew b₀) (n p:ℕ) : Edge C i.fst × Edge C i.fst:= feeling Y i.fst i.snd.val (i.snd.val+1) i.snd.val.le_succ (n,p)
-- seperate TC bounds
set_option maxHeartbeats 260000 in
lemma reservesE : Next.Extract.Reserve (f.refine g) (fun (_i:Crew b₀) _=>True) (X:=shoes C b₀) (Kiosk Y):=by
   choose A ha hA using fun i:Crew b₀=> sustain h Y hp i.fst i.snd.val i.snd.property
   exact Next.Extract.Reserve.of_norm (X:=shoes C b₀) (fun i=> Eventually.of_forall fun _=> trivial) (fun i p _=>⟨_,ha i,((f.refine g).mesh.cofinal.eventually (hA i)).mono fun n h=>h p⟩) (fun i=>⟨_, ha i, Eventually.of_forall (fun j=> ((f.refine g).mesh.cofinal.eventually (hA i)).mono fun n h=>h ((f.refine g).per j))⟩)
omit h hp
lemma tempo_keep (ℓ: Extraction.Order) (y:∀ i:Crew b₀, shoes C b₀ i)(h:∀ (d m:ℕ)(hm:b₀ d ≤ m),Tendsto (feeling Y d m (m+1) m.le_succ) ℓ.fuse (𝓝 (y (⟨d,m,hm⟩:(Crew b₀))))) :∃ Z:∀ d:ℕ,Emblems C d, Tempo Y b₀ ℓ Z:=by
    have hv(d m :ℕ)(he:b₀ d  ≤ m):∃ u:(Palette C d≃ₗ[ℂ]Palette C d),(u.symm.toLinearMap.toContinuousLinearMap,u.toLinearMap.toContinuousLinearMap)= y (⟨_,m,he⟩:Crew b₀):=by
       exact realizeD Y (h d m he)
    choose u hu using hv; let V(d m:ℕ):= if hm:b₀ d  ≤ m then u d m hm else LinearEquiv.refl ℂ _; refine ⟨V,⟨fun d m hm=>?_⟩⟩; unfold V; rw [dif_pos hm,hu]; exact h d m hm
lemma keeps_crew {g : Extraction.Order} {z : ∀ i:Crew b₀,ℕ → shoes C b₀ i} {y: ∀ i:Crew b₀, shoes C b₀ i}(hv:Keeps g (fun _ _=>True) (X:=shoes C b₀) (Kiosk Y) z y) (d m:ℕ)(hm:b₀ d ≤ m) : Tendsto (feeling Y d m (m+1) m.le_succ) g.fuse (𝓝 (y (⟨d,m,hm⟩:Crew b₀))):= by
    let X : Crew b₀:= ⟨d,m,hm⟩; exact Order.along («L»:= Kiosk Y X) (hv.limits X)
include h hp
lemma tempered : ∃ G: Extraction.Order, ∃ Z:∀ d:ℕ,Emblems C d, Tempo Y b₀ ((f.refine g).refine G) Z:=by
    have hz:=reservesE (f:=f) h Y hp g
    obtain ⟨g',z,y,hY⟩:=hz.gather; exact ⟨g',tempo_keep _ _ y (keeps_crew Y hY)⟩
-- any fixed-range maps compare in this Ξ grammar after representative limits
variable {q ℓ:Extraction.Order} {θ:∀ d:ℕ,Emblems C d}
omit h hp
end YM.RG05Readout.Planes
